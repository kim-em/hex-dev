/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Packed

public section

/-!
Packed lazy-reduction convolution for `FpPoly` and its value-correspondence with
the reference `*`.

`FpPoly p = DensePoly (ZMod64 p)` multiplies by the generic schoolbook
convolution, which reduces mod `p` after *every* product term. Under the
`p < 2^31` bound each product is below `2^62`, so a whole output coefficient's
worth of products can be summed in a `__uint128_t` and reduced *once*. The
`lean_hex_fp_convolve` extern does exactly that on the backing-word arrays, in a
single native C call (no per-term FFI boundary or boxed-`ZMod64` traffic).
`mulPacked_eq` proves it equals the reference `*`, so a `@[csimp]`/kernel swap is
value-identical.

**Status: dormant infrastructure.** Microbenchmarks put `mulPacked` at ~7x the
reference `*` on a raw large-by-large `FpPoly` multiply, but wiring it into the
hot paths (via `Quotient.mul`) was measured to give **no** improvement — neither
on the `hexpolyfp_bench` Frobenius/exponentiation targets nor on end-to-end
Berlekamp-Zassenhaus factorization (a full A/B factor sweep was flat, ~1.00x).
The finite-field polynomial workloads are **reduction-bound** (`modByMonic`, the
boxed per-term long division), not multiply-bound, so a faster multiply is
invisible in the total. The actual lever is a packed *reduction* kernel of the
`HexPolyFp/Packed.lean` `modByMonicPacked` shape; see the follow-up issue. This
module is kept as a correct, proven, tested building block for a future workload
that *is* raw-multiply-bound (or a packed-`modByMonic` rewrite that reuses the
`__uint128_t` accumulation idea). It is intentionally **not** wired into `*`.
-/

namespace Hex

/-- Fold homomorphism: a `ZMod64` conditional-add fold and the matching `Nat`
conditional-add fold agree modulo `p` on their `toNat` values. This is what lets
a lazily-accumulated (reduce-once) sum equal the per-term-reduced `ZMod64` sum. -/
theorem foldl_add_toNat_mod {p : Nat} [ZMod64.Bounds p]
    (L : List Nat) (P : Nat → Prop) [DecidablePred P]
    (f : Nat → ZMod64 p) (g : Nat → Nat) (hfg : ∀ i, (f i).toNat = g i % p)
    (init : ZMod64 p) (initN : Nat) (hinit : init.toNat = initN % p) :
    (L.foldl (fun c i => if P i then c + f i else c) init).toNat =
      (L.foldl (fun c i => if P i then c + g i else c) initN) % p := by
  induction L generalizing init initN with
  | nil => simpa using hinit
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hP : P x
      · rw [if_pos hP, if_pos hP]
        refine ih (init + f x) (initN + g x) ?_
        have h1 : (init + f x).toNat = (init.toNat + (f x).toNat) % p :=
          ZMod64.toNat_add init (f x)
        rw [h1, hinit, hfg, ← Nat.add_mod]
      · rw [if_neg hP, if_neg hP]
        exact ih init initN hinit

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- The zero residue's backing word reads as `0` (through the `OfNat` literal). -/
@[local simp] private theorem val_toNat_ofNat_zero : ((0 : ZMod64 p).val).toNat = 0 :=
  ZMod64.toNat_zero

/-- One output coefficient of the lazy convolution: sum (in `Nat`, no per-term
reduction) all products contributing to degree `k`, then reduce once mod `m`.
This is the trusted spec the `lean_hex_fp_convolve` extern must match. -/
private def convolveCoeff (a b : Array UInt64) (m : UInt64) (k : Nat) : UInt64 :=
  UInt64.ofNat
    (((List.range a.size).foldl
        (fun c i =>
          if i ≤ k ∧ k - i < b.size then c + (a.getD i 0).toNat * (b.getD (k - i) 0).toNat else c)
        0) % m.toNat)

/-- Lazy-reduction schoolbook convolution over `F_m` on backing words. The
runtime path is the `lean_hex_fp_convolve` extern (native `__uint128_t`
accumulation, one reduction per output coefficient); this Lean body is the
matching semantic contract.

`private`, and only reached through the type-safe `mulPacked`: the C extern's
`__uint128_t` accumulation and `% modulus` match this `Nat`-summing fallback only
under the precondition the callers establish — words reduced below `m` and
`0 < m < 2^31` (so products stay below `2^62` and the accumulator never
truncates). This mirrors `lean_hex_zmod64_mul`, whose contract likewise assumes
reduced small residues. -/
@[extern "lean_hex_fp_convolve"]
private def fpConvolve (a b : Array UInt64) (m : UInt64) : Array UInt64 :=
  if a.size = 0 ∨ b.size = 0 then #[]
  else (Array.range (a.size + b.size - 1)).map (convolveCoeff a b m)

/-- Packed lazy-reduction multiply: pack both operands to backing words,
convolve natively, reduce once per output coefficient, unpack. The `FpPoly`
coefficients are reduced residues below `p < 2^31`, so the internal
`fpConvolve` extern is always called within its contract. -/
def mulPacked (a b : FpPoly p) : FpPoly p :=
  DensePoly.ofCoeffs (ofWords p (fpConvolve (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p)))

/-- Reading `ofWords` with default `0` unpacks the word read with default `0`. -/
theorem ofWords_getD (W : Array UInt64) (k : Nat) :
    (ofWords p W).getD k (Zero.zero : ZMod64 p) = ZMod64.ofNat p ((W.getD k 0).toNat) := by
  apply ZMod64.ext_toNat
  simp only [ofWords, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases W[k]? <;> simp

/-- The modulus word `UInt64.ofNat p` reads back as `p`. -/
private theorem toNat_ofNat_p : (UInt64.ofNat p).toNat = p := by
  have hword : p < UInt64.word := ZMod64.Bounds.pLtWord p
  simpa [UInt64.toNat_ofNat, UInt64.size, UInt64.word] using Nat.mod_eq_of_lt hword

/-- The word at packed index `i` reads back as the residue coefficient's `toNat`. -/
private theorem toWords_getD_toNat (a : FpPoly p) (i : Nat) :
    ((toWords a.toArray).getD i 0).toNat = (a.coeff i).toNat := by
  rw [toWords_getD]
  rfl

/-- The `Nat` single-fold on packed words equals the one on residue `toNat`s. -/
private theorem convolveFold_eq (a b : FpPoly p) (k : Nat) :
    (List.range (toWords a.toArray).size).foldl
        (fun c i =>
          if i ≤ k ∧ k - i < (toWords b.toArray).size
          then c + ((toWords a.toArray).getD i 0).toNat * ((toWords b.toArray).getD (k - i) 0).toNat
          else c) 0 =
      (List.range a.size).foldl
        (fun c i =>
          if i ≤ k ∧ k - i < b.size then c + (a.coeff i).toNat * (b.coeff (k - i)).toNat else c) 0 := by
  simp only [toWords_size, DensePoly.toArray_size, toWords_getD_toNat]

/-- The reference single-fold coefficient, as `ofNat` of its `Nat` sum. -/
private theorem refFold_eq_ofNat (a b : FpPoly p) (k : Nat) :
    (List.range a.size).foldl
      (fun c i => if i ≤ k ∧ k - i < b.size then c + a.coeff i * b.coeff (k - i) else c)
      (Zero.zero : ZMod64 p) =
    ZMod64.ofNat p ((List.range a.size).foldl
      (fun c i => if i ≤ k ∧ k - i < b.size then c + (a.coeff i).toNat * (b.coeff (k - i)).toNat else c) 0) := by
  apply ZMod64.ext_toNat
  rw [ZMod64.toNat_ofNat]
  exact foldl_add_toNat_mod (List.range a.size) (fun i => i ≤ k ∧ k - i < b.size)
    (fun i => a.coeff i * b.coeff (k - i))
    (fun i => (a.coeff i).toNat * (b.coeff (k - i)).toNat)
    (fun i => ZMod64.toNat_mul (a.coeff i) (b.coeff (k - i))) Zero.zero 0 (by simp)

/-- A conditional-add fold whose condition is false on every list element leaves
the accumulator untouched. -/
private theorem foldl_if_false {α β : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (F : β → α → β) (init : β) (h : ∀ i ∈ l, ¬ P i) :
    l.foldl (fun c i => if P i then F c i else c) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, if_neg (h x (List.mem_cons_self)), ih init
        (fun i hi => h i (List.mem_cons_of_mem x hi))]

/-- The word-level per-coefficient `Nat` sum, over packed words. -/
private def natFoldW (a b : FpPoly p) (k : Nat) : Nat :=
  (List.range (toWords a.toArray).size).foldl
    (fun c i =>
      if i ≤ k ∧ k - i < (toWords b.toArray).size
      then c + ((toWords a.toArray).getD i 0).toNat * ((toWords b.toArray).getD (k - i) 0).toNat
      else c) 0

/-- The word sum is faithful once reduced: it and `convolveCoeff` agree mod `p`. -/
private theorem convGetD_mod (a b : FpPoly p) (k : Nat) :
    ((fpConvolve (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p)).getD k 0).toNat % p =
      natFoldW a b k % p := by
  have hp : (UInt64.ofNat p).toNat = p := toNat_ofNat_p
  have hp0 : 0 < p := ZMod64.Bounds.pPos (p := p)
  have hpsize : p < UInt64.word := ZMod64.Bounds.pLtWord p
  by_cases hab : (toWords a.toArray).size = 0 ∨ (toWords b.toArray).size = 0
  · have hconv : fpConvolve (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p) = #[] := by
      unfold fpConvolve; rw [if_pos hab]
    have hzero : natFoldW a b k = 0 := by
      unfold natFoldW
      rcases hab with hA | hB
      · rw [hA]; simp
      · exact foldl_if_false _ _ _ _ (fun i _ => by rw [hB]; omega)
    rw [hconv, hzero]
    simp
  · rw [not_or] at hab
    obtain ⟨hA, hB⟩ := hab
    by_cases hk : k < (toWords a.toArray).size + (toWords b.toArray).size - 1
    · have hconv : (fpConvolve (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p)).getD k 0 =
          convolveCoeff (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p) k := by
        unfold fpConvolve
        rw [if_neg (not_or.mpr ⟨hA, hB⟩)]
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
        have hk' : k < (toWords a.toArray).size + (toWords b.toArray).size - 1 := hk
        simp only [toWords_size, DensePoly.toArray_size] at hk' ⊢
        rw [if_pos hk']
        rfl
      rw [hconv]
      unfold convolveCoeff natFoldW
      rw [hp, UInt64.toNat_ofNat_mod_word,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp0) (Nat.le_of_lt hpsize)), Nat.mod_mod]
    · have hget : (fpConvolve (toWords a.toArray) (toWords b.toArray) (UInt64.ofNat p)).getD k 0 = 0 := by
        unfold fpConvolve
        rw [if_neg (not_or.mpr ⟨hA, hB⟩)]
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
        rw [if_neg (by omega)]
        rfl
      have hzero : natFoldW a b k = 0 :=
        foldl_if_false _ _ _ _ (fun i hi => by
          have := List.mem_range.mp hi; omega)
      rw [hget, hzero]; simp

/-- The packed lazy multiply computes the same polynomial as the reference `*`. -/
theorem mulPacked_eq (a b : FpPoly p) : mulPacked a b = a * b := by
  apply DensePoly.ext_coeff
  intro k
  rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum_eq_singleFold, refFold_eq_ofNat]
  unfold mulPacked
  rw [DensePoly.coeff_ofCoeffs, ofWords_getD, ZMod64.ofNat_eq_ofNat_iff_mod_eq,
    ← convolveFold_eq a b k]
  exact convGetD_mod a b k

end FpPoly
end Hex
