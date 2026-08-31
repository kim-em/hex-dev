/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.Montgomery.Context
public import HexModArith.Ntt.Convolution

public section

/-!
# Fixed auxiliary NTT primes

The catalogue packages each modulus together with kernel-checked bounds,
primality, and a root of exact maximal power-of-two order. Requested plans
derive the appropriate smaller root and build twiddle tables only for the
requested length.
-/

namespace Hex

namespace ZMod64

namespace Ntt

/-- Integer coefficient addition with the same zero-extending shape as the
modular convolution reference. -/
@[expose] def intAddCoeffs : List Int → List Int → List Int
  | [], right => right
  | left, [] => left
  | x :: xs, y :: ys => (x + y) :: intAddCoeffs xs ys

/-- Ordinary low-to-high integer schoolbook convolution.  This is the
coefficient target reconstructed from auxiliary-prime transforms. -/
@[expose] def intLinearConvolution : List Int → List Int → List Int
  | [], _ => []
  | _ :: _, [] => []
  | value :: values, right@(_ :: _) =>
      intAddCoeffs (right.map fun coefficient => value * coefficient)
        (0 :: intLinearConvolution values right)

/-- Zero-pad an integer coefficient list to a requested capacity. -/
@[expose] def intPadTo (n : Nat) (coefficients : List Int) : List Int :=
  coefficients ++ List.replicate (n - coefficients.length) 0

@[simp] theorem length_intPadTo (n : Nat) (coefficients : List Int)
    (hfit : coefficients.length ≤ n) :
    (intPadTo n coefficients).length = n := by
  simp [intPadTo]
  omega

private theorem map_intCast_addCoeffs {p : Nat} [Bounds p]
    (left right : List Int) :
    addCoeffs (left.map fun (value : Int) => (value : ZMod64 p))
        (right.map fun (value : Int) => (value : ZMod64 p)) =
      (intAddCoeffs left right).map
        fun (value : Int) => (value : ZMod64 p) := by
  induction left generalizing right with
  | nil => simp [addCoeffs, intAddCoeffs]
  | cons value values ih =>
      cases right with
      | nil => simp [addCoeffs, intAddCoeffs]
      | cons coefficient coefficients =>
          simp [addCoeffs, intAddCoeffs, ih, Lean.Grind.Ring.intCast_add]

/-- Reducing an integer convolution modulo `p` coefficientwise gives the
modular convolution of the reduced inputs. -/
theorem linearConvolution_intCast {p : Nat} [Bounds p]
    (left right : List Int) :
    linearConvolution
        (left.map fun (value : Int) => (value : ZMod64 p))
        (right.map fun (value : Int) => (value : ZMod64 p)) =
      (intLinearConvolution left right).map
        fun (value : Int) => (value : ZMod64 p) := by
  induction left with
  | nil => simp [linearConvolution, intLinearConvolution]
  | cons value values ih =>
      cases right with
      | nil => simp [linearConvolution, intLinearConvolution]
      | cons coefficient coefficients =>
          simp only [List.map_cons]
          change addCoeffs
              (List.map
                (fun entry : ZMod64 p => (value : ZMod64 p) * entry)
                ((coefficient : ZMod64 p) ::
                  List.map (fun (entry : Int) => (entry : ZMod64 p)) coefficients))
              (0 :: linearConvolution
                (List.map (fun (entry : Int) => (entry : ZMod64 p)) values)
                ((coefficient : ZMod64 p) ::
                  List.map (fun (entry : Int) => (entry : ZMod64 p)) coefficients)) =
            List.map (fun (entry : Int) => (entry : ZMod64 p))
              (intAddCoeffs
                (List.map (fun entry => value * entry)
                  (coefficient :: coefficients))
                (0 :: intLinearConvolution values
                  (coefficient :: coefficients)))
          simp only [List.map_cons] at ih
          rw [show
            List.map
                (fun entry : ZMod64 p => (value : ZMod64 p) * entry)
                ((coefficient : ZMod64 p) ::
                  List.map (fun (entry : Int) => (entry : ZMod64 p)) coefficients) =
              List.map (fun (entry : Int) => (entry : ZMod64 p))
                (List.map (fun entry => value * entry)
                  (coefficient :: coefficients)) by
                    simp [List.map_map, ← Lean.Grind.Ring.intCast_mul]]
          rw [ih]
          rw [show (0 : ZMod64 p) = ((0 : Int) : ZMod64 p) from
            (Lean.Grind.Ring.intCast_zero).symm]
          rw [← List.map_cons]
          exact map_intCast_addCoeffs (p := p)
            (List.map (fun entry => value * entry)
              (coefficient :: coefficients))
            (0 :: intLinearConvolution values (coefficient :: coefficients))

private theorem padTo_intCast {p : Nat} [Bounds p]
    (n : Nat) (coefficients : List Int) :
    padTo n (coefficients.map fun (value : Int) => (value : ZMod64 p)) =
      (intPadTo n coefficients).map
        fun (value : Int) => (value : ZMod64 p) := by
  simp [padTo, intPadTo, List.map_append, Lean.Grind.Ring.intCast_zero]

end Ntt

/-- One fixed auxiliary prime and its maximal radix-two root. -/
structure NttPrime where
  /-- Prime modulus, always below `2^31`. -/
  modulus : Nat
  /-- Word-arithmetic bounds for the modulus. -/
  bounds : Bounds modulus
  /-- Kernel-checked primality evidence. -/
  prime : PrimeModulus modulus
  /-- Maximum supported transform exponent. -/
  maxLog : Nat
  /-- The maximal power-of-two length divides the unit-group order. -/
  length_dvd : 2 ^ maxLog ∣ modulus - 1
  /-- Primitive root of order `2^maxLog`. -/
  root : @ZMod64 modulus bounds
  /-- The stored root has exact maximal power-of-two order. -/
  root_order : @ExactOrder modulus bounds root (2 ^ maxLog)

namespace NttPrime

/-- Maximum supported transform length. -/
def maxLength (prime : NttPrime) : Nat :=
  2 ^ prime.maxLog

/-- Derive the root requested for a smaller transform length. The checked
builder below rejects lengths that do not divide the maximum. -/
def rootFor (prime : NttPrime) (n : Nat) : @ZMod64 prime.modulus prime.bounds :=
  letI : Bounds prime.modulus := prime.bounds
  prime.root ^ (2 ^ (prime.maxLog - n.log2))

/-- Build a reusable plan when `n` is a supported power-of-two length. A
capacity miss or failed validation is normal control flow. -/
def plan? (prime : NttPrime) (n : Nat) :
    Option (@NttPlan prime.modulus n prime.bounds prime.prime) :=
  letI : Bounds prime.modulus := prime.bounds
  letI : PrimeModulus prime.modulus := prime.prime
  if n ≤ prime.maxLength then
    NttPlan.build? (rootFor prime n)
  else
    none

/-- The root derived for an in-capacity power-of-two length has exact order
`n`. -/
theorem rootFor_order (prime : NttPrime) (n : Nat)
    (hpow : IsPowTwo n) (hcapacity : n ≤ prime.maxLength) :
    @ExactOrder prime.modulus prime.bounds (rootFor prime n) n := by
  letI : Bounds prime.modulus := prime.bounds
  obtain ⟨hne, heq⟩ := hpow
  have hk : n.log2 ≤ prime.maxLog := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ n.log2 = n := heq.symm
      _ ≤ prime.maxLength := hcapacity
      _ = 2 ^ prime.maxLog := rfl
  have hstride :
      2 ^ (prime.maxLog - n.log2) * n = prime.maxLength := by
    calc
      2 ^ (prime.maxLog - n.log2) * n =
          2 ^ (prime.maxLog - n.log2) * 2 ^ n.log2 :=
        congrArg (fun value => 2 ^ (prime.maxLog - n.log2) * value) heq
      _ = 2 ^ (prime.maxLog - n.log2 + n.log2) :=
        (Nat.pow_add _ _ _).symm
      _ = 2 ^ prime.maxLog := by rw [Nat.sub_add_cancel hk]
      _ = prime.maxLength := rfl
  unfold ExactOrder
  constructor
  · unfold rootFor
    rw [Ntt.pow_mul, hstride]
    exact prime.root_order.pow_eq_one
  · by_cases hn : n = 1
    · exact Or.inl hn
    · refine Or.inr ?_
      have hmaxHalf : prime.root ^ (prime.maxLength / 2) ≠ 1 := by
        rcases prime.root_order.half with hmaxOne | hnot
        · exfalso
          apply hn
          have hnpos : 0 < n := Nat.pos_of_ne_zero hne
          have hmax : prime.maxLength = 1 := by
            simpa [maxLength] using hmaxOne
          omega
        · simpa [maxLength] using hnot
      have hkpos : 0 < n.log2 := by
        apply Nat.pos_of_ne_zero
        intro hkzero
        apply hn
        rw [heq, hkzero]
      have htwoDvd : 2 ∣ n := by
        rw [heq]
        obtain ⟨k, hkEq⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hkpos)
        rw [hkEq, Nat.pow_succ]
        refine ⟨2 ^ k, ?_⟩
        omega
      have hhalfStride :
          2 ^ (prime.maxLog - n.log2) * (n / 2) =
            prime.maxLength / 2 := by
        rw [← Nat.mul_div_assoc _ htwoDvd, hstride]
      intro hsmall
      apply hmaxHalf
      unfold rootFor at hsmall
      rw [Ntt.pow_mul, hhalfStride] at hsmall
      exact hsmall

/-- Every supported transform length divides the catalogue modulus's unit
group order. -/
theorem length_dvd_of_supported (prime : NttPrime) (n : Nat)
    (hpow : IsPowTwo n) (hcapacity : n ≤ prime.maxLength) :
    n ∣ prime.modulus - 1 := by
  obtain ⟨_, heq⟩ := hpow
  have hk : n.log2 ≤ prime.maxLog := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ n.log2 = n := heq.symm
      _ ≤ prime.maxLength := hcapacity
      _ = 2 ^ prime.maxLog := rfl
  have hnmax : n ∣ prime.maxLength := by
    refine ⟨2 ^ (prime.maxLog - n.log2), ?_⟩
    calc
      prime.maxLength = 2 ^ prime.maxLog := rfl
      _ = 2 ^ (n.log2 + (prime.maxLog - n.log2)) := by
        rw [Nat.add_sub_of_le hk]
      _ = 2 ^ n.log2 * 2 ^ (prime.maxLog - n.log2) :=
        Nat.pow_add _ _ _
      _ = n * 2 ^ (prime.maxLog - n.log2) :=
        congrArg (fun value => value * 2 ^ (prime.maxLog - n.log2)) heq.symm
  exact Nat.dvd_trans hnmax prime.length_dvd

/-- Every in-capacity power-of-two request succeeds; the checked runtime
failure channel is reserved for invalid lengths and capacity misses. -/
theorem plan?_isSome_of_supported (prime : NttPrime) (n : Nat)
    (hpow : IsPowTwo n) (hcapacity : n ≤ prime.maxLength) :
    (plan? prime n).isSome = true := by
  letI : Bounds prime.modulus := prime.bounds
  letI : PrimeModulus prime.modulus := prime.prime
  unfold plan?
  rw [ite_eq_left hcapacity, NttPlan.build?_isSome]
  apply decide_eq_true
  exact ⟨hpow, prime.length_dvd_of_supported n hpow hcapacity,
    prime.rootFor_order n hpow hcapacity⟩

/-- A request beyond a catalogue entry's capacity returns `none`. -/
theorem plan?_eq_none_of_capacity (prime : NttPrime) (n : Nat)
    (hcapacity : ¬ n ≤ prime.maxLength) :
    plan? prime n = none := by
  unfold plan?
  rw [ite_eq_right hcapacity]

/-- Run ordinary convolution at one catalogue prime and erase the dependent
modular coefficient type to canonical integer residues. -/
def convolution? (prime : NttPrime) (n : Nat)
    (left right : Array Int) : Option (Array Int) :=
  letI : Bounds prime.modulus := prime.bounds
  letI : PrimeModulus prime.modulus := prime.prime
  match prime.plan? n with
  | none => none
  | some plan =>
      (Ntt.ordinary? plan
        (left.map fun (value : Int) =>
          (value : @ZMod64 prime.modulus prime.bounds))
        (right.map fun (value : Int) =>
          (value : @ZMod64 prime.modulus prime.bounds))).map
        fun coefficients => coefficients.map
          fun value => Int.ofNat value.toNat

/-- Canonicalizing an integer through one catalogue modulus preserves its
ordinary integer remainder. -/
theorem residue_emod (prime : NttPrime) (value : Int) :
    Int.ofNat
        (@ZMod64.toNat prime.modulus prime.bounds
          (@ZMod64.intCast prime.modulus prime.bounds value)) %
        (prime.modulus : Int) =
      value % (prime.modulus : Int) := by
  letI : Bounds prime.modulus := prime.bounds
  letI : PrimeModulus prime.modulus := prime.prime
  apply (Lean.Grind.IsCharP.intCast_ext_iff
    (α := @ZMod64 prime.modulus prime.bounds) prime.modulus).mp
  change @ZMod64.intCast prime.modulus prime.bounds
      (Int.ofNat (@ZMod64.toNat prime.modulus prime.bounds
        (@ZMod64.intCast prime.modulus prime.bounds value))) =
    @ZMod64.intCast prime.modulus prime.bounds value
  rw [ZMod64.intCast_ofNat, ZMod64.natCast_eq_ofNat,
    ZMod64.ofNat_toNat]

/-- A successful erased transform is the padded integer convolution reduced
coefficientwise to canonical representatives at this catalogue prime. -/
theorem convolution?_eq_of_some (prime : NttPrime) (n : Nat)
    (left right result : Array Int)
    (hresult : prime.convolution? n left right = some result) :
    result =
      (Ntt.intPadTo n
        (Ntt.intLinearConvolution left.toList right.toList)).toArray.map
        (fun value => Int.ofNat
          (@ZMod64.toNat prime.modulus prime.bounds
            (@ZMod64.intCast prime.modulus prime.bounds value))) := by
  letI : Bounds prime.modulus := prime.bounds
  letI : PrimeModulus prime.modulus := prime.prime
  unfold convolution? at hresult
  cases hplan : prime.plan? n with
  | none => simp [hplan] at hresult
  | some plan =>
      cases hordinary : Ntt.ordinary? plan
          (left.map fun (value : Int) =>
            (value : @ZMod64 prime.modulus prime.bounds))
          (right.map fun (value : Int) =>
            (value : @ZMod64 prime.modulus prime.bounds)) with
      | none => simp [hplan, hordinary] at hresult
      | some coefficients =>
          simp only [hplan, hordinary, Option.map_some,
            Option.some.injEq] at hresult
          subst result
          have href := Ntt.ordinary?_eq_of_some plan _ _ coefficients hordinary
          subst coefficients
          simp only [Array.toList_map]
          rw [Ntt.linearConvolution_intCast,
            Ntt.padTo_intCast]
          rw [← List.map_toArray, Array.map_map]
          rfl

end NttPrime

/-- Kernel-facing modular exponentiation can discharge concrete root-order
checks without unfolding the runtime `ZMod64.pow` extern. -/
private theorem ofNat_pow_eq_of_powModNat {p : Nat} [Bounds p]
    (base exponent expected : Nat) (hbase : base < p) (hexpected : expected < p)
    (hcheck : _root_.HexArith.powModNat base exponent p = expected) :
    (ofNat p base) ^ exponent = ofNat p expected := by
  rw [ZMod64.eq_iff_toNat_eq]
  change (ZMod64.pow (ofNat p base) exponent).toNat = (ofNat p expected).toNat
  rw [ZMod64.toNat_pow, ZMod64.toNat_ofNat,
    Nat.mod_eq_of_lt hbase, ZMod64.toNat_ofNat,
    Nat.mod_eq_of_lt hexpected,
    ← _root_.HexArith.powModNat_eq base exponent p (Bounds.pPos (p := p))]
  exact hcheck

/-- Two kernel-reduced modular-power checks certify exact maximal
power-of-two order. -/
private theorem exactOrder_of_powModChecks {p : Nat} [Bounds p]
    (root maxLog : Nat) (hroot : root < p) (hthree : 3 ≤ p)
    (hfull : _root_.HexArith.powModNat root (2 ^ maxLog) p = 1)
    (hhalf : _root_.HexArith.powModNat root (2 ^ maxLog / 2) p = p - 1) :
    ExactOrder (ofNat p root) (2 ^ maxLog) := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hthree
  have hp2 : 2 < p := Nat.lt_of_lt_of_le (by decide) hthree
  unfold ExactOrder
  constructor
  · exact ofNat_pow_eq_of_powModNat root (2 ^ maxLog) 1
      hroot hp1 hfull
  · right
    intro heq
    have hvalue := ofNat_pow_eq_of_powModNat (p := p)
      root (2 ^ maxLog / 2) (p - 1) hroot (by omega) hhalf
    have hequal :
        (ofNat p (p - 1)).toNat = (1 : ZMod64 p).toNat :=
      congrArg ZMod64.toNat (hvalue.symm.trans heq)
    change (ofNat p (p - 1)).toNat = (ZMod64.one : ZMod64 p).toNat at hequal
    have hone : (ZMod64.one : ZMod64 p).toNat = 1 := by
      rw [ZMod64.toNat_one]
      exact Nat.mod_eq_of_lt hp1
    rw [hone, ZMod64.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hequal
    omega

private def prime998244353 : NttPrime := by
  let bounds : Bounds 998244353 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 998244353 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 998244353
      bounds
      prime
      maxLog := 23
      length_dvd := by decide
      root := ofNat 998244353 15311432
      root_order := exactOrder_of_powModChecks 15311432 23
        (by decide) (by decide) (by decide) (by decide) }

private def prime167772161 : NttPrime := by
  let bounds : Bounds 167772161 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 167772161 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 167772161
      bounds
      prime
      maxLog := 25
      length_dvd := by decide
      root := ofNat 167772161 243
      root_order := exactOrder_of_powModChecks 243 25
        (by decide) (by decide) (by decide) (by decide) }

private def prime469762049 : NttPrime := by
  let bounds : Bounds 469762049 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 469762049 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 469762049
      bounds
      prime
      maxLog := 26
      length_dvd := by decide
      root := ofNat 469762049 2187
      root_order := exactOrder_of_powModChecks 2187 26
        (by decide) (by decide) (by decide) (by decide) }

private def prime754974721 : NttPrime := by
  let bounds : Bounds 754974721 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 754974721 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 754974721
      bounds
      prime
      maxLog := 24
      length_dvd := by decide
      root := ofNat 754974721 739831874
      root_order := exactOrder_of_powModChecks 739831874 24
        (by decide) (by decide) (by decide) (by decide) }

private def prime1004535809 : NttPrime := by
  let bounds : Bounds 1004535809 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 1004535809 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 1004535809
      bounds
      prime
      maxLog := 21
      length_dvd := by decide
      root := ofNat 1004535809 702606812
      root_order := exactOrder_of_powModChecks 702606812 21
        (by decide) (by decide) (by decide) (by decide) }

private def prime1224736769 : NttPrime := by
  let bounds : Bounds 1224736769 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 1224736769 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 1224736769
      bounds
      prime
      maxLog := 24
      length_dvd := by decide
      root := ofNat 1224736769 1098543633
      root_order := exactOrder_of_powModChecks 1098543633 24
        (by decide) (by decide) (by decide) (by decide) }

private def prime2013265921 : NttPrime := by
  let bounds : Bounds 2013265921 := ⟨by decide, by decide⟩
  let prime : PrimeModulus 2013265921 :=
    primeModulusOfPrime (by decide)
  letI := bounds
  exact
    { modulus := 2013265921
      bounds
      prime
      maxLog := 27
      length_dvd := by decide
      root := ofNat 2013265921 440564289
      root_order := exactOrder_of_powModChecks 440564289 27
        (by decide) (by decide) (by decide) (by decide) }

/-- The finite auxiliary-prime catalogue, ordered by modulus. -/
def nttPrimes : List NttPrime :=
  [ prime167772161
  , prime469762049
  , prime754974721
  , prime998244353
  , prime1004535809
  , prime1224736769
  , prime2013265921
  ]

end ZMod64

end Hex
