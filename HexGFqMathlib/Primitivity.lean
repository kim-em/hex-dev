/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield
public import HexConway.Primitivity
public import Mathlib.GroupTheory.OrderOfElement

public section

/-!
The multiplicative order of the Conway generator.

`HexConway.Primitivity` checks, for each committed entry, that the residue of
`x` satisfies `α ^ N = 1` and `α ^ (N / q) ≠ 1` for every prime `q` of
`N = p ^ n - 1`. Those are the hypotheses of Mathlib's
`orderOf_eq_of_pow_and_pow_div_prime`. The transport is the work, because the
check runs on `FpPoly` representatives with structural powers, while `orderOf`
is about Mathlib's `^` in the field.

`orderOf_gen_of_primitive` supplies that transport. The bridge is
{name}`HexGFqMathlib.ofPolyHom`, which is a ring homomorphism, so it carries
the executable powers to Mathlib powers by `map_mul` and `map_pow`; reduced
representatives reflect equality with one, and the validated factorization
makes the supplied prime list exhaustive. The final section specializes the
result to all thirty-seven committed entries with `p ^ n > 2`.
-/

namespace HexGFqMathlib

open Hex

variable {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
variable {f : Hex.FpPoly p} {hf : 0 < Hex.FpPoly.degree f}
variable {hp : Hex.Nat.Prime p} {hirr : Hex.FpPoly.Irreducible f}

/-- Reduction modulo the modulus is invisible after passing to the field. -/
theorem ofPolyHom_reduceMod (y : Hex.FpPoly p) :
    ofPolyHom f hf hp hirr (Hex.GFqRing.reduceMod f y) =
      ofPolyHom f hf hp hirr y := by
  apply Hex.GFqField.ext
  apply Hex.GFqRing.ext
  show Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr _) =
    Hex.GFqField.repr (Hex.GFqField.ofPoly f hf hp hirr y)
  rw [Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_ofPoly,
    Hex.GFqRing.reduceMod_idem]

/-- The `modByMonic` spelling of {name}`HexGFqMathlib.ofPolyHom_reduceMod`. -/
theorem ofPolyHom_modByMonic (hm : Hex.DensePoly.Monic f) (y : Hex.FpPoly p) :
    ofPolyHom f hf hp hirr (Hex.FpPoly.modByMonic f y hm) =
      ofPolyHom f hf hp hirr y := by
  rw [show Hex.FpPoly.modByMonic f y hm = Hex.GFqRing.reduceMod f y from by
    rw [Hex.FpPoly.modByMonic, Hex.DensePoly.modByMonic_eq_mod]
    rfl]
  exact ofPolyHom_reduceMod y

/-- The executable structural power carries to a Mathlib power.

This is clean now only because `HexGFqMathlib.field` pins `npow` to the
executable power: with Mathlib's `npowRec` default the two would not be
definitionally equal and `pow_zero`/`pow_succ` would not apply to the `^` that
elaboration picks here. -/
theorem ofPolyHom_linPowMod (hm : Hex.DensePoly.Monic f) (x : Hex.FpPoly p) :
    ∀ k, ofPolyHom f hf hp hirr (Hex.Conway.linPowMod f hm x k) =
      (ofPolyHom f hf hp hirr x) ^ k
  | 0 => by
      show ofPolyHom f hf hp hirr 1 = _
      rw [map_one, pow_zero]
  | k + 1 => by
      show ofPolyHom f hf hp hirr
          (Hex.FpPoly.modByMonic f (Hex.Conway.linPowMod f hm x k * x) hm) = _
      rw [ofPolyHom_modByMonic, map_mul, ofPolyHom_linPowMod hm x k, pow_succ]

/-- The executable Horner power carries too, with the accumulator contributing
its own `q ^ length` factor. -/
theorem ofPolyHom_digitPowMod (hm : Hex.DensePoly.Monic f) (q : Nat)
    (x : Hex.FpPoly p) :
    ∀ (ds : List Nat) (acc : Hex.FpPoly p),
      ofPolyHom f hf hp hirr (Hex.Conway.digitPowMod f hm q x acc ds) =
        (ofPolyHom f hf hp hirr acc) ^ (q ^ ds.length) *
          (ofPolyHom f hf hp hirr x) ^ (Hex.Conway.digitsValue q ds)
  | [], acc => by
      show ofPolyHom f hf hp hirr acc = _
      rw [List.length_nil, pow_zero, pow_one, Hex.Conway.digitsValue, pow_zero,
        mul_one]
  | d :: ds, acc => by
      show ofPolyHom f hf hp hirr
          (Hex.Conway.digitPowMod f hm q x
            (Hex.FpPoly.modByMonic f
              (Hex.Conway.linPowMod f hm acc q * Hex.Conway.linPowMod f hm x d) hm)
            ds) = _
      rw [ofPolyHom_digitPowMod hm q x ds, ofPolyHom_modByMonic, map_mul,
        ofPolyHom_linPowMod, ofPolyHom_linPowMod, mul_pow, ← pow_mul, ← pow_mul,
        Hex.Conway.digitsValue, List.length_cons, pow_succ, mul_assoc,
        ← pow_add]
      ring_nf

/-- With the accumulator at `1`, the Horner power is exactly the power at the
digit list's value. -/
theorem ofPolyHom_digitPowMod_one (hm : Hex.DensePoly.Monic f) (q : Nat)
    (x : Hex.FpPoly p) (ds : List Nat) :
    ofPolyHom f hf hp hirr (Hex.Conway.digitPowMod f hm q x 1 ds) =
      (ofPolyHom f hf hp hirr x) ^ (Hex.Conway.digitsValue q ds) := by
  rw [ofPolyHom_digitPowMod, map_one, one_pow, one_mul]

/-! # From the executable check to `orderOf`

Two more ingredients. Reduction is not injective in general, so a `≠ 1` on
representatives does not by itself give a `≠ 1` in the field — but on *reduced*
representatives it does, and the Horner power always returns one. And the
supplied prime list has to be shown exhaustive, which is where the validated
product does its work.
-/

/-- On reduced representatives, being one in the field is being one on the
nose. -/
theorem ofPolyHom_eq_one_iff {y : Hex.FpPoly p}
    (hy : Hex.GFqRing.reduceMod f y = y) :
    ofPolyHom f hf hp hirr y = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hrepr := congrArg Hex.GFqField.repr h
    rw [ofPolyHom_apply] at hrepr
    rw [Hex.GFqField.repr_ofPoly, Hex.GFqField.repr_one,
      Hex.GFqRing.reduceMod_one f hf, hy] at hrepr
    exact hrepr
  · intro h
    subst h
    exact map_one _

set_option maxHeartbeats 400000 in
/-- The Horner power returns a reduced representative on a nonempty digit
list: its last step is a reduction. -/
theorem reduceMod_digitPowMod (hm : Hex.DensePoly.Monic f) (q : Nat)
    (x : Hex.FpPoly p) :
    ∀ (ds : List Nat) (acc : Hex.FpPoly p), ds ≠ [] →
      Hex.GFqRing.reduceMod f (Hex.Conway.digitPowMod f hm q x acc ds) =
        Hex.Conway.digitPowMod f hm q x acc ds
  | [], _, h => absurd rfl h
  | [_], acc, _ => by
      show Hex.GFqRing.reduceMod f (Hex.FpPoly.modByMonic f _ hm) =
        Hex.FpPoly.modByMonic f _ hm
      rw [show ∀ y, Hex.FpPoly.modByMonic f y hm = Hex.GFqRing.reduceMod f y from
        fun y => by rw [Hex.FpPoly.modByMonic, Hex.DensePoly.modByMonic_eq_mod]; rfl]
      exact Hex.GFqRing.reduceMod_idem f _
  | d :: e :: ds, acc, _ => by
      show Hex.GFqRing.reduceMod f
          (Hex.Conway.digitPowMod f hm q x _ (e :: ds)) = _
      exact reduceMod_digitPowMod hm q x (e :: ds) _ (by simp)

/-- Hex's Mathlib-free prime predicate implies Mathlib's. -/
theorem mathlibPrime_of_hexPrime {q : Nat} (h : Hex.Nat.Prime q) :
    Nat.Prime q :=
  Nat.prime_def.mpr ⟨h.two_le, fun m hm => h.2 m hm⟩

/-- Every prime dividing a validated prime-power product appears in its prime
list. This is unique factorization in the form the check needs: it is what
turns "the supplied primes multiply to `N`" into "the supplied primes are all
of them", so a short list cannot weaken the test. -/
theorem mem_of_prime_dvd_primePowerProduct :
    ∀ (qs es : List Nat) {q : Nat}, Nat.Prime q →
      (∀ r ∈ qs, Nat.Prime r) →
      q ∣ Hex.Conway.primePowerProduct qs es → q ∈ qs := by
  intro qs
  induction qs with
  | nil =>
      intro es q hq _ hdvd
      rw [show Hex.Conway.primePowerProduct [] es = 1 from rfl] at hdvd
      exact absurd (Nat.eq_one_of_dvd_one hdvd) hq.ne_one
  | cons r qs ih =>
      intro es q hq hall hdvd
      cases es with
      | nil =>
          rw [show Hex.Conway.primePowerProduct (r :: qs) [] = 1 from rfl] at hdvd
          exact absurd (Nat.eq_one_of_dvd_one hdvd) hq.ne_one
      | cons e es =>
          rw [show Hex.Conway.primePowerProduct (r :: qs) (e :: es) =
            r ^ e * Hex.Conway.primePowerProduct qs es from rfl] at hdvd
          rcases (Nat.Prime.dvd_mul hq).mp hdvd with hleft | hright
          · have hqr : q ∣ r := hq.dvd_of_dvd_pow hleft
            have hr : Nat.Prime r := hall r List.mem_cons_self
            rw [(Nat.prime_dvd_prime_iff_eq hq hr).mp hqr]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (ih es hq (fun s hs => hall s (List.mem_cons_of_mem _ hs)) hright)

/-! # The order of the Conway generator -/

/-- A verified executable primitivity certificate proves that the Conway
generator has multiplicative order `p ^ n - 1`.

This is the assembly point for the component transport lemmas above. The
factorization check makes `qs` exhaustive, while the two digit-power checks
become the hypotheses of `orderOf_eq_of_pow_and_pow_div_prime`. -/
theorem orderOf_gen_of_primitive {n : Nat} (h : Hex.Conway.SupportedEntry p n)
    {qs es fullDigits : List Nat} {perPrimeDigits : List (List Nat)}
    (hprimitive : Hex.Conway.Primitive p n h qs es fullDigits perPrimeDigits) :
    orderOf (Hex.GFq.ofPoly h Hex.FpPoly.X) = p ^ n - 1 := by
  have hcheck := hprimitive.check
  simp only [Hex.Conway.primitiveCheck, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hcheck
  -- Factorization, full digits, list length, per-prime digits, full power,
  -- and per-prime powers, in `primitiveCheck` order.
  rcases hcheck with
    ⟨⟨⟨⟨⟨hfactor, hfullDigits⟩, hlength⟩, hperDigits⟩, hfullPower⟩, hperPower⟩
  apply orderOf_eq_of_pow_and_pow_div_prime
  · have hn : 0 < n := by
      simpa only [HexGFqMathlib.GFq.conwayPoly_degree h] using
        Hex.Conway.conwayPoly_nonconstant p n h
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hn) h.prime.one_lt)
  · rw [← hfullDigits]
    change (ofPolyHom (Hex.Conway.conwayPoly p n h)
      (Hex.Conway.conwayPoly_nonconstant p n h) h.prime
      (Hex.Conway.conwayPoly_irreducible p n h) Hex.FpPoly.X) ^
        Hex.Conway.digitsValue p fullDigits = 1
    rw [← ofPolyHom_digitPowMod_one
      (Hex.Conway.conwayPoly_monic p n h) p Hex.FpPoly.X fullDigits]
    rw [hfullPower, map_one]
    rfl
  · intro q hq hqdiv
    have hqmem : q ∈ qs := mem_of_prime_dvd_primePowerProduct qs es hq
      (fun r hr => mathlibPrime_of_hexPrime (hprimitive.primes r hr))
      (hfactor.symm ▸ hqdiv)
    have hqmap : q ∈ (qs.zip perPrimeDigits).map Prod.fst := by
      rw [List.map_fst_zip (Nat.le_of_eq hlength.symm)]
      exact hqmem
    obtain ⟨⟨r, ds⟩, hrds, hr⟩ := List.mem_map.mp hqmap
    change r = q at hr
    subst r
    have hds : ds ∈ perPrimeDigits := (List.of_mem_zip hrds).2
    have hdigits : Hex.Conway.digitsValue p ds = (p ^ n - 1) / q :=
      hperDigits (q, ds) hrds
    have hrep : Hex.Conway.digitPowMod (Hex.Conway.conwayPoly p n h)
        (Hex.Conway.conwayPoly_monic p n h) p Hex.FpPoly.X 1 ds ≠ 1 := by
      intro heq
      have hnot := hperPower ds hds
      rw [heq] at hnot
      simp at hnot
    have hdsne : ds ≠ [] := by
      intro hnil
      subst ds
      exact hrep rfl
    rw [← hdigits]
    change (ofPolyHom (Hex.Conway.conwayPoly p n h)
      (Hex.Conway.conwayPoly_nonconstant p n h) h.prime
      (Hex.Conway.conwayPoly_irreducible p n h) Hex.FpPoly.X) ^
        Hex.Conway.digitsValue p ds ≠ 1
    rw [← ofPolyHom_digitPowMod_one
      (Hex.Conway.conwayPoly_monic p n h) p Hex.FpPoly.X ds]
    intro hone
    exact hrep ((ofPolyHom_eq_one_iff
      (reduceMod_digitPowMod (Hex.Conway.conwayPoly_monic p n h) p
        Hex.FpPoly.X ds 1 hdsne)).mp hone)

/-! # Committed generators

The generic theorem specializes to every committed nontrivial entry without
replaying its executable certificate. -/

/-- The Conway generator of `GF(2 ^ 2)` has order `3`. -/
theorem orderOf_gen_2_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_2 Hex.FpPoly.X) = 2 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_2

/-- The Conway generator of `GF(2 ^ 3)` has order `7`. -/
theorem orderOf_gen_2_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_3 Hex.FpPoly.X) = 2 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_3

/-- The Conway generator of `GF(2 ^ 4)` has order `15`. -/
theorem orderOf_gen_2_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_4 Hex.FpPoly.X) = 2 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_4

/-- The Conway generator of `GF(2 ^ 5)` has order `31`. -/
theorem orderOf_gen_2_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_5 Hex.FpPoly.X) = 2 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_5

/-- The Conway generator of `GF(2 ^ 6)` has order `63`. -/
theorem orderOf_gen_2_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_6 Hex.FpPoly.X) = 2 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_6

/-- The Conway generator of `GF(2 ^ 7)` has order `127`. -/
theorem orderOf_gen_2_7 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_7 Hex.FpPoly.X) = 2 ^ 7 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_7

/-- The Conway generator of `GF(2 ^ 8)` has order `255`. -/
theorem orderOf_gen_2_8 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_2_8 Hex.FpPoly.X) = 2 ^ 8 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_2_8

/-- The Conway generator of `GF(3 ^ 1)` has order `2`. -/
theorem orderOf_gen_3_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_1 Hex.FpPoly.X) = 3 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_1

/-- The Conway generator of `GF(3 ^ 2)` has order `8`. -/
theorem orderOf_gen_3_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_2 Hex.FpPoly.X) = 3 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_2

/-- The Conway generator of `GF(3 ^ 3)` has order `26`. -/
theorem orderOf_gen_3_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_3 Hex.FpPoly.X) = 3 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_3

/-- The Conway generator of `GF(3 ^ 4)` has order `80`. -/
theorem orderOf_gen_3_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_4 Hex.FpPoly.X) = 3 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_4

/-- The Conway generator of `GF(3 ^ 5)` has order `242`. -/
theorem orderOf_gen_3_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_5 Hex.FpPoly.X) = 3 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_5

/-- The Conway generator of `GF(3 ^ 6)` has order `728`. -/
theorem orderOf_gen_3_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_3_6 Hex.FpPoly.X) = 3 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_3_6

/-- The Conway generator of `GF(5 ^ 1)` has order `4`. -/
theorem orderOf_gen_5_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_1 Hex.FpPoly.X) = 5 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_1

/-- The Conway generator of `GF(5 ^ 2)` has order `24`. -/
theorem orderOf_gen_5_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_2 Hex.FpPoly.X) = 5 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_2

/-- The Conway generator of `GF(5 ^ 3)` has order `124`. -/
theorem orderOf_gen_5_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_3 Hex.FpPoly.X) = 5 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_3

/-- The Conway generator of `GF(5 ^ 4)` has order `624`. -/
theorem orderOf_gen_5_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_4 Hex.FpPoly.X) = 5 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_4

/-- The Conway generator of `GF(5 ^ 5)` has order `3124`. -/
theorem orderOf_gen_5_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_5 Hex.FpPoly.X) = 5 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_5

/-- The Conway generator of `GF(5 ^ 6)` has order `15624`. -/
theorem orderOf_gen_5_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_5_6 Hex.FpPoly.X) = 5 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_5_6

/-- The Conway generator of `GF(7 ^ 1)` has order `6`. -/
theorem orderOf_gen_7_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_1 Hex.FpPoly.X) = 7 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_1

/-- The Conway generator of `GF(7 ^ 2)` has order `48`. -/
theorem orderOf_gen_7_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_2 Hex.FpPoly.X) = 7 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_2

/-- The Conway generator of `GF(7 ^ 3)` has order `342`. -/
theorem orderOf_gen_7_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_3 Hex.FpPoly.X) = 7 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_3

/-- The Conway generator of `GF(7 ^ 4)` has order `2400`. -/
theorem orderOf_gen_7_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_4 Hex.FpPoly.X) = 7 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_4

/-- The Conway generator of `GF(7 ^ 5)` has order `16806`. -/
theorem orderOf_gen_7_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_5 Hex.FpPoly.X) = 7 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_5

/-- The Conway generator of `GF(7 ^ 6)` has order `117648`. -/
theorem orderOf_gen_7_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_7_6 Hex.FpPoly.X) = 7 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_7_6

/-- The Conway generator of `GF(11 ^ 1)` has order `10`. -/
theorem orderOf_gen_11_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_1 Hex.FpPoly.X) = 11 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_1

/-- The Conway generator of `GF(11 ^ 2)` has order `120`. -/
theorem orderOf_gen_11_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_2 Hex.FpPoly.X) = 11 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_2

/-- The Conway generator of `GF(11 ^ 3)` has order `1330`. -/
theorem orderOf_gen_11_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_3 Hex.FpPoly.X) = 11 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_3

/-- The Conway generator of `GF(11 ^ 4)` has order `14640`. -/
theorem orderOf_gen_11_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_4 Hex.FpPoly.X) = 11 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_4

/-- The Conway generator of `GF(11 ^ 5)` has order `161050`. -/
theorem orderOf_gen_11_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_5 Hex.FpPoly.X) = 11 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_5

/-- The Conway generator of `GF(11 ^ 6)` has order `1771560`. -/
theorem orderOf_gen_11_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_11_6 Hex.FpPoly.X) = 11 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_11_6

/-- The Conway generator of `GF(13 ^ 1)` has order `12`. -/
theorem orderOf_gen_13_1 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_1 Hex.FpPoly.X) = 13 ^ 1 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_1

/-- The Conway generator of `GF(13 ^ 2)` has order `168`. -/
theorem orderOf_gen_13_2 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_2 Hex.FpPoly.X) = 13 ^ 2 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_2

/-- The Conway generator of `GF(13 ^ 3)` has order `2196`. -/
theorem orderOf_gen_13_3 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_3 Hex.FpPoly.X) = 13 ^ 3 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_3

/-- The Conway generator of `GF(13 ^ 4)` has order `28560`. -/
theorem orderOf_gen_13_4 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_4 Hex.FpPoly.X) = 13 ^ 4 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_4

/-- The Conway generator of `GF(13 ^ 5)` has order `371292`. -/
theorem orderOf_gen_13_5 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_5 Hex.FpPoly.X) = 13 ^ 5 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_5

/-- The Conway generator of `GF(13 ^ 6)` has order `4826808`. -/
theorem orderOf_gen_13_6 :
    orderOf (Hex.GFq.ofPoly Hex.Conway.supportedEntry_13_6 Hex.FpPoly.X) = 13 ^ 6 - 1 :=
  orderOf_gen_of_primitive _ Hex.Conway.primitive_13_6

end HexGFqMathlib
