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
makes the supplied prime list exhaustive. Generated modules specialize the result to every supported entry, including
the trivial multiplicative group in characteristic two and degree one.
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

/-- The binary generator power represents the corresponding field power. -/
theorem ofPolyHom_powerResidue (hm : Hex.DensePoly.Monic f) (k : Nat) :
    ofPolyHom f hf hp hirr (Hex.Conway.powerResidue f hm k) =
      (ofPolyHom f hf hp hirr Hex.FpPoly.X) ^ k := by
  rw [Hex.Conway.powerResidue, ofPolyHom_modByMonic, Hex.Conway.powMod_eq,
    ← Hex.Conway.linPowMod_eq]
  exact ofPolyHom_linPowMod hm Hex.FpPoly.X k

/-- A generator power representative is already reduced. -/
theorem reduceMod_powerResidue (hm : Hex.DensePoly.Monic f) (k : Nat) :
    Hex.GFqRing.reduceMod f (Hex.Conway.powerResidue f hm k) =
      Hex.Conway.powerResidue f hm k := by
  unfold Hex.Conway.powerResidue
  rw [show ∀ y, Hex.FpPoly.modByMonic f y hm = Hex.GFqRing.reduceMod f y from
    fun y => by rw [Hex.FpPoly.modByMonic, Hex.DensePoly.modByMonic_eq_mod]; rfl]
  exact Hex.GFqRing.reduceMod_idem f _

/-! # From the executable check to `orderOf`

Two more ingredients. Reduction is not injective in general, so a `≠ 1` on
representatives does not by itself give a `≠ 1` in the field — but on *reduced*
representatives it does: `reduceMod_powerResidue` proves that `powerResidue`
always returns a reduced representative. The validated product proves that
the supplied prime list includes every prime divisor of the order.
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
factorization check makes `qs` exhaustive, while the two power checks
become the hypotheses of `orderOf_eq_of_pow_and_pow_div_prime`. -/
theorem orderOf_gen_of_primitive {n : Nat} (h : Hex.Conway.SupportedEntry p n)
    {qs es : List Nat}
    (hprimitive : Hex.Conway.Primitive p n h qs es) :
    orderOf (Hex.GFq.ofPoly h Hex.FpPoly.X) = p ^ n - 1 := by
  have hcheck := hprimitive.check
  simp only [Hex.Conway.primitiveCheck, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨hfactor, hfullPower⟩, hperPower⟩
  apply orderOf_eq_of_pow_and_pow_div_prime
  · have hn : 0 < n := by
      simpa only [HexGFqMathlib.GFq.conwayPoly_degree h] using
        Hex.Conway.conwayPoly_nonconstant p n h
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hn) h.prime.one_lt)
  · change (ofPolyHom (Hex.Conway.conwayPoly p n h)
      (Hex.Conway.conwayPoly_nonconstant p n h) h.prime
      (Hex.Conway.conwayPoly_irreducible p n h) Hex.FpPoly.X) ^
        (p ^ n - 1) = 1
    rw [← ofPolyHom_powerResidue
      (Hex.Conway.conwayPoly_monic p n h) ((p ^ n - 1))]
    rw [hfullPower, map_one]
    rfl
  · intro q hq hqdiv
    have hqmem : q ∈ qs := mem_of_prime_dvd_primePowerProduct qs es hq
      (fun r hr => mathlibPrime_of_hexPrime (hprimitive.primes r hr))
      (hfactor.symm ▸ hqdiv)
    have hrep : Hex.Conway.powerResidue (Hex.Conway.conwayPoly p n h)
        (Hex.Conway.conwayPoly_monic p n h) (((p ^ n - 1) / q)) ≠ 1 := by
      intro heq
      have hnot := hperPower q hqmem
      rw [heq] at hnot
      simp at hnot
    change (ofPolyHom (Hex.Conway.conwayPoly p n h)
      (Hex.Conway.conwayPoly_nonconstant p n h) h.prime
      (Hex.Conway.conwayPoly_irreducible p n h) Hex.FpPoly.X) ^
        ((p ^ n - 1) / q) ≠ 1
    rw [← ofPolyHom_powerResidue
      (Hex.Conway.conwayPoly_monic p n h) (((p ^ n - 1) / q))]
    intro hone
    exact hrep ((ofPolyHom_eq_one_iff
      (reduceMod_powerResidue (Hex.Conway.conwayPoly_monic p n h)
        (((p ^ n - 1) / q)))).mp hone)

end HexGFqMathlib
