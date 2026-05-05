import HexHenselMathlib.Basic
import HexPolyMathlib.Basic

/-!
Mathlib-facing correctness and uniqueness theorem surface for executable
Hensel lifting.

The statements in this module transfer the `Hex.ZPoly` Hensel API through
`HexPolyMathlib.toPolynomial`, while keeping all new content proof-only.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/-- The iterative executable lift gives a factorization of `f` over Mathlib polynomials modulo `p^k`. -/
theorem hensel_correct
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod (p ^ k))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  sorry

/-- The iterative executable lift extends the input factorization modulo `p`. -/
theorem hensel_extends
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod p)
    (HexPolyMathlib.toPolynomial r.g).map φ =
        (HexPolyMathlib.toPolynomial g).map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ =
        (HexPolyMathlib.toPolynomial h).map φ := by
  sorry

/-- The iterative executable lift preserves the Mathlib degree of the monic lifted factor. -/
theorem hensel_degree
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    (HexPolyMathlib.toPolynomial r.g).natDegree =
      (HexPolyMathlib.toPolynomial g).natDegree := by
  sorry

/--
Coefficientwise executable congruence modulo `m` transfers to equality after
mapping the corresponding Mathlib polynomials to `ZMod m`.
-/
theorem zpoly_congr_toPolynomial_map_eq
    (f g : Hex.ZPoly) (m : Nat)
    (hcongr : Hex.ZPoly.congr f g m) :
    let φ := Int.castRingHom (ZMod m)
    (HexPolyMathlib.toPolynomial f).map φ =
      (HexPolyMathlib.toPolynomial g).map φ := by
  sorry

/--
Equality of Mathlib polynomial reductions modulo `m` gives the executable
coefficientwise congruence used by `Hex.ZPoly`.
-/
theorem zpoly_congr_of_toPolynomial_map_eq
    (f g : Hex.ZPoly) (m : Nat)
    (hmap :
      let φ := Int.castRingHom (ZMod m)
      (HexPolyMathlib.toPolynomial f).map φ =
        (HexPolyMathlib.toPolynomial g).map φ) :
    Hex.ZPoly.congr f g m := by
  sorry

/-- The executable monic predicate transfers to Mathlib's polynomial monic predicate. -/
theorem toPolynomial_monic_of_dense_monic
    (f : Hex.ZPoly) (hmonic : Hex.DensePoly.Monic f) :
    (HexPolyMathlib.toPolynomial f).Monic := by
  sorry

/--
The quadratic executable step gives a Mathlib factorization modulo `m*m`.
This is the Mathlib-facing form of `Hex.ZPoly.quadraticHenselStep_factor_spec`.
-/
theorem quadraticHenselStep_factor_correct
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hprod : Hex.ZPoly.congr (g * h) f m)
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    let φ := Int.castRingHom (ZMod (m * m))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  sorry

/--
The quadratic executable step updates Bezout witnesses modulo `m*m`.
This is the Mathlib-facing form of `Hex.ZPoly.quadraticHenselStep_bezout_spec`.
-/
theorem quadraticHenselStep_bezout_correct
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hprod : Hex.ZPoly.congr (g * h) f m)
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    let φ := Int.castRingHom (ZMod (m * m))
    (HexPolyMathlib.toPolynomial r.s).map φ *
          (HexPolyMathlib.toPolynomial r.g).map φ +
        (HexPolyMathlib.toPolynomial r.t).map φ *
          (HexPolyMathlib.toPolynomial r.h).map φ =
      (1 : Polynomial (ZMod (m * m))) := by
  sorry

/-- The quadratic step preserves monicity on the lifted `g` factor in Mathlib form. -/
theorem quadraticHenselStep_monic
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    (HexPolyMathlib.toPolynomial r.g).Monic := by
  sorry

/--
Quadratic lifting is compatible with the Mathlib uniqueness theorem at the
doubled prime-power precision.
-/
theorem quadraticHenselStep_unique_mod_pow_two_mul
    (f g h s t : Hex.ZPoly) (g' h' : Polynomial ℤ)
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    (hk : 0 < k)
    (hprod : Hex.ZPoly.congr (g * h) f (p ^ k))
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 (p ^ k))
    (hmonic : Hex.DensePoly.Monic g)
    (hg' : g'.Monic)
    (hdeg :
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).natDegree =
        g'.natDegree)
    (hprod' :
      let φ := Int.castRingHom (ZMod (p ^ (2 * k)))
      (g'.map φ) * (h'.map φ) =
        (HexPolyMathlib.toPolynomial f).map φ)
    (hg1 :
      let φ := Int.castRingHom (ZMod p)
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).map φ =
        g'.map φ)
    (hh1 :
      let φ := Int.castRingHom (ZMod p)
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h).map φ =
        h'.map φ)
    (hcop :
      let φ := Int.castRingHom (ZMod p)
      IsCoprime
        ((HexPolyMathlib.toPolynomial
          (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).map φ)
        ((HexPolyMathlib.toPolynomial
          (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h).map φ)) :
    let r := Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t
    let φ := Int.castRingHom (ZMod (p ^ (2 * k)))
    (HexPolyMathlib.toPolynomial r.g).map φ = g'.map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ = h'.map φ := by
  sorry

/-- Coprime monic factorizations with the same reduction modulo `p` are unique modulo `p^k`. -/
theorem hensel_unique (f g h g' h' : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (hk : 0 < k)
    (hg : g.Monic) (hg' : g'.Monic)
    (hdeg : g.natDegree = g'.natDegree)
    (hprod :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g.map φ) * (h.map φ) = f.map φ)
    (hprod' :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g'.map φ) * (h'.map φ) = f.map φ)
    (hg1 :
      let φ := Int.castRingHom (ZMod p)
      g.map φ = g'.map φ)
    (hh1 :
      let φ := Int.castRingHom (ZMod p)
      h.map φ = h'.map φ)
    (hcop :
      let φ := Int.castRingHom (ZMod p)
      IsCoprime (g.map φ) (h.map φ)) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    g.map φ = g'.map φ ∧ h.map φ = h'.map φ := by
  sorry

/--
The linear and quadratic multifactor lifters agree modulo `p ^ k` after
canonical reduction, when both are applied to the same input under the
recursive `MultifactorLiftInvariant` precondition consumed by both
`Hex.ZPoly.multifactorLift_spec` and
`Hex.ZPoly.multifactorLiftQuadratic_spec`.

The result is stated over the public array/product multifactor surface
rather than the private split-tree helpers, and is expressed in Mathlib
form via `Polynomial.map (Int.castRingHom (ZMod (p ^ k)))`. Through
`zpoly_congr_toPolynomial_map_eq` / `zpoly_congr_of_toPolynomial_map_eq`,
this is equivalent to per-factor canonicalisation by
`Hex.ZPoly.reduceModPow _ p k`.

This is the lift-uniqueness obligation that `hex-hensel` defers to
`hex-hensel-mathlib`; see `SPEC/Libraries/hex-hensel.md` and the
companion-statement note at the top of `HexHensel/QuadraticMultifactor.lean`.
-/
theorem multifactorLift_eq_multifactorLiftQuadratic
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (f : Hex.ZPoly) (factors : Array Hex.ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors.toList) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    (Hex.ZPoly.multifactorLift p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) =
      (Hex.ZPoly.multifactorLiftQuadratic p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) := by
  sorry

end

end HexHenselMathlib
