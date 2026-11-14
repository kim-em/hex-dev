/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PolynomialBuild
public import HexRCF.RealCoefficients.PolynomialSignsSoundness
public import HexRCF.RealCoefficients.QueryCells
public section

namespace Hex.RCF.RealCoefficients.PolynomialBuild
open Hex Hex.RealFormula Hex.OrderedFn.Oracle Hex.RealClosure HexPolyTheory.Interpret

attribute [local instance 2500] MvPoly.instZero MvPoly.instOneOfLawfulBEq
  MvPoly.instAddOfLawfulBEq
  MvPoly.instMulOfAddOfLawfulBEq MvPoly.instNegOfLawfulBEq MvPoly.instSubOfAddOfNegOfLawfulBEq
  MvPoly.instNatCast

theorem values_spec (valuation : Fin n → ℝ) (i : Fin n) :
    PolynomialBounds.value valuation (values i) = valuation i := by
  unfold PolynomialBounds.value values
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp

theorem point_spec (valuation : Fin n → ℝ) (d : Dyadic) :
    PolynomialBounds.value valuation (point d) = HexRealRootsTheory.Dyadic.toReal d := by
  unfold PolynomialBounds.value point
  rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp [HexRealRootsTheory.toReal_eq_cast_toRat]

/-- The existing grouped compiler retains the exact shared formula valuation. -/
theorem query_eval (valuation : Fin n → ℝ) (atom : RealFormula.Poly (n + 1)) (x : ℝ) :
    (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
      (Transport.polynomial (PolynomialBounds.value valuation) (query atom))).eval x =
        atom.eval (append valuation x) := by
  have laws := PolynomialBounds.closed_native valuation
  have compiled := RepresentationSpecialize.map_eval (PolynomialBounds.value valuation)
    laws.read_one (fun a b => laws.read_add a b trivial trivial)
    (fun a b => laws.read_mul a b trivial trivial) laws.read_natCast
    (PolynomialBounds.value_neg valuation) laws.read_zero values atom x
  simpa only [query, values_spec] using compiled

/-- Both accepted verdicts have their exact source-formula meaning. The
coefficient bounds are interpreted at one fixed authenticated valuation. -/
theorem check_spec (bounds : Fin n → Bounds) (valuation : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (valuation i))
    (formula : QF (n + 1)) (quantifier : Quantifier) (cert : Certificate n) (verdict : Bool)
    (checked : check bounds formula cert = true) (folded : run formula quantifier cert = some verdict) :
    verdict = true ↔ (Prenex.quant quantifier (.matrix formula)).toProp valuation := by
  have parts := Bool.and_eq_true_iff.mp checked
  let lookup := PolynomialSigns.lookup cert.entries cert.index
  have sound := PolynomialSigns.lookup_spec bounds valuation contained cert.entries parts.1 cert.index
  cases quantifier with
  | forallReal =>
    have meaning := QueryCells.forall_formula lookup (PolynomialBounds.value valuation)
      (PolynomialBounds.closed_native valuation) sound point (point_spec valuation) () query formula
      cert.radical cert.isolation cert.rows (fun x => append valuation x) (query_eval valuation) parts.2
    change OptionFold.allArray _ _ = some verdict at folded
    rw [folded] at meaning
    simpa only [Option.some.injEq, Prenex.toProp] using meaning
  | existsReal =>
    have meaning := QueryCells.exists_formula lookup (PolynomialBounds.value valuation)
      (PolynomialBounds.closed_native valuation) sound point (point_spec valuation) () query formula
      cert.radical cert.isolation cert.rows (fun x => append valuation x) (query_eval valuation) parts.2
    change OptionFold.anyArray _ _ = some verdict at folded
    rw [folded] at meaning
    simpa only [Option.some.injEq, Prenex.toProp] using meaning

/-- Ordinary real truth follows from frozen finite checks, independently of
the numerical producer, convergence laws or transcendence hypotheses. -/
theorem check_sound (bounds : Fin n → Bounds) (valuation : Fin n → ℝ)
    (contained : ∀ i, Contains (bounds i) (valuation i))
    (formula : QF (n + 1)) (quantifier : Quantifier) (cert : Certificate n)
    (checked : check bounds formula cert = true) (folded : run formula quantifier cert = some true) :
    (Prenex.quant quantifier (.matrix formula)).toProp valuation :=
  (check_spec bounds valuation contained formula quantifier cert true checked folded).mp rfl

end Hex.RCF.RealCoefficients.PolynomialBuild
