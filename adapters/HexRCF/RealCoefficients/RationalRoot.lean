/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public meta import HexRCF.RealCoefficients.Tactic

public section

namespace Hex.RCF.RealCoefficients.RationalRoot

/-- The denominator-cleared equation of a positive rational root. Its selected
embedding is authenticated by a real-axis isolating square. -/
@[expose] def polynomial (base : Rat) (degree : Nat) : ZPoly :=
  DensePoly.monomial degree (base.den : Int) - DensePoly.C base.num

theorem interpret (base : Rat) (degree : Nat) :
    LiteralSign.realPoly (ZPoly.toRatPoly (polynomial base degree)) =
      Polynomial.C (base.den : ℝ) * (Polynomial.X : Polynomial ℝ) ^ degree -
        Polynomial.C (base.num : ℝ) := by
  ext i
  simp [LiteralSign.realPoly, polynomial, HexPolyMathlib.Interpret.coeff_interpret,
    ZPoly.coeff_toRatPoly, DensePoly.coeff_monomial,
    DensePoly.coeff_C, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  simp only [← Polynomial.C_eq_intCast, Polynomial.coeff_C]
  split_ifs <;> norm_num

theorem selected (base : Rat) (degree : Nat) (hdegree : degree ≠ 0)
    (s : DyadicSquare)
    (hw : atomWitness (polynomial base degree) s)
    (hp : (mahlerPrec (polynomial base degree) : Int) ≤ s.prec)
    (hreal : s.meetsRealAxis = true)
    (hpositive : 0 < ((s.re - s.radiusHi).toRat : ℝ)) :
    (Field.literalRep (polynomial base degree) s hw hp).root.re =
      (base : ℝ) ^ (1 / (degree : ℝ)) := by
  let rep := Field.literalRep (polynomial base degree) s hw hp
  have hroot := Field.literalRep_root (polynomial base degree) s hw hp hreal
  rw [interpret] at hroot
  have hproduct : (base.den : ℝ) * rep.root.re ^ degree = (base.num : ℝ) := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hroot
  have hden : (base.den : ℝ) ≠ 0 := by exact_mod_cast base.den_nz
  have hpower : rep.root.re ^ degree = (base : ℝ) := by
    rw [Rat.cast_def]
    exact (eq_div_iff hden).mpr (by simpa only [mul_comm] using hproduct)
  have hpos : 0 < rep.root.re := hpositive.trans
    (Field.literalRep_bounds (polynomial base degree) s hw hp).1
  rw [← hpower, one_div, Real.pow_rpow_inv_natCast hpos.le hdegree]

end Hex.RCF.RealCoefficients.RationalRoot

public meta section
namespace Hex.RCF.RealCoefficients.RationalRoot
open Hex Lean Meta Qq Hex.RealFormula.Reify

structure Parameters where
  base : Rat
  degree : Nat
  deriving Inhabited

/-- Detect root notation without treating natural powers as atomic leaves. -/
def isNotation (e : Expr) : Bool :=
  e.isAppOfArity ``Real.sqrt 1 || e.isAppOfArity ``Real.rpow 2 ||
    (e.isAppOfArity ``HPow.hPow 6 && e.getAppArgs[1]!.isConstOf ``Real)

/-- Recognize a positive rational base and reciprocal natural degree. Shared
reflection limits remain structured errors; source admission retains every
original base/exponent divisor before this classification. -/
def parameters? (original : Expr) (config : Hex.RealFormula.Reify.Config := {}) :
    MetaM (Except Error (Option Parameters)) := do
  let source := original.consumeMData
  let args := source.getAppArgs
  let square := source.isAppOfArity ``Real.sqrt 1
  let realPower ← if source.isAppOfArity ``HPow.hPow 6 then
      pure ((← inferType args[5]!).isConstOf ``Real) else pure false
  let parts := if square then some (args[0]!, q((1 / 2 : ℝ)))
    else if source.isAppOfArity ``Real.rpow 2 then some (args[0]!, args[1]!)
    else if realPower then some (args[4]!, args[5]!) else none
  let some (base, exponent) := parts | return .ok none
  let base ← Reify.lowerSources #[] base
  let action : ReifyM Nat := do
    let _ ← arithmetic #[] base
    Coefficients.rootDegree exponent
  let degree ← match ← (action.run
      {config, budget := .ofBudget config.ring.budget}).run with
    | .error error => return .error error
    | .ok (degree, _) => pure degree
  let .ok value ← (Hex.RCF.Reify.recognizeCoefficient base).run | return .ok none
  unless 0 < value do return .ok none
  return .ok (some ⟨value, degree⟩)

/-- Prove the selected positive-root notation equals the original source,
using checked source lowering. This does not discharge source divisors. -/
private def identifyCore (source : Expr) (parameters : Parameters) : MetaM Expr := do
  let num : Q(ℤ) := mkIntLit parameters.base.num
  let den : Q(ℕ) := mkNatLit parameters.base.den
  let degree : Q(ℕ) := mkNatLit parameters.degree
  let canonical : Q(ℝ) := q(((mkRat $num $den : ℚ) : ℝ) ^ (1 / ($degree : ℝ)))
  let (lowered, equality) ← Reify.lowerWithProof #[] source
  let goal ← mkFreshExprMVar (← mkEq canonical lowered)
  let remaining ← Elab.runTactic' goal.mvarId!
    (← `(tactic| norm_num [Real.sqrt_eq_rpow, mkRat]))
  unless remaining.isEmpty do
    throwError "rcf: positive rational-root alias did not normalize"
  let proof ← mkEqTrans (← instantiateMVars goal) (← mkEqSymm equality)
  Hex.RCF.checkProof `Hex.RCF.RealCoefficients.RationalRoot
    (← mkEq canonical source) proof

/-- Alias identification restores the caller's full state on refusal. -/
def identify (source : Expr) (parameters : Parameters) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (identifyCore source parameters)
    (fun result => unless result.isSome do saved.restore)
  return result

end Hex.RCF.RealCoefficients.RationalRoot
