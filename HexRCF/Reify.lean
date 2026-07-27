/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Soundness
public import HexRealRootsMathlib.IsolateRoots
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public meta import HexRCF.Decision
public meta import Mathlib.Lean.Elab.Tactic.Meta
public meta import Qq
public import Lean

public section
set_option backward.proofsInPublic true

/-!
# Reification support for the `rcf` tactic

The trusted portion of reification consists of small transport lemmas. Meta
code may propose integer coefficients and a positive denominator scale, but the
kernel checks the resulting polynomial-evaluation identity before any reflected
atom is related to the source goal.
-/

namespace Hex.RCF

/-- Transport any supported comparison across subtraction and multiplication
by a positive scalar. -/
theorem Cmp.scale_sub_iff (cmp : Cmp) {lhs rhs scale : ℝ}
    (hscale : 0 < scale) :
    cmp.toProp (scale * (lhs - rhs)) 0 ↔ cmp.toProp lhs rhs := by
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  have hscaleNonneg : 0 ≤ scale := hscale.le
  have hscaleNotNeg : ¬scale < 0 := not_lt_of_ge hscaleNonneg
  have hscaleNotNonpos : ¬scale ≤ 0 := not_le_of_gt hscale
  cases cmp <;>
    simp [Cmp.toProp, mul_neg_iff, mul_nonpos_iff, sub_eq_zero,
      hscale, hscale0, hscaleNonneg, hscaleNotNeg, hscaleNotNonpos]

/-- A kernel-checked scaled evaluation identity validates one reified atom. -/
theorem Atom.toProp_iff_scale {p : ZPoly} {cmp : Cmp}
    {x lhs rhs scale : ℝ} (hscale : 0 < scale)
    (heval : Polynomial.aeval x (HexPolyZMathlib.toPolynomial p) =
      scale * (lhs - rhs)) :
    (Atom.mk p cmp).toProp x ↔ cmp.toProp lhs rhs := by
  rw [Atom.toProp, heval]
  exact cmp.scale_sub_iff hscale

/-- Natural denominator clearing is a convenient literal specialization for
the meta reifier. -/
theorem Atom.toProp_iff_natScale {p : ZPoly} {cmp : Cmp}
    {x lhs rhs : ℝ} {scale : Nat} (hscale : 0 < scale)
    (heval : Polynomial.aeval x (HexPolyZMathlib.toPolynomial p) =
      (scale : ℝ) * (lhs - rhs)) :
    (Atom.mk p cmp).toProp x ↔ cmp.toProp lhs rhs := by
  apply Atom.toProp_iff_scale (by exact_mod_cast hscale) heval

namespace Sentence

/-- Transport a reflected universal sentence along its formula equivalence. -/
theorem forallReal_iff {formula : Formula} {predicate : ℝ → Prop}
    (h : ∀ x, formula.toProp x ↔ predicate x) :
    Sentence.toProp (.forallReal formula) ↔ ∀ x, predicate x := by
  exact forall_congr' h

/-- Transport a reflected existential sentence along its formula equivalence. -/
theorem existsReal_iff {formula : Formula} {predicate : ℝ → Prop}
    (h : ∀ x, formula.toProp x ↔ predicate x) :
    Sentence.toProp (.existsReal formula) ↔ ∃ x, predicate x := by
  exact exists_congr h

/-- Transport a reflected bounded universal sentence and its dyadic endpoints. -/
theorem forallIoc_iff {a b : Dyadic} {a' b' : ℝ} {formula : Formula}
    {predicate : ℝ → Prop}
    (ha : HexRealRootsMathlib.Dyadic.toReal a = a')
    (hb : HexRealRootsMathlib.Dyadic.toReal b = b')
    (h : ∀ x, formula.toProp x ↔ predicate x) :
    Sentence.toProp (.forallIoc a b formula) ↔
      ∀ x ∈ Set.Ioc a' b', predicate x := by
  simp only [Sentence.toProp, ha, hb]
  exact forall_congr' fun _ => imp_congr Iff.rfl (h _)

/-- Transport a reflected bounded existential sentence and its dyadic endpoints. -/
theorem existsIoc_iff {a b : Dyadic} {a' b' : ℝ} {formula : Formula}
    {predicate : ℝ → Prop}
    (ha : HexRealRootsMathlib.Dyadic.toReal a = a')
    (hb : HexRealRootsMathlib.Dyadic.toReal b = b')
    (h : ∀ x, formula.toProp x ↔ predicate x) :
    Sentence.toProp (.existsIoc a b formula) ↔
      ∃ x ∈ Set.Ioc a' b', predicate x := by
  simp only [Sentence.toProp, ha, hb]
  exact exists_congr fun _ => and_congr Iff.rfl (h _)

end Sentence

/-- Close evaluation identities for literal `ZPoly` coefficients and accepted
ring syntax. The parser remains untrusted: unsupported or misparsed syntax
merely makes this proof fail during elaboration. -/
macro "rcf_ring" : tactic =>
  `(tactic|
    (simp only [HexRealRootsMathlib.aeval_toPolynomial_ofCoeffs] <;>
     simp [Hex.DensePoly.coeff_ofCoeffs, Finset.sum_range_succ,
       Finset.sum_range_zero, Polynomial.aeval_X, Polynomial.aeval_C,
       map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one] <;>
     norm_num <;>
     push_cast <;>
     ring))

namespace Reify

open Lean Meta Qq

/-- Runtime and literal forms of a reflected formula, plus its checked bridge
to the source proposition at the current bound variable. -/
private meta structure FormulaResult where
  formula : Formula
  expr : Expr
  proof : Expr

/-- Exact rational value of a closed real expression. -/
private meta def scalarRat (e : Expr) : MetaM Rat := do
  let eQ : Q(ℝ) := e
  try
    let ⟨value, _num, _den, _proof⟩ ←
      Mathlib.Meta.NormNum.deriveRat eQ (_inst := q(inferInstance))
    return value
  catch _ =>
    throwError "rcf: symbolic or non-rational coefficient{indentExpr e}"

/-- Natural exponentiation for runtime rational polynomials. -/
private meta def powRatPoly (base : DensePoly Rat) (power : Nat) : DensePoly Rat :=
  Id.run do
    let mut result := DensePoly.C (1 : Rat)
    for _ in [0:power] do result := result * base
    return result

/-- Parse one real polynomial expression relative to its sole permitted free
variable. Closed subexpressions are normalized exactly by `norm_num`. -/
private meta partial def parsePoly (x : Expr) (fuel : Nat)
    (input : Expr) : MetaM (DensePoly Rat) := do
  let input := input.consumeMData
  if input == x then
    return DensePoly.ofCoeffs #[(0 : Rat), 1]
  if !input.containsFVar x.fvarId! then
    return DensePoly.C (← scalarRat input)
  match input.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, left, right]) =>
      return (← parsePoly x fuel left) + (← parsePoly x fuel right)
  | (``HSub.hSub, #[_, _, _, _, left, right]) =>
      return (← parsePoly x fuel left) - (← parsePoly x fuel right)
  | (``HMul.hMul, #[_, _, _, _, left, right]) =>
      return (← parsePoly x fuel left) * (← parsePoly x fuel right)
  | (``Neg.neg, #[_, _, value]) => return -(← parsePoly x fuel value)
  | (``HPow.hPow, #[_, _, _, _, base, power]) =>
      let some n ← getNatValue? power
        | throwError "rcf: polynomial exponent is not a natural literal{indentExpr power}"
      return powRatPoly (← parsePoly x fuel base) n
  | (``HDiv.hDiv, #[_, _, _, _, numerator, denominator]) =>
      if denominator.containsFVar x.fvarId! then
        throwError "rcf: division by an expression containing the variable is not polynomial; \
          clear denominators by hand"
      let q ← scalarRat denominator
      if q = 0 then throwError "rcf: division by zero in a polynomial coefficient"
      return DensePoly.scale q⁻¹ (← parsePoly x fuel numerator)
  | (``Inv.inv, #[_, _, value]) =>
      if value.containsFVar x.fvarId! then
        throwError "rcf: inversion of an expression containing the variable is not polynomial; \
          clear denominators by hand"
      return DensePoly.C (← scalarRat input)
  | _ =>
      let (fn, _) := input.getAppFnArgs
      if fn == ``Real.sin || fn == ``Real.exp then
        throwError "rcf: non-polynomial real functions such as sin and exp are unsupported"
      if fuel = 0 then
        throwError "rcf: unsupported polynomial syntax{indentExpr input}"
      match ← unfoldDefinition? input with
      | some unfolded => parsePoly x (fuel - 1) unfolded
      | none =>
          if input.isFVar then
            throwError "rcf: more than one variable or a symbolic coefficient is unsupported"
          throwError "rcf: unsupported polynomial syntax{indentExpr input}"

/-- Clear one positive common denominator from a rational polynomial. -/
private meta def clearPoly (p : DensePoly Rat) : Nat × ZPoly :=
  let den := p.toArray.foldl (fun acc q => Nat.lcm acc q.den) 1
  let coeffs := p.toArray.map fun q => q.num * Int.ofNat (den / q.den)
  (den, DensePoly.ofCoeffs coeffs)

/-- Recover the reflected comparison and its two real operands. -/
private meta def comparison? (e : Expr) : Option (Cmp × Expr × Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``LT.lt, #[_, _, left, right]) => some (.lt, left, right)
  | (``LE.le, #[_, _, left, right]) => some (.le, left, right)
  | (``GT.gt, #[_, _, left, right]) => some (.gt, left, right)
  | (``GE.ge, #[_, _, left, right]) => some (.ge, left, right)
  | (``Eq, #[_, left, right]) => some (.eq, left, right)
  | (``Ne, #[_, left, right]) => some (.ne, left, right)
  | (``Not, #[body]) =>
      match body.consumeMData.getAppFnArgs with
      | (``Eq, #[_, left, right]) => some (.ne, left, right)
      | _ => none
  | _ => none

/-- Literal array expression built from a literal list. -/
private meta def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  let list := xs.foldr
    (fun x rest => mkApp3 (mkConst ``List.cons [Level.zero]) ty x rest) nil
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty list

/-- Literal list expression. -/
private meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x rest => mkApp3 (mkConst ``List.cons [Level.zero]) ty x rest)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- Literal option expression. -/
private meta def optionLit (ty : Expr) : Option Expr → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) ty
  | some value => mkApp2 (mkConst ``Option.some [Level.zero]) ty value

/-- Literal integer polynomial. -/
private meta def zpolyExpr (p : ZPoly) : MetaM Expr :=
  mkAppM ``Hex.DensePoly.ofCoeffs
    #[arrayLit (mkConst ``Int) (p.toArray.toList.map mkIntLit)]

/-- Literal dyadic value. -/
private meta def dyadicExpr (d : Dyadic) : MetaM Expr := do
  let q := d.toRat
  let base ← mkAppM ``Dyadic.ofInt #[mkIntLit q.num]
  if q.den = 1 then return base
  mkAppM ``HShiftRight.hShiftRight #[base, mkIntLit (Int.ofNat q.den.log2)]

/-- Literal dyadic interval with a regenerated kernel proof of endpoint order. -/
private meta def intervalExpr (interval : DyadicInterval) : MetaM Expr := do
  let lower ← dyadicExpr interval.lower
  let upper ← dyadicExpr interval.upper
  let orderTy ← mkAppM ``LT.lt #[lower, upper]
  let order ← mkDecideProof orderTy
  mkAppM ``DyadicInterval.mk #[lower, upper, order]

/-- Literal comparison constructor. -/
private meta def cmpExpr : Cmp → Expr
  | .lt => mkConst ``Cmp.lt
  | .le => mkConst ``Cmp.le
  | .eq => mkConst ``Cmp.eq
  | .ge => mkConst ``Cmp.ge
  | .gt => mkConst ``Cmp.gt
  | .ne => mkConst ``Cmp.ne

/-- Literal atom. -/
private meta def atomExpr (atom : Atom) : MetaM Expr := do
  mkAppM ``Atom.mk #[← zpolyExpr atom.p, cmpExpr atom.cmp]

/-- Literal reflected formula. -/
private meta partial def formulaExpr : Formula → MetaM Expr
  | .atom atom => do mkAppM ``Formula.atom #[← atomExpr atom]
  | .tt => return mkConst ``Formula.tt
  | .ff => return mkConst ``Formula.ff
  | .not formula => do mkAppM ``Formula.not #[← formulaExpr formula]
  | .and left right => do
      mkAppM ``Formula.and #[← formulaExpr left, ← formulaExpr right]
  | .or left right => do
      mkAppM ``Formula.or #[← formulaExpr left, ← formulaExpr right]
  | .imp left right => do
      mkAppM ``Formula.imp #[← formulaExpr left, ← formulaExpr right]

/-- Literal reflected sentence. -/
meta def sentenceExpr : Sentence → MetaM Expr
  | .forallReal formula => do
      mkAppM ``Sentence.forallReal #[← formulaExpr formula]
  | .existsReal formula => do
      mkAppM ``Sentence.existsReal #[← formulaExpr formula]
  | .forallIoc lower upper formula => do
      mkAppM ``Sentence.forallIoc
        #[← dyadicExpr lower, ← dyadicExpr upper, ← formulaExpr formula]
  | .existsIoc lower upper formula => do
      mkAppM ``Sentence.existsIoc
        #[← dyadicExpr lower, ← dyadicExpr upper, ← formulaExpr formula]

/-- Literal generalized Sturm recurrence step. -/
private meta def sturmStepExpr (step : SturmStep) : MetaM Expr := do
  mkAppM ``SturmStep.mk
    #[mkIntLit step.leftScale, ← zpolyExpr step.quotient,
      mkIntLit step.rightScale]

/-- Literal generalized Sturm replay. -/
private meta def sturmReplayExpr (replay : SturmReplay) : MetaM Expr := do
  let chain ← replay.chain.toList.mapM zpolyExpr
  let steps ← replay.steps.toList.mapM sturmStepExpr
  mkAppM ``SturmReplay.mk
    #[arrayLit (mkConst ``ZPoly) chain, mkIntLit replay.derivScale,
      arrayLit (mkConst ``SturmStep) steps]

/-- Literal carrier certificate. -/
private meta def carrierExpr (carrier : CarrierCert) : MetaM Expr := do
  mkAppM ``CarrierCert.mk
    #[← zpolyExpr carrier.carrier, ← zpolyExpr carrier.repeated,
      ← zpolyExpr carrier.derivPart, mkIntLit carrier.factorScale,
      mkIntLit carrier.derivScale, ← sturmReplayExpr carrier.replay]

/-- Literal generalized isolation certificate. -/
private meta def isolationsExpr (isolations : IsolationCert) : MetaM Expr := do
  let intervals ← isolations.intervals.toList.mapM intervalExpr
  mkAppM ``IsolationCert.mk
    #[arrayLit (mkConst ``DyadicInterval) intervals]

/-- Literal common-root certificate. -/
private meta def commonRootExpr (common : CommonRootCert) : MetaM Expr := do
  let replay ← common.replay.mapM sturmReplayExpr
  mkAppM ``CommonRootCert.mk
    #[← zpolyExpr common.gcd, ← zpolyExpr common.atomFactor,
      ← zpolyExpr common.carrierFactor, ← zpolyExpr common.atomCoeff,
      ← zpolyExpr common.carrierCoeff, mkIntLit common.scale,
      optionLit (mkConst ``SturmReplay) replay]

/-- Literal sign-matrix certificate. -/
private meta def signMatrixExpr (signs : SignMatrixCert) : MetaM Expr := do
  let commons ← signs.commonRoots.mapM commonRootExpr
  mkAppM ``SignMatrixCert.mk
    #[listLit (mkConst ``CommonRootCert) commons]

/-- Literal endpoint-order constructor. -/
private meta def rootCmpExpr : Separation.RootCmp → Expr
  | .lt => mkConst ``Separation.RootCmp.lt
  | .eq => mkConst ``Separation.RootCmp.eq
  | .gt => mkConst ``Separation.RootCmp.gt

/-- Literal size-indexed vector whose size proof reduces by reflexivity. -/
private meta def rootCmpVectorExpr {n : Nat}
    (values : Vector Separation.RootCmp n) : MetaM Expr := do
  let data := arrayLit (mkConst ``Separation.RootCmp)
    (values.toArray.toList.map rootCmpExpr)
  let size := mkNatLit n
  let proof ← mkAppM ``Eq.refl #[size]
  mkAppM ``Vector.mk #[data, proof]

/-- Literal bounded endpoint-comparison package. -/
private meta def iocCmpsExpr {n : Nat} (cmps : IocCmps n) : MetaM Expr := do
  mkAppM ``IocCmps.mk
    #[← rootCmpVectorExpr cmps.lower, ← rootCmpVectorExpr cmps.upper]

/-- Literal top-level replay certificate. -/
meta def certificateExpr : Certificate → MetaM Expr
  | .emptyIoc => return mkConst ``Certificate.emptyIoc
  | .constants => return mkConst ``Certificate.constants
  | .noRoots data => do
      let decomp ← mkAppM ``DecompCert.mk
        #[← carrierExpr data.carrier, ← isolationsExpr data.isolations]
      mkAppM ``Certificate.noRoots #[decomp]
  | .cells data => do
      let cmps ← data.iocCmps.mapM iocCmpsExpr
      let cells ← mkAppM ``CellsCert.mk
        #[← carrierExpr data.carrier, ← isolationsExpr data.isolations,
          ← signMatrixExpr data.signs,
          optionLit
            (mkApp (mkConst ``IocCmps) (mkNatLit data.isolations.intervals.size))
            cmps]
      mkAppM ``Certificate.cells #[cells]

/-- Discharge one proposed polynomial evaluation bridge with the kernel ring
normalizer. -/
private meta def proveRing (type : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar type
  let goals ← Lean.Elab.runTactic' goal.mvarId! (← `(tactic| rcf_ring))
  unless goals.isEmpty do
    throwError "rcf: failed to certify the normalized polynomial identity{indentExpr type}"
  instantiateMVars goal

/-- Reify one comparison atom and certify its scaled evaluation identity. -/
private meta def reifyAtom (x source : Expr) (cmp : Cmp)
    (lhs rhs : Expr) : MetaM FormulaResult := do
  let realType := mkConst ``Real
  unless ← isDefEq (← inferType lhs) realType do
    throwError "rcf: comparison operand is not real{indentExpr lhs}"
  unless ← isDefEq (← inferType rhs) realType do
    throwError "rcf: comparison operand is not real{indentExpr rhs}"
  let rational := (← parsePoly x 16 lhs) - (← parsePoly x 16 rhs)
  let (scale, polynomial) := clearPoly rational
  let atom : Atom := { p := polynomial, cmp }
  let polynomialE ← zpolyExpr polynomial
  let atomE ← mkAppM ``Atom.mk #[polynomialE, cmpExpr cmp]
  let formulaE ← mkAppM ``Formula.atom #[atomE]
  let xQ : Q(ℝ) := x
  let lhsQ : Q(ℝ) := lhs
  let rhsQ : Q(ℝ) := rhs
  let polynomialQ : Q(ZPoly) := polynomialE
  let scaleQ : Q(Nat) := mkNatLit scale
  let hevalType : Q(Prop) :=
    q(Polynomial.aeval $xQ (HexPolyZMathlib.toPolynomial $polynomialQ) =
      ($scaleQ : ℝ) * ($lhsQ - $rhsQ))
  let heval ← proveRing hevalType
  let positiveType : Q(Prop) := q(0 < $scaleQ)
  let positive ← mkDecideProof positiveType
  let proof := mkAppN (mkConst ``Atom.toProp_iff_natScale)
    #[polynomialE, cmpExpr cmp, x, lhs, rhs, mkNatLit scale, positive, heval]
  unless ← isDefEq (← inferType proof)
      (← mkAppM ``Iff #[← mkAppM ``Formula.toProp #[formulaE, x], source]) do
    throwError "rcf: internal comparison bridge mismatch"
  return { formula := .atom atom, expr := formulaE, proof := proof }

/-- Reify a Boolean formula under one real bound variable. -/
private meta partial def reifyFormula (x source : Expr) : MetaM FormulaResult := do
  if let some (cmp, lhs, rhs) := comparison? source then
    return ← reifyAtom x source cmp lhs rhs
  let source := source.consumeMData
  match source.getAppFnArgs with
  | (``True, #[]) =>
      let proof := mkApp (mkConst ``Iff.rfl) source
      return { formula := .tt, expr := mkConst ``Formula.tt, proof := proof }
  | (``False, #[]) =>
      let proof := mkApp (mkConst ``Iff.rfl) source
      return { formula := .ff, expr := mkConst ``Formula.ff, proof := proof }
  | (``Not, #[body]) =>
      let result ← reifyFormula x body
      let expr ← mkAppM ``Formula.not #[result.expr]
      let proof ← mkAppM ``not_congr #[result.proof]
      let formula := Formula.not result.formula
      return { formula := formula, expr := expr, proof := proof }
  | (``And, #[left, right]) =>
      let leftResult ← reifyFormula x left
      let rightResult ← reifyFormula x right
      let expr ← mkAppM ``Formula.and #[leftResult.expr, rightResult.expr]
      let proof ← mkAppM ``and_congr #[leftResult.proof, rightResult.proof]
      let formula := Formula.and leftResult.formula rightResult.formula
      return { formula := formula, expr := expr, proof := proof }
  | (``Or, #[left, right]) =>
      let leftResult ← reifyFormula x left
      let rightResult ← reifyFormula x right
      let expr ← mkAppM ``Formula.or #[leftResult.expr, rightResult.expr]
      let proof ← mkAppM ``or_congr #[leftResult.proof, rightResult.proof]
      let formula := Formula.or leftResult.formula rightResult.formula
      return { formula := formula, expr := expr, proof := proof }
  | (``Exists, _) => throwError "rcf: nested quantifiers are unsupported"
  | _ =>
      match source with
      | .forallE _ domain body _ =>
          unless ← isDefEq (← inferType domain) (mkSort Level.zero) do
            throwError "rcf: more than one variable or a nested quantifier is unsupported"
          if body.hasLooseBVar 0 then
            throwError "rcf: more than one variable or a nested quantifier is unsupported"
          let leftResult ← reifyFormula x domain
          let rightResult ← reifyFormula x body
          let expr ← mkAppM ``Formula.imp #[leftResult.expr, rightResult.expr]
          let proof ← mkAppM ``imp_congr #[leftResult.proof, rightResult.proof]
          let formula := Formula.imp leftResult.formula rightResult.formula
          return { formula := formula, expr := expr, proof := proof }
      | _ => throwError "rcf: unsupported proposition in the quantifier body{indentExpr source}"

/-- Runtime and literal forms of a reflected sentence, plus its checked bridge
to the source goal. -/
meta structure SentenceResult where
  sentence : Sentence
  expr : Expr
  proof : Expr

/-- Recognize membership in a standard two-ended interval without unfolding it
to inequalities. -/
private meta def intervalMembership? (x membership : Expr) :
    Option (Name × Expr × Expr) :=
  match membership.consumeMData.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, set, point]) =>
      if point != x then none else
        match set.consumeMData.getAppFnArgs with
        | (kind, #[_, _, a, b]) => some (kind, a, b)
        | _ => none
  | _ => none

/-- Explain the supported rewrites for the two common unsupported interval
conventions. -/
private meta def rejectInterval (kind : Name) (universal : Bool) :
    MetaM SentenceResult := do
  if kind == ``Set.Icc then
    if universal then
      throwError "rcf: Set.Icc quantifiers are unsupported; rewrite
  ∀ x ∈ Set.Icc a b, φ x
as
  (a ≤ b → φ a) ∧ ∀ x ∈ Set.Ioc a b, φ x"
    else
      throwError "rcf: Set.Icc quantifiers are unsupported; rewrite
  ∃ x ∈ Set.Icc a b, φ x
as
  a ≤ b ∧ (φ a ∨ ∃ x ∈ Set.Ioc a b, φ x)"
  else if kind == ``Set.Ioo then
    if universal then
      throwError "rcf: Set.Ioo quantifiers are unsupported; rewrite
  ∀ x ∈ Set.Ioo a b, φ x
as
  ∀ x ∈ Set.Ioc a b, x ≠ b → φ x"
    else
      throwError "rcf: Set.Ioo quantifiers are unsupported; rewrite
  ∃ x ∈ Set.Ioo a b, φ x
as
  ∃ x ∈ Set.Ioc a b, φ x ∧ x ≠ b"
  else
    throwError "rcf: only Set.Ioc bounded quantifiers are supported"

/-- Convert an exact rational endpoint to a dyadic, rejecting every other
denominator instead of approximating it. -/
private meta def ratDyadic (q : Rat) : MetaM Dyadic := do
  let shift := q.den.log2
  unless q.den = 2 ^ shift do
    throwError "rcf: bounded endpoints must be dyadic rationals; got {q}"
  return Dyadic.ofInt q.num >>> (Int.ofNat shift)

/-- Certify that a literal dyadic denotes the source rational real endpoint. -/
private meta def proveEndpoint (dyadicExpr source : Expr) : MetaM Expr := do
  let lhs ← mkAppM ``HexRealRootsMathlib.Dyadic.toReal #[dyadicExpr]
  let type ← mkAppM ``Eq #[lhs, source]
  let goal ← mkFreshExprMVar type
  let goals ← Lean.Elab.runTactic' goal.mvarId!
    (← `(tactic|
      (simp only [HexRealRootsMathlib.toReal_ofInt,
          HexRealRootsMathlib.toReal_ofInt_shiftRight] <;>
       push_cast <;>
       norm_num)))
  unless goals.isEmpty do
    throwError "rcf: failed to certify a dyadic endpoint{indentExpr source}"
  instantiateMVars goal

/-- Check the final sentence bridge before returning it to the tactic. -/
private meta def finishSentence (source : Expr) (sentence : Sentence)
    (expr proof : Expr) : MetaM SentenceResult := do
  let reflected ← mkAppM ``Sentence.toProp #[expr]
  let expected ← mkAppM ``Iff #[reflected, source]
  unless ← isDefEq (← inferType proof) expected do
    throwError "rcf: internal quantified-sentence bridge mismatch"
  return { sentence, expr, proof }

/-- Reify a universal sentence, preferring the exact `Set.Ioc` shape before
treating implication as an ordinary Boolean connective. -/
private meta def reifyForall (source domain body : Expr) : MetaM SentenceResult := do
  unless ← isDefEq domain (mkConst ``Real) do
    throwError "rcf: the quantified variable must have type Real"
  withLocalDeclD `x domain fun x => do
    let instantiated := body.instantiate1 x
    if let .forallE _ membership consequent _ := instantiated.consumeMData then
      if !consequent.hasLooseBVar 0 then
        if let some (kind, aSource, bSource) := intervalMembership? x membership then
          unless kind == ``Set.Ioc do
            return ← rejectInterval kind true
          let aValue ← ratDyadic (← scalarRat aSource)
          let bValue ← ratDyadic (← scalarRat bSource)
          let aExpr ← dyadicExpr aValue
          let bExpr ← dyadicExpr bValue
          let formula ← reifyFormula x consequent
          let sentence := Sentence.forallIoc aValue bValue formula.formula
          let expr ← mkAppM ``Sentence.forallIoc #[aExpr, bExpr, formula.expr]
          let ha ← proveEndpoint aExpr aSource
          let hb ← proveEndpoint bExpr bSource
          let bridge ← mkLambdaFVars #[x] formula.proof
          let predicate ← mkLambdaFVars #[x] consequent
          let proof := mkAppN (mkConst ``Sentence.forallIoc_iff)
            #[aExpr, bExpr, aSource, bSource, formula.expr, predicate,
              ha, hb, bridge]
          return ← finishSentence source sentence expr proof
    let formula ← reifyFormula x instantiated
    let sentence := Sentence.forallReal formula.formula
    let expr ← mkAppM ``Sentence.forallReal #[formula.expr]
    let bridge ← mkLambdaFVars #[x] formula.proof
    let predicate ← mkLambdaFVars #[x] instantiated
    let proof := mkAppN (mkConst ``Sentence.forallReal_iff)
      #[formula.expr, predicate, bridge]
    finishSentence source sentence expr proof

/-- Reify an existential sentence, recognizing an `Ioc` membership conjunct
before the quantifier-free body. -/
private meta def reifyExists (source domain predicate : Expr) : MetaM SentenceResult := do
  unless ← isDefEq domain (mkConst ``Real) do
    throwError "rcf: the quantified variable must have type Real"
  let .lam _ binderType body _ := predicate.consumeMData
    | throwError "rcf: malformed existential predicate"
  unless ← isDefEq binderType domain do
    throwError "rcf: malformed existential binder"
  withLocalDeclD `x domain fun x => do
    let instantiated := body.instantiate1 x
    if let (``And, #[membership, consequent]) :=
        instantiated.consumeMData.getAppFnArgs then
      if let some (kind, aSource, bSource) := intervalMembership? x membership then
        unless kind == ``Set.Ioc do
          return ← rejectInterval kind false
        let aValue ← ratDyadic (← scalarRat aSource)
        let bValue ← ratDyadic (← scalarRat bSource)
        let aExpr ← dyadicExpr aValue
        let bExpr ← dyadicExpr bValue
        let formula ← reifyFormula x consequent
        let sentence := Sentence.existsIoc aValue bValue formula.formula
        let expr ← mkAppM ``Sentence.existsIoc #[aExpr, bExpr, formula.expr]
        let ha ← proveEndpoint aExpr aSource
        let hb ← proveEndpoint bExpr bSource
        let bridge ← mkLambdaFVars #[x] formula.proof
        let predicate ← mkLambdaFVars #[x] consequent
        let proof := mkAppN (mkConst ``Sentence.existsIoc_iff)
          #[aExpr, bExpr, aSource, bSource, formula.expr, predicate,
            ha, hb, bridge]
        return ← finishSentence source sentence expr proof
    let formula ← reifyFormula x instantiated
    let sentence := Sentence.existsReal formula.formula
    let expr ← mkAppM ``Sentence.existsReal #[formula.expr]
    let bridge ← mkLambdaFVars #[x] formula.proof
    let predicateExpr ← mkLambdaFVars #[x] instantiated
    let proof := mkAppN (mkConst ``Sentence.existsReal_iff)
      #[formula.expr, predicateExpr, bridge]
    finishSentence source sentence expr proof

/-- Reify one supported, singly quantified real sentence. -/
meta def reifySentence (source : Expr) : MetaM SentenceResult := do
  let source := source.consumeMData
  match source with
  | .forallE _ domain body _ => reifyForall source domain body
  | _ =>
      match source.getAppFnArgs with
      | (``Exists, #[domain, predicate]) => reifyExists source domain predicate
      | _ => throwError "rcf: expected one universal or existential real quantifier"

end Reify

end Hex.RCF
