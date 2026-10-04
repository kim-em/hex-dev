/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldBuild
public import HexRCF.RealCoefficients.FieldSignProgress

public section

/-! Finite frontend search budgets. Accepted evidence still goes through literal replay. -/
namespace Hex.RCF.RealCoefficients.FieldBuild

/-- Search exhaustion and invalid construction are distinct terminal outcomes. -/
inductive BuildError where
  | exhausted
  | invalidReplay
  deriving DecidableEq, Repr

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- Bounded interval refinement with cached selected-field root solving.
The direct proposal and final accepted replay are each built once. A rejected
replay is terminal; only absence of a direct proposal starts fixed-field root search. -/
def isolateWithin [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (sign : PolyQuot p root → Int) (context : Ctx)
    (head : DensePoly (PolyQuot p root)) (depth doublings : Nat) :
    Except BuildError (IsolationReplay (PolyQuot p root) Ctx) :=
  let replay (intervals : IsolationCert) :=
    match IsolationReplay.build sign FieldDecision.point context head intervals with
    | some cert => Except.ok cert
    | none => Except.error BuildError.invalidReplay
  match FieldIsolate.propose? sign FieldDecision.point head depth with
  | some intervals => replay intervals
  | none =>
    if doublings = 0 then .error .exhausted else
    -- Reuse the existing field coordinates instead of reconstructing a common
    -- field from separately converted coefficients.
    let roots := roots? rep hrep head
    let rec refine : Nat → Nat → Except BuildError IsolationCert
      | 0, _ => .error .exhausted
      | fuel + 1, precision =>
        match roots with
        | none => .error .invalidReplay
        | some roots =>
          match roots.mapM (fun r => rootInterval r.root precision) with
          | none => .error .invalidReplay
          | some intervals =>
            let cert : IsolationCert := ⟨intervals⟩
            if cert.checkGaps then .ok cert else refine fuel (2 * precision)
    match refine doublings 1 with
    | .error error => .error error
    | .ok intervals => replay intervals

/-- Frontend production with explicit finite search resources. The complete
`produce` API remains separate; the tactic uses this bounded path and reports
exhaustion without dispatching another handler. The raw default preserves the
existing direct-call behavior; the tactic explicitly passes its `monicCore`
option, whose default is true. Neither path enters quotation. -/
def produceWithin [RealAlgebraicNumber.Laws] (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] (real : s.meetsRealAxis = true)
    {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (depth doublings : Nat)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := [])
    (monicCore : Bool := false) :
    Except BuildError (Result p s hw hp Ctx (n + 1)) := do
  let prepared := Field.prepareSign p s hw hp real
  let sign := fun a : PolyQuot p (SimpleRoot.ofSquare p s hw hp) =>
    Sturm.queryPrepared prepared.val a.coeffs
  let rep := Field.literalRep p s hw hp
  let hrep := Field.literalRep_mk p s hw hp
  let product := FieldCarrier.product values formula
  let proposal := if monicCore then RadicalCert.buildMonic context product
    else RadicalCert.build context product
  let some radical := proposal |
    .error .invalidReplay
  let isolation ← isolateWithin rep hrep sign context radical.core depth doublings
  let some rootSigns := FieldRootSigns.Table.build sign FieldDecision.point
      context radical.core isolation (FieldSpecialize.literalPolynomial values) formula |
    .error .invalidReplay
  let keys := signKeys values formula radical.core isolation rootSigns extraSignKeys
  let some signs := buildTable p s hw hp keys | .error .invalidReplay
  return ⟨radical, isolation, rootSigns, signs⟩

end Hex.RCF.RealCoefficients.FieldBuild
