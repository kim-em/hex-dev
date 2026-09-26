/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldDecision
public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.RadicalBuild
public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.FieldReplay
public import HexRCF.RealCoefficients.SignInputs

public section

/-! Propose fixed-field root isolations using the existing algebraic root solver. -/

namespace Hex.RCF.RealCoefficients.FieldBuild

open Hex

variable {p : ZPoly} {root : SimpleRoot p} [ZPoly.CheckedIrreducible p]

/-- Convert one fixed-field coordinate to its canonical real value for search.
The resulting isolations are checked later over the original coordinates. -/
@[expose] def canonical? (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (a : PolyQuot p root) :
    Option RealAlgebraicNumber := do
  let algebraic ← a.toAlgebraicNumber? rep hrep
  RealAlgebraicNumber.ofAlgebraic? algebraic

/-- Search for roots with the existing canonical solver, retaining only its
dyadic interval proposals. -/
@[expose] def proposeIsolations [RealAlgebraicNumber.Laws]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (head : DensePoly (PolyQuot p root)) (precision : Nat) :
    Option IsolationCert := do
  let coefficients ← head.toArray.mapM (canonical? rep hrep)
  let roots ← (RealAlgebraicPoly.ofArray coefficients).roots.finite?
  let intervals ← roots.mapM fun r => rootInterval r.root precision
  return ⟨intervals⟩

/-- A search-only sign oracle. An unsuccessful canonical conversion makes the
proposal fail its subsequent exact replay checks. -/
@[expose] def proposalSign (rep : RefinedIsolation p)
    (hrep : SimpleRoot.mk rep = root) (a : PolyQuot p root) : Int :=
  (canonical? rep hrep a).map RealAlgebraicNumber.sign |>.getD 0

/-- Search and certify root cells over the original fixed-field coefficients.
The result contains the original literal Tarski evidence, not canonical data. -/
def isolateAt [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (context : Ctx) (head : DensePoly (PolyQuot p root))
    (precision : Nat) : Option (IsolationReplay (PolyQuot p root) Ctx) :=
  match proposeIsolations rep hrep head precision with
  | none => none
  | some isolations =>
      IsolationReplay.build (proposalSign rep hrep) FieldDecision.point context head isolations

/-- Every successful proposal is accepted by the generic isolation checker
with the same root, field coordinates and sign operation. -/
theorem isolateAt_checked [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (rep : RefinedIsolation p) (hrep : SimpleRoot.mk rep = root)
    (context : Ctx) (head : DensePoly (PolyQuot p root))
    (precision : Nat) (cert : IsolationReplay (PolyQuot p root) Ctx)
    (h : isolateAt rep hrep context head precision = some cert) :
    cert.check (proposalSign rep hrep) FieldDecision.point context head = true := by
  unfold isolateAt at h
  split at h
  · contradiction
  · exact (IsolationReplay.build_checked _ _ _ _ _ _ h).2

/-- Prepare the rational defining polynomial once and certify the finite sign
arguments that replay will read. The selected square fixes the root and both
open rational endpoints. -/
def buildTable (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (keys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp))) :
    Option (LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp))) := do
  let table ← LiteralSign.Table.build (ZPoly.toRatPoly p)
    (s.re - s.radiusHi).toRat (s.re + s.radiusHi).toRat keys PolyQuot.coeffs
  if Field.checkSignTable p s hw hp table then some table else none

/-- A produced table passes the full literal-context binding check. -/
theorem buildTable_checked (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (keys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (table : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (h : buildTable p s hw hp keys = some table) :
    Field.checkSignTable p s hw hp table = true := by
  unfold buildTable at h
  simp only [bind, Option.bind] at h
  split at h
  · simp at h
  · next table htable =>
      dsimp only at h
      split at h
      · next hc =>
          cases Option.some.inj h
          exact hc
      · simp at h

/-- Literal evidence produced over one fixed coordinate field. The final
Boolean checks are replayed using the finite rational sign table, rather than
assuming the search oracle's signs. -/
structure Result (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    (Ctx : Type u) (n : Nat) where
  radical : RadicalCert (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) Ctx
  isolation : IsolationReplay (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) Ctx
  rootSigns : FieldRootSigns.Table
    (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) Ctx n isolation.isolations.intervals.size
  signs : LiteralSign.Table (PolyQuot p (SimpleRoot.ofSquare p s hw hp))

/-- Build all literal field evidence. Finite sign keys come from the exact
arguments read by the checked isolation and root-query certificates. -/
def build [RealAlgebraicNumber.Laws] (p : ZPoly) (s : DyadicSquare)
    (hw : atomWitness p s) (hp : (mahlerPrec p : Int) ≤ s.prec)
    [ZPoly.CheckedIrreducible p] {Ctx : Type u} [DecidableEq Ctx]
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx) (precision : Nat) :
    Option (Result p s hw hp Ctx (n + 1)) :=
  let rep := Field.literalRep p s hw hp
  let hrep := Field.literalRep_mk p s hw hp
  let product := FieldCarrier.product values formula
  match RadicalCert.build context product with
  | none => none
  | some radical =>
    match isolateAt rep hrep context radical.core precision with
    | none => none
    | some isolation =>
      match FieldRootSigns.Table.build (proposalSign rep hrep) FieldDecision.point
          context radical.core isolation
          (FieldSpecialize.literalPolynomial values) formula with
      | none => none
      | some rootSigns =>
        let keys :=
          SignInputs.isolation FieldDecision.point radical.core isolation ++
          SignInputs.rootQueries FieldDecision.point radical.core isolation
            (rootSigns.entries.map fun row i => row.evidence[i]) ++
          SignInputs.openSamples FieldDecision.point isolation
            (formula.polys.map (FieldSpecialize.literalPolynomial values))
        match buildTable p s hw hp keys with
        | none => none
        | some signs => some ⟨radical, isolation, rootSigns, signs⟩

namespace Result

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable [ZPoly.CheckedIrreducible p] {Ctx : Type u} [DecidableEq Ctx]

/-- Literal finite signs, with the semantic fallback used only outside the
finite key set. -/
@[expose] noncomputable def sign (data : Result p s hw hp Ctx n)
    (a : PolyQuot p (SimpleRoot.ofSquare p s hw hp)) : Int :=
  data.signs.sign (Field.value (Field.literalRep p s hw hp)) a

@[expose] noncomputable def checkForall (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx) : Bool :=
  Field.checkSignTable p s hw hp data.signs &&
    data.radical.check context (FieldCarrier.product values formula) &&
    data.isolation.check data.sign FieldDecision.point context data.radical.core &&
    data.rootSigns.check data.sign FieldDecision.point context data.radical.core
      (FieldReplay.intervals data.isolation)
      (FieldSpecialize.literalPolynomial values) formula &&
    OptionFold.allArray (Cell.all data.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign data.sign values data.isolation
          (data.rootSigns.value data.isolation.total) cell)) == some true

/-- A true checked universal verdict proves the original fixed-field formula
at every real argument. The producer's canonical search is absent from the
proof term. -/
theorem checkForall_sound (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (h : data.checkForall values formula context = true) :
    ∀ x, formula.toProp
      (RealFormula.append (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x) := by
  simp only [checkForall, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨htable, hradical⟩, hisolation⟩, hroots⟩, hcells⟩ := h
  have hreal : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at htable
    exact htable.1.2
  exact (FieldReplay.forall_formula
    (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp)
    (Field.literalRep_real p s hw hp hreal)
    data.sign (Field.checkSignTable_spec p s hw hp data.signs htable)
    values formula context data.radical hradical data.isolation hisolation
    data.rootSigns hroots).mp hcells

@[expose] noncomputable def checkExists (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx) : Bool :=
  Field.checkSignTable p s hw hp data.signs &&
    data.radical.check context (FieldCarrier.product values formula) &&
    data.isolation.check data.sign FieldDecision.point context data.radical.core &&
    data.rootSigns.check data.sign FieldDecision.point context data.radical.core
      (FieldReplay.intervals data.isolation)
      (FieldSpecialize.literalPolynomial values) formula &&
    OptionFold.anyArray (Cell.all data.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns
        (FieldDecision.cellSign data.sign values data.isolation
          (data.rootSigns.value data.isolation.total) cell)) == some true

/-- A true checked existential verdict proves the original fixed-field
formula has a real witness. -/
theorem checkExists_sound (data : Result p s hw hp Ctx (n + 1))
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (context : Ctx)
    (h : data.checkExists values formula context = true) :
    ∃ x, formula.toProp
      (RealFormula.append (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x) := by
  simp only [checkExists, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨htable, hradical⟩, hisolation⟩, hroots⟩, hcells⟩ := h
  have hreal : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at htable
    exact htable.1.2
  exact (FieldReplay.exists_formula
    (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp)
    (Field.literalRep_real p s hw hp hreal)
    data.sign (Field.checkSignTable_spec p s hw hp data.signs htable)
    values formula context data.radical hradical data.isolation hisolation
    data.rootSigns hroots).mp hcells

end Result

end Hex.RCF.RealCoefficients.FieldBuild
