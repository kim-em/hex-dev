/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.FieldIsolation
public import HexRCF.RealCoefficients.RepresentationCarrier
public import HexRCF.RealCoefficients.QueryCells

public section

namespace Hex.RCF.RealCoefficients.FieldRootSigns
open Hex Hex.RealFormula

namespace Table

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx] {n roots : Nat}
local notation "K" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Validate the existing root rows with finite sign coverage and semantic
degree guards. The original atom and interval are independently supplied. -/
@[expose] def checkTransportWith (table : Table K Ctx n roots)
    (lookup : K → Option Int) (context : Ctx) (head : DensePoly K)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly K) (formula : QF n) : Bool :=
  table.checkRows formula fun atom i cert =>
    let interval := intervals[i]
    FieldQuery.checkWith lookup context head (query atom)
      (.finite (PolyQuot.ofRat interval.lower.toRat))
      (.finite (PolyQuot.ofRat interval.upper.toRat)) cert.value cert

@[expose] def checkTransport (table : Table K Ctx n roots)
    (signs : LiteralSign.Table K) (context : Ctx) (head : DensePoly K)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly K) (formula : QF n) : Bool :=
  table.checkTransportWith signs.lookup? context head intervals query formula

/-- Every accepted row gives the corresponding real query, retaining its
source atom, selected interval and claimed sign. No common-field
irreducibility theorem or sign/root producer is used. -/
theorem query_transport (table : Table K Ctx n roots)
    (signs : LiteralSign.Table K)
    (header : Field.checkSignTable p s hw hp signs = true) (context : Ctx) (head : DensePoly K)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly K) (formula : QF n)
    (accepted : table.checkTransport signs context head intervals query formula = true)
    (i : Fin roots) (atom : RealFormula.Poly n) (member : atom ∈ formula.polys)
    (fallback : TarskiCertificate K K Ctx) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Hex.RealClosure.Transport.polynomial (Field.value (Field.literalRep p s hw hp)) head)
      (Hex.RealClosure.Transport.polynomial (Field.value (Field.literalRep p s hw hp))
        (query atom))
      (.finite (HexRealRootsTheory.Dyadic.toReal intervals[i].lower))
      (.finite (HexRealRootsTheory.Dyadic.toReal intervals[i].upper))
      (table.value fallback i atom)
      (Hex.RealClosure.Transport.query (Field.value (Field.literalRep p s hw hp)) id
        (table.evidence fallback i atom)) = true := by
  unfold checkTransport checkTransportWith at accepted
  have checked := table.query_checkedWith formula _
    (table.checkRows_checked formula _ accepted) i atom member fallback
  change FieldQuery.check signs context head (query atom) _ _
    (table.value fallback i atom) (table.evidence fallback i atom) = true at checked
  have point := FieldTransport.point signs header
  simpa only [Hex.RealClosure.Transport.endpoint, point] using
    FieldQuery.checked signs header context head (query atom) _ _
      (table.value fallback i atom) (table.evidence fallback i atom) checked

end Table
end Hex.RCF.RealCoefficients.FieldRootSigns

namespace Hex.RCF.RealCoefficients.FieldCells
open Hex Hex.RealFormula Hex.RealClosure HexPolyTheory.Interpret

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx] {n : Nat}
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Validate all evidence before the Boolean fold, including every atom and
ordinary sector sample. No numerical producer is called during this check. -/
@[expose] def checkWith (signs : LiteralSign.Table E) (lookup : E → Option Int) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  Field.checkSignTable p s hw hp signs &&
    QueryCells.check lookup FieldDecision.point context query formula radical cert rows

@[expose] def check (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  checkWith signs signs.lookup? context query formula radical cert rows

/-- Finite signs needed by the supplied isolations, root queries and ordinary
samples. Source identities and original divisors are added by the caller. -/
@[expose] def keys (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : List E :=
  formula.polys.map (fun atom => (query atom).coeff ((query atom).size - 1)) ++
    FieldIsolation.keys head cert ++
    rows.entries.flatMap (fun row =>
      (List.finRange cert.isolations.intervals.size).flatMap fun i =>
        let interval := cert.isolations.intervals[i]
        FieldQuery.keys head (.finite (PolyQuot.ofRat interval.lower.toRat))
          (.finite (PolyQuot.ofRat interval.upper.toRat)) row.evidence[i]) ++
    SignInputs.openSamples FieldDecision.point cert (formula.polys.map query)

/-- Accepted evidence authenticates the finite sign table independently of
whether the strict formula fold returns true or false. -/
theorem signs_checked (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (accepted : check signs context query formula radical cert rows = true) :
    Field.checkSignTable p s hw hp signs = true := by
  exact (Bool.and_eq_true_iff.mp accepted).1

/-- Acceptance certifies each original atom's semantic degree, including
literal zero atoms and structural cancellation in the shared specialization. -/
theorem degrees (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (accepted : check signs context query formula radical cert rows = true)
    (atom : RealFormula.Poly n) (member : atom ∈ formula.polys) :
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) (query atom))).natDegree =
        (query atom).natDegree := by
  have parts := Bool.and_eq_true_iff.mp accepted
  let rep := Field.literalRep p s hw hp
  exact QueryCells.degrees signs.lookup? (Field.value rep)
    (FieldTransport.closed rep (Field.literalRep_mk p s hw hp) (FieldTransport.real signs parts.1))
    (fun x value hit => Field.checkSignTable_lookup p s hw hp signs parts.1 x value hit)
    FieldDecision.point context query formula radical cert rows parts.2 atom member

/-- The shared grouped compiler has the exact source meaning at the fixed
selected embedding. No common-field irreducibility proof is needed. -/
theorem specialize (signs : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp signs = true)
    (values : Fin m → E) (atom : RealFormula.Poly (m + 1)) (x : ℝ) :
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp))
        (RepresentationSpecialize.polynomial values atom))).eval x =
          atom.eval (append (fun j => Field.value (Field.literalRep p s hw hp) (values j)) x) := by
  have real := FieldTransport.real signs checked
  exact RepresentationSpecialize.map_eval (Field.value (Field.literalRep p s hw hp))
    (Field.value_one _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_add _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_mul _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_natCast _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_neg _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_zero _ (Field.literalRep_mk p s hw hp) real) values atom x

/-- Successful finite replay determines every source atom throughout every
real cell. Coverage, degree guards and all signs are checked conclusions;
`atom_eval` is the specialization law for the independently supplied compiler. -/
theorem cells (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) (query atom))).eval x =
          atom.eval (valuation x))
    (accepted : check signs context query formula radical cert rows = true) :
    ∃ roots : Fin cert.isolations.intervals.size → ℝ,
      StrictMono roots ∧ ∀ cell x, Cell.Region roots cell x →
        ∀ atom ∈ formula.polys, ∃ observed,
          Decision.cellSign (FieldQuery.cached signs) FieldDecision.point query cert
            (rows.value cert.total) cell atom = some observed ∧
          SignType.sign (((observed.toInt : Int) : ℝ)) = SignType.sign (atom.eval (valuation x)) := by
  have parts := Bool.and_eq_true_iff.mp accepted
  let rep := Field.literalRep p s hw hp
  exact QueryCells.cells signs.lookup? (Field.value rep)
    (FieldTransport.closed rep (Field.literalRep_mk p s hw hp) (FieldTransport.real signs parts.1))
    (fun x value hit => Field.checkSignTable_lookup p s hw hp signs parts.1 x value hit)
    FieldDecision.point (FieldTransport.point signs parts.1) context query formula radical cert rows
    valuation atom_eval parts.2

/-- The strict universal fold covers the whole real line. -/
theorem forall_formula (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) (query atom))).eval x =
          atom.eval (valuation x))
    (accepted : check signs context query formula radical cert rows = true) :
    OptionFold.allArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (Decision.cellSign (FieldQuery.cached signs)
        FieldDecision.point query cert (rows.value cert.total) cell)) = some true ↔
      ∀ x, formula.toProp (valuation x) := by
  obtain ⟨roots, ordered, meanings⟩ := cells signs context query formula radical cert rows
    valuation atom_eval accepted
  exact RealCoefficients.forall_formula roots ordered formula valuation _ meanings

/-- Existential truth has an ordinary real point in a checked section or sector. -/
theorem exists_formula (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) (query atom))).eval x =
          atom.eval (valuation x))
    (accepted : check signs context query formula radical cert rows = true) :
    OptionFold.anyArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (Decision.cellSign (FieldQuery.cached signs)
        FieldDecision.point query cert (rows.value cert.total) cell)) = some true ↔
      ∃ x, formula.toProp (valuation x) := by
  obtain ⟨roots, ordered, meanings⟩ := cells signs context query formula radical cert rows
    valuation atom_eval accepted
  exact RealCoefficients.exists_formula roots ordered formula valuation _ meanings


end Hex.RCF.RealCoefficients.FieldCells
