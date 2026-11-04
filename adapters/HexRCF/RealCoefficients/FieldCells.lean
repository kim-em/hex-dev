/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.FieldIsolation
public import HexRCF.RealCoefficients.RepresentationCarrier

public section

namespace Hex.RCF.RealCoefficients.FieldRootSigns
open Hex Hex.RealFormula

namespace Table

/-- Bind the complete ordered row inventory and validate every retained row,
including repeated atoms. Unused or corrupt duplicate rows cannot hide behind
a previous matching row. -/
@[expose] def checkRows {E : Type u} {Ctx : Type v} {n roots : Nat}
    [Zero E] [DecidableEq E] (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool) : Bool :=
  Decidable.decide (table.entries.map (fun row => row.atom) = formula.polys) &&
    table.entries.all fun row => (List.finRange roots).all fun i => accept row.atom i row.evidence[i]

/-- Complete checked rows supply the existing source-atom lookup interface. -/
theorem checkRows_checked {E : Type u} {Ctx : Type v} {n roots : Nat}
    [Zero E] [DecidableEq E] (table : Table E Ctx n roots) (formula : QF n)
    (accept : RealFormula.Poly n → Fin roots → TarskiCertificate E E Ctx → Bool)
    (accepted : table.checkRows formula accept = true) : table.checkWith formula accept = true := by
  simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at accepted
  unfold checkWith
  apply List.all_eq_true.mpr
  intro atom member
  cases found : table.entries.find? (sameAtom atom) with
  | none =>
      have listed : atom ∈ table.entries.map (fun row => row.atom) := by
        rw [accepted.1]
        exact member
      obtain ⟨row, rowMember, equality⟩ := List.mem_map.mp listed
      have absent := List.find?_eq_none.mp found row rowMember
      simp [sameAtom, equality] at absent
  | some row =>
      have matched : row.atom = atom := by
        simpa [sameAtom] using List.find?_some found
      simpa only [matched] using
        List.all_eq_true.mp accepted.2 row (List.mem_of_find?_eq_some found)

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx] {n roots : Nat}
local notation "K" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Validate the existing root rows with finite sign coverage and semantic
degree guards. The original atom and interval are independently supplied. -/
@[expose] def checkTransport (table : Table K Ctx n roots)
    (signs : LiteralSign.Table K) (context : Ctx) (head : DensePoly K)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly K) (formula : QF n) : Bool :=
  table.checkRows formula fun atom i cert =>
    let interval := intervals[i]
    FieldQuery.check signs context head (query atom)
      (.finite (PolyQuot.ofRat interval.lower.toRat))
      (.finite (PolyQuot.ofRat interval.upper.toRat)) cert.value cert

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
  have checked := table.query_checkedWith formula _
    (table.checkRows_checked formula _ accepted) i atom member fallback
  change FieldQuery.check signs context head (query atom) _ _
    (table.value fallback i atom) (table.evidence fallback i atom) = true at checked
  have real := FieldTransport.real signs header
  have point (d : Dyadic) :
      Field.value (Field.literalRep p s hw hp) (PolyQuot.ofRat d.toRat : K) =
        HexRealRootsTheory.Dyadic.toReal d := by
    simpa only [HexRealRootsTheory.toReal_eq_cast_toRat] using
      FieldSpecialize.value_ofRat (Field.literalRep p s hw hp)
        (Field.literalRep_mk p s hw hp) real d.toRat
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
@[expose] def check (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  Field.checkSignTable p s hw hp signs &&
    formula.polys.all (fun atom => FieldTransport.leadingCheck signs (query atom)) &&
    radical.check context (RepresentationCarrier.product (formula.polys.map query)) &&
    FieldIsolation.check signs context radical.core cert &&
    rows.checkTransport signs context radical.core cert.isolations.intervals.toVector query formula &&
    FieldQuery.covered signs (SignInputs.openSamples FieldDecision.point cert
      (formula.polys.map query))

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
  simp only [check, Bool.and_eq_true] at accepted
  exact accepted.1.1.1.1.1

/-- Acceptance certifies each original atom's semantic degree, including
literal zero atoms and leading cancellation in the shared specialization. -/
theorem degrees (signs : LiteralSign.Table E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (accepted : check signs context query formula radical cert rows = true)
    (atom : RealFormula.Poly n) (member : atom ∈ formula.polys) :
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) (query atom))).natDegree =
        (query atom).natDegree := by
  have header := signs_checked signs context query formula radical cert rows accepted
  have real := FieldTransport.real signs header
  have zero := Field.value_zero (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp) real
  simp only [check, Bool.and_eq_true] at accepted
  have guard := List.all_eq_true.mp accepted.1.1.1.1.2 atom member
  rw [natDegree_interpret (fun x : ℝ => x) (fun _ => Iff.rfl)]
  exact Transport.polynomial_degree _ zero _ (FieldTransport.leading signs header _ guard)

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
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨⟨header, _⟩, radicalChecked⟩, isolationChecked⟩, rowsChecked⟩, samples⟩ := accepted
  let rep := Field.literalRep p s hw hp
  let read : E → ℝ := Field.value rep
  have same := Field.literalRep_mk p s hw hp
  have real := FieldTransport.real signs header
  have h0 : read 0 = 0 := Field.value_zero rep same real
  have h1 : read 1 = 1 := Field.value_one rep same real
  have ha : ∀ a b, read (a + b) = read a + read b := Field.value_add rep same real
  have hs : ∀ a b, read (a - b) = read a - read b := Field.value_sub rep same real
  have hm : ∀ a b, read (a * b) = read a * read b := Field.value_mul rep same real
  have point (d : Dyadic) : read (FieldDecision.point d) = HexRealRootsTheory.Dyadic.toReal d := by
    simpa only [read, rep, FieldDecision.point, HexRealRootsTheory.toReal_eq_cast_toRat] using
      FieldSpecialize.value_ofRat rep same real d.toRat
  have coverage : ∀ atom ∈ formula.polys,
      interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (Transport.polynomial read (query atom)) = 0 ∨
      ∀ x, (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read (query atom))).IsRoot x →
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read radical.core)).IsRoot x := by
    intro atom member
    rcases RepresentationCarrier.atom_roots_transport read h0 h1 ha hm
        (formula.polys.map query) (query atom) (List.mem_map.mpr ⟨atom, member, rfl⟩) with
      zero | roots
    · exact Or.inl zero
    · right
      intro x root
      exact (radical.roots_transport read h0 h1 ha hs hm context _ radicalChecked x).mpr
        (roots x root)
  have queries : ∀ i atom, atom ∈ formula.polys →
      Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
        (Transport.polynomial read radical.core) (Transport.polynomial read (query atom))
        (.finite (HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].lower))
        (.finite (HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].upper))
        (rows.value cert.total i atom)
        (Transport.query read id (rows.evidence cert.total i atom)) = true := by
    intro i atom member
    simpa [read, rep] using rows.query_transport signs header context radical.core
      cert.isolations.intervals.toVector query formula rowsChecked i atom member cert.total
  have semantics := Decision.cellSign_spec (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x : ℝ => (SignType.sign x : Int)) (fun _ => rfl)
    HexRealRootsTheory.Dyadic.toReal (fun _ => rfl) formula valuation
    (fun atom => Transport.polynomial read (query atom)) atom_eval context
    (Transport.polynomial read radical.core) (FieldIsolation.map cert)
    (FieldIsolation.checked signs header context radical.core cert isolationChecked)
    coverage (rows.value cert.total)
    (fun i atom => Transport.query read id (rows.evidence cert.total i atom)) queries
  obtain ⟨roots, ordered, semantics⟩ := semantics
  refine ⟨roots, ordered, ?_⟩
  intro cell x region atom member
  obtain ⟨observed, observedEq, meaning⟩ := semantics cell x region atom member
  refine ⟨observed, ?_, meaning⟩
  rw [← observedEq]
  cases cell with
  | root i => rfl
  | «open» cut =>
    let d := cert.isolations.openPoint cut
    let key := (query atom).eval (FieldDecision.point d)
    have sample : key ∈ SignInputs.openSamples FieldDecision.point cert (formula.polys.map query) := by
      apply List.mem_flatMap.mpr
      refine ⟨Cell.open cut, Array.mem_toList_iff.mpr (Cell.mem_all _), ?_⟩
      exact List.mem_map.mpr ⟨query atom, List.mem_map.mpr ⟨atom, member, rfl⟩, rfl⟩
    have sign := (FieldQuery.cached_eq signs _ samples key sample read).trans
      (Field.checkSignTable_spec p s hw hp signs header key)
    have evaluation := Transport.Ring.polynomial_eval read h0 (query atom) (FieldDecision.point d)
      (fun _ _ => hm _ _) (fun _ _ => ha _ _)
    rw [point] at evaluation
    change some (Sign.ofInt (FieldQuery.cached signs key)) =
      some (Sign.ofInt ((SignType.sign ((Transport.polynomial read (query atom)).eval
        (HexRealRootsTheory.Dyadic.toReal d)) : Int)))
    rw [sign]
    change some (Sign.ofInt ((SignType.sign (read ((query atom).eval
      (FieldDecision.point d))) : Int))) = _
    rw [evaluation]

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
