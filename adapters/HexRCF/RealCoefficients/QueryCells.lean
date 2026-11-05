/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.IsolationTransport
public import HexRCF.RealCoefficients.RepresentationCarrier
public section

namespace Hex.RCF.RealCoefficients.QueryCells
open Hex Hex.RealFormula Hex.RealClosure HexPolyTheory.Interpret

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Bind every original row and check its sign at the same isolated root.
Repeated atom occurrences remain in the checked inventory. -/
@[expose] def checkRows (lookup : E → Option Int) (point : Dyadic → E)
    (context : Ctx) (head : DensePoly E) (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (rows : FieldRootSigns.Table E Ctx n roots) : Bool :=
  rows.checkRows formula fun atom i cert =>
    let interval := intervals[i]
    QueryReplay.check lookup context head (query atom)
      (.finite (point interval.lower)) (.finite (point interval.upper)) cert.value cert

/-- Complete finite cell checking over stored coefficients with ordinary
arithmetic. Coefficient evidence is authenticated by the caller; no field,
inverse, global zero reflection or numerical search is required here. -/
@[expose] def check (lookup : E → Option Int) (point : Dyadic → E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  formula.polys.all (fun atom => QueryReplay.leading lookup (query atom)) &&
    radical.check context (RepresentationCarrier.product (formula.polys.map query)) &&
    IsolationTransport.check lookup point context radical.core cert &&
    checkRows lookup point context radical.core cert.isolations.intervals.toVector query formula rows &&
    QueryReplay.covered lookup (SignInputs.openSamples point cert (formula.polys.map query))

/-- Sign operands of the actual formula, root queries and ordinary sectors.
Original source bindings and divisor conditions remain the caller's inventory. -/
@[expose] def keys (point : Dyadic → E)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : List E :=
  formula.polys.map (fun atom => (query atom).coeff ((query atom).size - 1)) ++
    IsolationTransport.keys point head cert ++
    rows.entries.flatMap (fun row =>
      (List.finRange cert.isolations.intervals.size).flatMap fun i =>
        let interval := cert.isolations.intervals[i]
        QueryReplay.keys head (.finite (point interval.lower))
          (.finite (point interval.upper)) row.evidence[i]) ++
    SignInputs.openSamples point cert (formula.polys.map query)

variable (lookup : E → Option Int) (read : E → ℝ)
variable (closed : Transport.Closed read (fun _ => True))
variable (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
variable (point : Dyadic → E)
variable (point_spec : ∀ d, read (point d) = HexRealRootsTheory.Dyadic.toReal d)

include closed sound point_spec in
/-- Accepted rows give real Tarski queries with the exact atom and interval. -/
theorem rows_checked (context : Ctx) (head : DensePoly E)
    (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (rows : FieldRootSigns.Table E Ctx n roots)
    (accepted : checkRows lookup point context head intervals query formula rows = true)
    (i : Fin roots) (atom : RealFormula.Poly n) (member : atom ∈ formula.polys)
    (fallback : TarskiCertificate E E Ctx) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Transport.polynomial read head) (Transport.polynomial read (query atom))
      (.finite (HexRealRootsTheory.Dyadic.toReal intervals[i].lower))
      (.finite (HexRealRootsTheory.Dyadic.toReal intervals[i].upper))
      (rows.value fallback i atom) (Transport.query read id (rows.evidence fallback i atom)) = true := by
  have checked := rows.query_checkedWith formula _
    (rows.checkRows_checked formula _ accepted) i atom member fallback
  have result := QueryReplay.checked lookup read closed sound context head (query atom) _ _
    (rows.value fallback i atom) (rows.evidence fallback i atom) checked
  simpa only [Transport.endpoint, point_spec] using result

include closed sound in
/-- Each retained atom has its checked semantic degree. -/
theorem degrees (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (accepted : check lookup point context query formula radical cert rows = true)
    (atom : RealFormula.Poly n) (member : atom ∈ formula.polys) :
    (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial read (query atom))).natDegree = (query atom).natDegree := by
  simp only [check, Bool.and_eq_true] at accepted
  have guard := List.all_eq_true.mp accepted.1.1.1.1 atom member
  rw [natDegree_interpret (fun x : ℝ => x) (fun _ => Iff.rfl)]
  exact Transport.polynomial_degree read closed.read_zero _
    (QueryReplay.leading_spec lookup read sound _ guard)

include closed sound point_spec in
/-- Checked identities, complete root counts and same-root atom queries
determine signs throughout every real section and sector. -/
theorem cells (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read (query atom))).eval x = atom.eval (valuation x))
    (accepted : check lookup point context query formula radical cert rows = true) :
    ∃ roots : Fin cert.isolations.intervals.size → ℝ,
      StrictMono roots ∧ ∀ cell x, Cell.Region roots cell x →
        ∀ atom ∈ formula.polys, ∃ observed,
          Decision.cellSign (QueryReplay.cached lookup) point query cert
            (rows.value cert.total) cell atom = some observed ∧
          SignType.sign (((observed.toInt : Int) : ℝ)) = SignType.sign (atom.eval (valuation x)) := by
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨_, radicalChecked⟩, isolationChecked⟩, rowsChecked⟩, samples⟩ := accepted
  have coverage : ∀ atom ∈ formula.polys,
      interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (Transport.polynomial read (query atom)) = 0 ∨
      ∀ x, (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read (query atom))).IsRoot x →
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read radical.core)).IsRoot x := by
    intro atom member
    rcases RepresentationCarrier.atom_roots_transport read closed.read_zero closed.read_one
        (fun a b => closed.read_add a b trivial trivial)
        (fun a b => closed.read_mul a b trivial trivial)
        (formula.polys.map query) (query atom) (List.mem_map.mpr ⟨atom, member, rfl⟩) with
      zero | roots
    · exact Or.inl zero
    · right
      intro x root
      exact (radical.roots_transport read closed context _ radicalChecked x).mpr (roots x root)
  have queries := rows_checked lookup read closed sound point point_spec context radical.core
    cert.isolations.intervals.toVector query formula rows rowsChecked
  have semantics := Decision.cellSign_spec (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x : ℝ => (SignType.sign x : Int)) (fun _ => rfl)
    HexRealRootsTheory.Dyadic.toReal (fun _ => rfl) formula valuation
    (fun atom => Transport.polynomial read (query atom)) atom_eval context
    (Transport.polynomial read radical.core) (IsolationTransport.map read cert)
    (IsolationTransport.checked lookup read closed sound point point_spec context radical.core cert isolationChecked)
    coverage (rows.value cert.total)
    (fun i atom => Transport.query read id (rows.evidence cert.total i atom))
    (fun i atom member => queries i atom member cert.total)
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
    let key := (query atom).eval (point d)
    have sample : key ∈ SignInputs.openSamples point cert (formula.polys.map query) := by
      apply List.mem_flatMap.mpr
      refine ⟨Cell.open cut, Array.mem_toList_iff.mpr (Cell.mem_all _), ?_⟩
      exact List.mem_map.mpr ⟨query atom, List.mem_map.mpr ⟨atom, member, rfl⟩, rfl⟩
    have sign := (QueryReplay.cached_eq lookup _ samples key sample read).trans
      (QueryReplay.sign_spec lookup read sound key)
    have evaluation := Transport.Ring.polynomial_eval read closed.read_zero (query atom) (point d)
      (fun _ _ => closed.read_mul _ _ trivial trivial)
      (fun _ _ => closed.read_add _ _ trivial trivial)
    rw [point_spec] at evaluation
    change some (Sign.ofInt (QueryReplay.cached lookup key)) =
      some (Sign.ofInt ((SignType.sign ((Transport.polynomial read (query atom)).eval
        (HexRealRootsTheory.Dyadic.toReal d)) : Int)))
    rw [sign]
    change some (Sign.ofInt ((SignType.sign (read ((query atom).eval (point d))) : Int))) = _
    rw [evaluation]

include closed sound point_spec in
/-- The strict universal fold covers the whole real line. -/
theorem forall_formula (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read (query atom))).eval x = atom.eval (valuation x))
    (accepted : check lookup point context query formula radical cert rows = true) :
    OptionFold.allArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (Decision.cellSign (QueryReplay.cached lookup)
        point query cert (rows.value cert.total) cell)) = some true ↔
      ∀ x, formula.toProp (valuation x) := by
  obtain ⟨roots, ordered, meanings⟩ := cells lookup read closed sound point point_spec context
    query formula radical cert rows valuation atom_eval accepted
  exact RealCoefficients.forall_formula roots ordered formula valuation _ meanings

include closed sound point_spec in
/-- Existential truth has one ordinary real point satisfying its entire row. -/
theorem exists_formula (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size)
    (valuation : ℝ → Fin n → ℝ)
    (atom_eval : ∀ atom x,
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
        (Transport.polynomial read (query atom))).eval x = atom.eval (valuation x))
    (accepted : check lookup point context query formula radical cert rows = true) :
    OptionFold.anyArray (Cell.all cert.isolations.intervals.size)
      (fun cell => formula.evalSigns (Decision.cellSign (QueryReplay.cached lookup)
        point query cert (rows.value cert.total) cell)) = some true ↔
      ∃ x, formula.toProp (valuation x) := by
  obtain ⟨roots, ordered, meanings⟩ := cells lookup read closed sound point point_spec context
    query formula radical cert rows valuation atom_eval accepted
  exact RealCoefficients.exists_formula roots ordered formula valuation _ meanings

end Hex.RCF.RealCoefficients.QueryCells
