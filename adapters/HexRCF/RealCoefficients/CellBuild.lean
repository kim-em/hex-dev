/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.CellDecision
public import HexRCF.RealCoefficients.IsolationBuild
public import HexRCF.RealCoefficients.RadicalBuild

public section

/-! Produce and replay cell signs in fixed root and atom order. -/

namespace Hex.RCF.RealCoefficients

open Hex.RealFormula

/-- Literal evidence for one formula. Root rows follow isolation order, and
columns follow the formula's left-to-right atom order, including duplicates. -/
structure CellReplay (n : Nat) (Ctx : Type u) [DecidableEq Ctx]
    (formula : QF (n + 1)) where
  radical : RadicalCert RealAlgebraicNumber Ctx
  isolation : IsolationReplay RealAlgebraicNumber Ctx
  openValues : Vector (Vector Int formula.polys.length)
    (isolation.isolations.intervals.size + 1)
  rootValues : Vector (Vector Int formula.polys.length) isolation.isolations.intervals.size
  rootQueries : Vector
    (Vector (TarskiCertificate RealAlgebraicNumber RealAlgebraicNumber Ctx)
      formula.polys.length) isolation.isolations.intervals.size

namespace CellReplay

variable {n : Nat} {Ctx : Type u} [DecidableEq Ctx]

/-- Replay the product reduction, complete root isolation, and every recorded
query. Vector dimensions enforce exact row and column counts; no `zip` can
silently discard a missing atom or root. -/
@[expose] def check (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula) : Bool :=
  cert.radical.check context (Specialize.product values formula) &&
    cert.isolation.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context cert.radical.core &&
    (List.finRange cert.isolation.isolations.intervals.size).all (fun i =>
      (List.finRange formula.polys.length).all (fun j =>
        Sturm.check RealAlgebraicNumber.sign context cert.radical.core
          (Specialize.polynomial values formula.polys[j])
          (.finite (RealAlgebraicNumber.ofRat
            cert.isolation.isolations.intervals[i].lower.toRat))
          (.finite (RealAlgebraicNumber.ofRat
            cert.isolation.isolations.intervals[i].upper.toRat))
          cert.rootValues[i][j] cert.rootQueries[i][j])) &&
    (List.finRange (cert.isolation.isolations.intervals.size + 1)).all (fun cut =>
      (List.finRange formula.polys.length).all (fun j =>
        cert.openValues[cut][j] == RealAlgebraicNumber.sign
          ((Specialize.polynomial values formula.polys[j]).eval
            (RealAlgebraicNumber.ofRat
              (cert.isolation.isolations.openPoint cut).toRat))))

/-- Repeated occurrences use their first recorded column. Values outside the
formula are irrelevant to the fold; the default is never used by an atom. -/
@[expose] def valueAt (formula : QF (n + 1))
    (cert : CellReplay n Ctx formula)
    (i : Fin cert.isolation.isolations.intervals.size)
    (p : RealFormula.Poly (n + 1)) : Int :=
  if h : p ∈ formula.polys then
    let j : Fin formula.polys.length :=
      ⟨formula.polys.idxOf p, List.idxOf_lt_length_iff.mpr h⟩
    cert.rootValues[i][j]
  else 0

/-- Read an open-cell sign in the same fixed atom order. -/
@[expose] def openValueAt (formula : QF (n + 1))
    (cert : CellReplay n Ctx formula)
    (cut : Fin (cert.isolation.isolations.intervals.size + 1))
    (p : RealFormula.Poly (n + 1)) : Int :=
  if h : p ∈ formula.polys then
    let j : Fin formula.polys.length :=
      ⟨formula.polys.idxOf p, List.idxOf_lt_length_iff.mpr h⟩
    cert.openValues[cut][j]
  else 0

/-- Locate the evidence paired with `valueAt`. The fallback is never used for
an atom of the formula. -/
@[expose] def queryAt (formula : QF (n + 1))
    (cert : CellReplay n Ctx formula)
    (i : Fin cert.isolation.isolations.intervals.size)
    (p : RealFormula.Poly (n + 1)) :
    TarskiCertificate RealAlgebraicNumber RealAlgebraicNumber Ctx :=
  if h : p ∈ formula.polys then
    let j : Fin formula.polys.length :=
      ⟨formula.polys.idxOf p, List.idxOf_lt_length_iff.mpr h⟩
    cert.rootQueries[i][j]
  else cert.isolation.total

/-- Accepted replay checks the exact query for each atom, including a repeated
atom whose value is read from its first column. -/
theorem check_query (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true)
    (i : Fin cert.isolation.isolations.intervals.size)
    (p : RealFormula.Poly (n + 1)) (hp : p ∈ formula.polys) :
    Sturm.check RealAlgebraicNumber.sign context cert.radical.core
      (Specialize.polynomial values p)
      (.finite (RealAlgebraicNumber.ofRat cert.isolation.isolations.intervals[i].lower.toRat))
      (.finite (RealAlgebraicNumber.ofRat cert.isolation.isolations.intervals[i].upper.toRat))
      (cert.valueAt formula i p) (cert.queryAt formula i p) = true := by
  simp only [check, Bool.and_eq_true] at h
  let j : Fin formula.polys.length :=
    ⟨formula.polys.idxOf p, List.idxOf_lt_length_iff.mpr hp⟩
  have hrow := List.all_eq_true.mp h.1.2 i (List.mem_finRange i)
  have hcol := List.all_eq_true.mp hrow j (List.mem_finRange j)
  have hj : formula.polys[j] = p := List.getElem_idxOf j.isLt
  have hv : cert.valueAt formula i p = cert.rootValues[i][j] := by
    unfold valueAt
    simp only [dite_eq_left hp]
    rfl
  have he : cert.queryAt formula i p = cert.rootQueries[i][j] := by
    unfold queryAt
    simp only [dite_eq_left hp]
    rfl
  rw [hv, he]
  simpa only [hj] using hcol

/-- Accepted replay binds a literal open-cell sign to its exact sample and
specialized source atom. -/
theorem check_open (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true)
    (cut : Fin (cert.isolation.isolations.intervals.size + 1))
    (p : RealFormula.Poly (n + 1)) (hp : p ∈ formula.polys) :
    cert.openValueAt formula cut p = RealAlgebraicNumber.sign
      ((Specialize.polynomial values p).eval
        (RealAlgebraicNumber.ofRat (cert.isolation.isolations.openPoint cut).toRat)) := by
  simp only [check, Bool.and_eq_true] at h
  let j : Fin formula.polys.length :=
    ⟨formula.polys.idxOf p, List.idxOf_lt_length_iff.mpr hp⟩
  have hrow := List.all_eq_true.mp h.2 cut (List.mem_finRange cut)
  have hcol := List.all_eq_true.mp hrow j (List.mem_finRange j)
  have hj : formula.polys[j] = p := List.getElem_idxOf j.isLt
  have hv : cert.openValueAt formula cut p = cert.openValues[cut][j] := by
    unfold openValueAt
    simp only [dite_eq_left hp]
    rfl
  rw [hv]
  exact (beq_iff_eq.mp hcol).trans (by rw [hj])

/-- The finite checker supplies the three independent premises used by the
cell semantic theorem. -/
theorem check_parts (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true) :
    cert.radical.check context (Specialize.product values formula) = true ∧
    cert.isolation.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context cert.radical.core = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.1

/-- Formula evaluation reads only literal sign rows after replay has checked
their equality to the executable sample computations. -/
@[expose] def signAt (formula : QF (n + 1))
    (cert : CellReplay n Ctx formula)
    (cell : Cell cert.isolation.isolations.intervals.size)
    (p : RealFormula.Poly (n + 1)) : Option Sign :=
  match cell with
  | .open cut => some (Sign.ofInt (cert.openValueAt formula cut p))
  | .root i => some (Sign.ofInt (cert.valueAt formula i p))

theorem signAt_eq_cellSign (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true)
    (cell : Cell cert.isolation.isolations.intervals.size)
    (p : RealFormula.Poly (n + 1)) (hp : p ∈ formula.polys) :
    cert.signAt formula cell p =
      cellSign values cert.isolation (cert.valueAt formula) cell p := by
  cases cell with
  | root i => rfl
  | «open» cut =>
      simp only [signAt, cellSign]
      rw [cert.check_open values formula context h cut p hp]

/-- Replayed literal rows prove the universal source formula exactly when the
strict cell fold returns true. -/
theorem forall_spec (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true) :
    OptionFold.allArray (Cell.all cert.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns (cert.signAt formula cell)) = some true ↔
      ∀ x, formula.toProp (append (fun j => (values j).toReal) x) := by
  obtain ⟨hradical, hisolation⟩ := cert.check_parts values formula context h
  have hfold : (fun cell => formula.evalSigns (cert.signAt formula cell)) =
      (fun cell => formula.evalSigns
        (cellSign values cert.isolation (cert.valueAt formula) cell)) := by
    funext cell
    exact formula.evalSigns_congr _ _
      (fun p hp => cert.signAt_eq_cellSign values formula context h cell p hp)
  rw [hfold]
  exact forall_cells values formula context cert.radical hradical
    cert.isolation hisolation (cert.valueAt formula) (cert.queryAt formula)
    (fun i p hp => cert.check_query values formula context h i p hp)

/-- Replayed literal rows prove the existential source formula exactly when
the strict cell fold returns true. -/
theorem exists_spec (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx)
    (cert : CellReplay n Ctx formula)
    (h : cert.check values formula context = true) :
    OptionFold.anyArray (Cell.all cert.isolation.isolations.intervals.size)
      (fun cell => formula.evalSigns (cert.signAt formula cell)) = some true ↔
      ∃ x, formula.toProp (append (fun j => (values j).toReal) x) := by
  obtain ⟨hradical, hisolation⟩ := cert.check_parts values formula context h
  have hfold : (fun cell => formula.evalSigns (cert.signAt formula cell)) =
      (fun cell => formula.evalSigns
        (cellSign values cert.isolation (cert.valueAt formula) cell)) := by
    funext cell
    exact formula.evalSigns_congr _ _
      (fun p hp => cert.signAt_eq_cellSign values formula context h cell p hp)
  rw [hfold]
  exact exists_cells values formula context cert.radical hradical
    cert.isolation hisolation (cert.valueAt formula) (cert.queryAt formula)
    (fun i p hp => cert.check_query values formula context h i p hp)

/-- Produce one candidate certificate at a requested isolation precision.
Failure makes no claim about the formula; callers may refine the precision.
The final replay runs after all proposals are constructed. -/
def build [RealAlgebraicNumber.Laws] (values : Fin n → RealAlgebraicNumber)
    (formula : QF (n + 1)) (context : Ctx) (precision : Nat) :
    Option (CellReplay n Ctx formula) :=
  match RadicalCert.build context (Specialize.product values formula) with
  | none => none
  | some radical =>
      match isolateAt context radical.core precision with
      | none => none
      | some isolation =>
          let openValues := Vector.ofFn fun cut => Vector.ofFn fun j =>
            RealAlgebraicNumber.sign
              ((Specialize.polynomial values formula.polys[j]).eval
                (RealAlgebraicNumber.ofRat
                  (isolation.isolations.openPoint cut).toRat))
          let rootQueries := Vector.ofFn fun i => Vector.ofFn fun j =>
            isolation.queryAt RealAlgebraicNumber.sign
              (fun d => RealAlgebraicNumber.ofRat d.toRat) context radical.core
              (Specialize.polynomial values formula.polys[j]) i
          let rootValues := Vector.ofFn fun i => Vector.ofFn fun j => rootQueries[i][j].value
          let cert : CellReplay n Ctx formula :=
            ⟨radical, isolation, openValues, rootValues, rootQueries⟩
          if cert.check values formula context then some cert else none

/-- A successful producer result passes the same exact replay check used for
arbitrary literal certificates. -/
theorem build_checked [RealAlgebraicNumber.Laws]
    (values : Fin n → RealAlgebraicNumber) (formula : QF (n + 1))
    (context : Ctx) (precision : Nat) (cert : CellReplay n Ctx formula)
    (h : build values formula context precision = some cert) :
    cert.check values formula context = true := by
  unfold build at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · dsimp only at h
      split at h
      · cases Option.some.inj h
        assumption
      · contradiction

end CellReplay
end Hex.RCF.RealCoefficients
