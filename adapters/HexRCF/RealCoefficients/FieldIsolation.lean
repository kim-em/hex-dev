/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldQuery
public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRCF.RealCoefficients.Isolations

public section

namespace Hex.RCF.RealCoefficients.FieldIsolation
open Hex.RealClosure

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable {Ctx : Type u} [DecidableEq Ctx]
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Retain the proposed intervals and independently check their complete count
and each count-one query, including all finite sign and leading guards.
The enclosing checker authenticates the shared sign table once. -/
@[expose] def checkWith (lookup : E → Option Int) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx) : Bool :=
  cert.isolations.checkGaps &&
    FieldQuery.checkWith lookup context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total &&
    (List.finRange cert.isolations.intervals.size).all fun i =>
      let interval := cert.isolations.intervals[i]
      FieldQuery.checkWith lookup context head 1
        (.finite (PolyQuot.ofRat interval.lower.toRat))
        (.finite (PolyQuot.ofRat interval.upper.toRat)) 1 cert.counts[i]

@[expose] def check (table : LiteralSign.Table E) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx) : Bool :=
  checkWith table.lookup? context head cert

/-- Exact finite sign inventory for the complete count and every root interval. -/
@[expose] def keys (head : DensePoly E) (cert : IsolationReplay E Ctx) : List E :=
  FieldQuery.keys head .negInf .posInf cert.total ++
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      FieldQuery.keys head (.finite (PolyQuot.ofRat interval.lower.toRat))
        (.finite (PolyQuot.ofRat interval.upper.toRat)) cert.counts[i]

/-- Transport the existing literal certificate, retaining interval order and
the exact root-count values. No isolation algorithm is evaluated. -/
@[expose, reducible] noncomputable def map (cert : IsolationReplay E Ctx) : IsolationReplay ℝ Ctx where
  isolations := cert.isolations
  total := Transport.query (Field.value (Field.literalRep p s hw hp)) id cert.total
  counts := Vector.ofFn fun i =>
    Transport.query (Field.value (Field.literalRep p s hw hp)) id cert.counts[i]

/-- Accepted finite coordinate checks give the existing real isolation check.
All degree and sign obligations come from `check`, without a field instance
or global zero reflection on the stored coordinate representation. -/
theorem checked (table : LiteralSign.Table E)
    (tableChecked : Field.checkSignTable p s hw hp table = true) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (accepted : check table context head cert = true) :
    (map cert).check (fun x : ℝ => (SignType.sign x : Int))
      HexRealRootsTheory.Dyadic.toReal context
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) head) = true := by
  simp only [check, checkWith, Bool.and_eq_true] at accepted
  obtain ⟨⟨gaps, total⟩, counts⟩ := accepted
  have real := FieldTransport.real table tableChecked
  let read : E → ℝ := Field.value (Field.literalRep p s hw hp)
  have unit : Transport.polynomial read (1 : DensePoly E) = 1 :=
    Transport.polynomial_one read
      (Field.value_zero _ (Field.literalRep_mk p s hw hp) real)
      (Field.value_one _ (Field.literalRep_mk p s hw hp) real)
  have point (d : Dyadic) :
      read (PolyQuot.ofRat d.toRat) = HexRealRootsTheory.Dyadic.toReal d := by
    exact FieldTransport.point table tableChecked d
  dsimp only [read] at unit point
  simp only [IsolationReplay.check, map, Bool.and_eq_true]
  refine ⟨⟨gaps, ?_⟩, ?_⟩
  · have result := FieldQuery.checked table tableChecked context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total total
    simpa only [unit, Transport.endpoint] using result
  · apply List.all_eq_true.mpr
    intro i member
    have result := FieldQuery.checked table tableChecked context head 1
      (.finite (PolyQuot.ofRat cert.isolations.intervals[i].lower.toRat))
      (.finite (PolyQuot.ofRat cert.isolations.intervals[i].upper.toRat))
      1 cert.counts[i] (List.all_eq_true.mp counts i member)
    simpa [unit, Transport.endpoint, point] using result

/-- Checked counts provide all real roots in strict order, with ordinary
sample points in every intervening sector. Coverage is a checked conclusion. -/
theorem roots (table : LiteralSign.Table E)
    (tableChecked : Field.checkSignTable p s hw hp table = true) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (accepted : check table context head cert = true) :
    let polynomial := HexPolyTheory.Interpret.interpret (fun x : ℝ => x) (fun _ => Iff.rfl)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) head)
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, polynomial.IsRoot (root i) ∧
        HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsTheory.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, polynomial.IsRoot x ↔ ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsTheory.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  exact (map cert).check_roots (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x : ℝ => (SignType.sign x : Int)) (fun _ => rfl)
    HexRealRootsTheory.Dyadic.toReal (fun _ => rfl) context _
    (checked table tableChecked context head cert accepted)

end Hex.RCF.RealCoefficients.FieldIsolation
