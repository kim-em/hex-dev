/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.CellCheck
public import HexRCF.RealCoefficients.PolynomialRadical
public import HexRCF.RealCoefficients.PolynomialSigns
public import HexRCF.RealCoefficients.FieldIsolate
public section

namespace Hex.RCF.RealCoefficients.PolynomialBuild
open Hex Hex.OrderedFn.Oracle PolynomialBounds
open Hex.RealFormula (QF Quantifier)

/-- The shared source coordinates remain in their original order. -/
@[expose] def values (i : Fin n) : Poly n := MvPoly.X i

@[expose] def query (atom : RealFormula.Poly (n + 1)) : DensePoly (Poly n) :=
  RepresentationSpecialize.polynomial values atom

@[expose] def point (d : Dyadic) : Poly n := MvPoly.C d.toRat

/-- A finite proposal assembled from existing radical, isolation, atom-row and
sign records. Expected formula, bounds and source bindings are supplied by the
consumer; none is trusted merely because it was copied into a proposal. -/
structure Certificate (n : Nat) where
  radical : RadicalCert (Poly n) Unit
  isolation : IsolationReplay (Poly n) Unit
  rows : FieldRootSigns.Table (Poly n) Unit (n + 1) isolation.isolations.intervals.size
  entries : Array (LiteralSign.Entry (Poly n))
  index : LiteralSign.Index

/-- Construction failures remain distinct from either quantified verdict. -/
inductive Error where
  | radical
  | query
  | isolation
  | signs
  | replay
  deriving DecidableEq, Repr

/-- Check all coefficient evidence and the complete cell envelope, independently
of the quantified verdict. Replay performs no gcd, root or approximation search. -/
@[expose] def check (bounds : Fin n → Bounds) (formula : QF (n + 1))
    (cert : Certificate n) : Bool :=
  PolynomialSigns.check bounds cert.entries &&
    QueryCells.check (PolynomialSigns.lookup cert.entries cert.index) point () query formula
      cert.radical cert.isolation cert.rows

/-- Strictly evaluate every cell after evidence preflight. Accepted false is a
diagnostic value; it does not prove the corresponding source goal. -/
@[expose] def run (formula : QF (n + 1)) (quantifier : Quantifier)
    (cert : Certificate n) : Option Bool :=
  let row := fun cell => formula.evalSigns
    (Decision.cellSign (QueryReplay.cached (PolynomialSigns.lookup cert.entries cert.index))
      point query cert.isolation (cert.rows.value cert.isolation.total) cell)
  match quantifier with
  | .forallReal => OptionFold.allArray (Cell.all cert.isolation.isolations.intervals.size) row
  | .existsReal => OptionFold.anyArray (Cell.all cert.isolation.isolations.intervals.size) row

/-- Bounded fraction-free proposal construction from fixed coefficient bounds.
Missing signs can influence an untrusted proposal but cannot survive the exact
sign inventory and full replay preflight. Every atom occurrence is retained. -/
def buildResult (bounds : Fin n → Bounds) (formula : QF (n + 1)) (depth : Nat) :
    Except Error (Certificate n) := do
  let sign := fun q : Poly n => (PolynomialBounds.sign? bounds q).getD 0
  let product := RepresentationCarrier.product (formula.polys.map query)
  let some radical := PolynomialRadical.build () product | throw .radical
  let some total := TarskiCertificate.certify sign (EndpointSigns.ofSign sign)
    SignedRemainderChain.normalizeId () radical.core 1 .negInf .posInf | throw .query
  let some intervals := FieldIsolate.proposeWith? sign point SignedRemainderChain.normalizeId radical.core depth |
    throw .isolation
  let isolation : IsolationReplay (Poly n) Unit := {
    isolations := intervals
    total
    counts := Vector.ofFn fun i =>
      let interval := intervals.intervals[i]
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) () radical.core 1
        (.finite (point interval.lower)) (.finite (point interval.upper))
        total.squarefree total.remainders }
  let some rows := FieldRootSigns.Table.buildWith sign point SignedRemainderChain.normalizeId
    () radical.core isolation query formula | throw .query
  let keys := QueryCells.keys point query formula radical.core isolation rows
  let some (entries, index) := PolynomialSigns.build? bounds keys | throw .signs
  let cert : Certificate n := ⟨radical, isolation, rows, entries, index⟩
  if check bounds formula cert then return cert else throw .replay

/-- Optional proposal interface for existing numerical callers. `buildResult`
retains the typed failure stage needed by the tactic and diagnostics. -/
def build (bounds : Fin n → Bounds) (formula : QF (n + 1)) (depth : Nat) :
    Option (Certificate n) := (buildResult bounds formula depth).toOption

end Hex.RCF.RealCoefficients.PolynomialBuild
