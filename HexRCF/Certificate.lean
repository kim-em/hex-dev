/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SignMatrixCheck

public section

/-!
# Kernel certificate replay

This module assembles the already-checked carrier, isolation, endpoint, and
sign-matrix layers into a three-valued replay. `none` means malformed data,
`some false` is a valid diagnostic result, and the public Boolean checker
accepts only `some true`.
-/

namespace Hex.RCF

namespace OptionFold

/-- Universal option fold that does not Boolean-short-circuit a false value. -/
@[expose]
def all (f : α → Option Bool) : List α → Option Bool
  | [] => some true
  | x :: xs => do
      let head ← f x
      let tail ← all f xs
      pure (head && tail)

/-- Existential option fold that does not Boolean-short-circuit a true value. -/
@[expose]
def any (f : α → Option Bool) : List α → Option Bool
  | [] => some false
  | x :: xs => do
      let head ← f x
      let tail ← any f xs
      pure (head || tail)

/-- Universal fold over an array. -/
@[expose]
def allArray (xs : Array α) (f : α → Option Bool) : Option Bool :=
  all f xs.toList

/-- Existential fold over an array. -/
@[expose]
def anyArray (xs : Array α) (f : α → Option Bool) : Option Bool :=
  any f xs.toList

/-- Filter irrelevant entries before a strict universal fold. -/
@[expose]
def allWhereArray (xs : Array α) (relevant : α → Bool)
    (f : α → Option Bool) : Option Bool :=
  all f (xs.toList.filter relevant)

/-- Filter irrelevant entries before a strict existential fold. -/
@[expose]
def anyWhereArray (xs : Array α) (relevant : α → Bool)
    (f : α → Option Bool) : Option Bool :=
  any f (xs.toList.filter relevant)

end OptionFold

/-- Carrier and isolation data for a carrier with no real roots. -/
structure DecompCert where
  carrier : CarrierCert
  isolations : IsolationCert

/-- Full positive-root decomposition data. Endpoint comparisons are present
exactly for bounded sentences. -/
structure CellsCert where
  carrier : CarrierCert
  isolations : IsolationCert
  signs : SignMatrixCert
  iocCmps : Option (IocCmps isolations.intervals.size)

/-- The four disjoint replay branches. -/
inductive Certificate
  /-- Equal or reversed bounded endpoints. -/
  | emptyIoc
  /-- A formula containing no nonconstant atom polynomial. -/
  | constants
  /-- A checked carrier with no real roots. -/
  | noRoots (data : DecompCert)
  /-- A checked carrier with at least one real root. -/
  | cells (data : CellsCert)

/-- Evaluate one open cell without constructing common-root packages. -/
@[expose]
def Sentence.evalOpen? (s : Sentence) (isolations : IsolationCert)
    (cut : Fin (isolations.intervals.size + 1)) : Option Bool :=
  s.formula.evalSigns fun p => openCellSign? p isolations cut

/-- Replay the carrier-free constant branch. Nonempty bounded domains are
checked here; empty domains belong to `Certificate.emptyIoc`. -/
@[expose]
def Sentence.replayConstants? (s : Sentence) : Option Bool :=
  if s.polys.isEmpty then
    match s with
    | .forallReal formula | .existsReal formula => formula.evalConstants?
    | .forallIoc a b formula | .existsIoc a b formula =>
        if a < b then formula.evalConstants? else none
  else none

/-- Replay a checked decomposition whose carrier has no real roots. -/
@[expose]
def Sentence.replayNoRoots? (s : Sentence) (data : DecompCert) : Option Bool :=
  if data.carrier.check s &&
      data.isolations.checkStrict data.carrier.replay &&
      data.isolations.intervals.isEmpty then
    let cut := Fin.last data.isolations.intervals.size
    match s with
    | .forallReal _ | .existsReal _ => s.evalOpen? data.isolations cut
    | .forallIoc a b _ | .existsIoc a b _ =>
        if a < b then s.evalOpen? data.isolations cut else none
  else none

/-- Replay a checked positive-root decomposition. Real sentences forbid
endpoint data; bounded sentences require and verify it. -/
@[expose]
def Sentence.replayCells? (s : Sentence) (data : CellsCert) : Option Bool :=
  if data.carrier.check s &&
      data.isolations.checkStrict data.carrier.replay &&
      decide (0 < data.isolations.intervals.size) &&
      data.signs.check s data.carrier then
    let cells := Cell.all data.isolations.intervals.size
    let value := data.signs.evalCell? s data.isolations
    match s, data.iocCmps with
    | .forallReal _, none => OptionFold.allArray cells value
    | .existsReal _, none => OptionFold.anyArray cells value
    | .forallIoc a b _, some cmps =>
        if a < b && cmps.check data.carrier.carrier data.carrier.replay
            data.isolations a b then
          OptionFold.allWhereArray cells (Cell.meetsIocOn a b cmps) value
        else none
    | .existsIoc a b _, some cmps =>
        if a < b && cmps.check data.carrier.carrier data.carrier.replay
            data.isolations a b then
          OptionFold.anyWhereArray cells (Cell.meetsIocOn a b cmps) value
        else none
    | _, _ => none
  else none

/-- Three-valued certificate replay. -/
@[expose]
def Certificate.replay? (s : Sentence) : Certificate → Option Bool
  | .emptyIoc =>
      match s with
      | .forallIoc a b _ => if a < b then none else some true
      | .existsIoc a b _ => if a < b then none else some false
      | _ => none
  | .constants => s.replayConstants?
  | .noRoots data => s.replayNoRoots? data
  | .cells data => s.replayCells? data

/-- The kernel boundary accepts only a fully replayed true verdict. -/
@[expose]
def Certificate.check (s : Sentence) (cert : Certificate) : Bool :=
  cert.replay? s == some true

end Hex.RCF
