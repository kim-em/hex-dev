/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Nearest
public section

/-! Exact reference selection and certified lazy root selection. -/
namespace Hex.AlgebraicNumber
namespace Radical

/-- Rank the sign of the imaginary coordinate without computing the coordinate. -/
@[expose] def rank (a : AlgebraicNumber) : Int :=
  match a.side with
  | .lower => -1
  | .real => 0
  | .upper => 1

/-- A root candidate with its doubled real part computed once. -/
structure Candidate where
  value : AlgebraicNumber
  twiceRe : AlgebraicNumber
  correct : twiceRe = value + value.conj

/-- Exactify a root and cache the real coordinate used in branch selection. -/
@[expose] def candidate (r : RootCount) : Candidate :=
  let a := r.root.exact
  ⟨a, a + a.conj, rfl⟩

/-- Prefer greater real part, then the upper imaginary side. -/
@[expose] def choose (a b : Candidate) : Candidate :=
  match realCompare a.twiceRe b.twiceRe with
  | .lt => b
  | .eq => if rank a.value < rank b.value then b else a
  | .gt => a

/-- Select one principal candidate, sharing cached coordinates throughout the fold. -/
@[expose] def select (roots : Array RootCount) : Option Candidate :=
  match roots.toList with
  | [] => none
  | r :: rs => some (rs.foldl (fun best root => choose best (candidate root)) (candidate r))

end Radical
end Hex.AlgebraicNumber

/-- The exact imaginary side of a lazy root, without factorization. -/
@[expose] def Hex.AlgebraicRoot.side (a : Hex.AlgebraicRoot) : Hex.AlgebraicNumber.RootSide :=
  Hex.AlgebraicNumber.sideOf a.rep

namespace Hex.RootSelection

/-- One lazy root with its original precision, retained across refinement rounds. -/
structure Work where
  root : AlgebraicRoot
  prec : Int

/-- Same-polynomial root identity needs only the stored isolations. -/
@[expose] def same (a b : AlgebraicRoot) : Bool :=
  if h : a.p = b.p then (h ▸ a.rep).sameRoot b.rep else false

/-- Choose a proposed maximum by its centre; the proposal is checked separately. -/
@[expose] def pick (a b : Work) : Work :=
  if a.root.rep.1.square.re < b.root.rep.1.square.re then b else a

/-- A candidate is accepted only if every other value is equal or strictly to its left. -/
@[expose] def dominates (a b : Work) : Bool :=
  same a.root b.root ||
    (Interval.realOrder? b.root.rep.1.square a.root.rep.1.square == some .lt)

/-- Linear-time proposal and validation; no candidate is exactified. -/
@[expose] def probe : List Work → Option Work
  | [] => none
  | a :: rest =>
    let best := rest.foldl pick a
    if (a :: rest).all (dominates best) then some best else none

/-- Refine from the cached representative, relative to its original precision. -/
@[expose] def refine? (bits : Nat) (a : Work) : Option Work := do
  let r ← a.root.rep.refineTo? (a.prec + (bits : Int))
  pure { a with root := { a.root with rep := r.1, rep_mk := r.2.trans a.root.rep_mk } }

/-- Bounded selection with one cached representative per candidate. -/
@[expose] def search : List Nat → List Work → Option AlgebraicRoot
  | rounds, roots =>
    match probe roots with
    | some best => some best.root
    | none => match rounds with
      | [] => none
      | bits :: rest => do
        let refined ← roots.mapM (refine? bits)
        search rest refined

/-- Select a certified maximum real part, or leave the decision to an exact fallback. -/
@[expose] def select? (roots : List AlgebraicRoot) : Option AlgebraicRoot :=
  search [16, 64] (roots.map fun r => ⟨r, r.rep.1.square.prec⟩)

/-- A total-on-nonempty maximum selector, with the exact coordinate comparison
retained only as a fallback for inconclusive interval probes. -/
@[expose] def maximum? (roots : List AlgebraicRoot) : Option AlgebraicNumber :=
  match select? roots with
  | some root => some root.exact
  | none => (AlgebraicNumber.Radical.select
      (roots.map (fun r => (⟨r, 1, by decide⟩ : RootCount))).toArray).map (·.value)

/-- The integer root solver before exactification. This shares the checked
normalization/isolation pipeline of `ZPoly.algebraicRoots?`, without factoring
or canonicalizing every root. -/
@[expose] def integerRoots? (p : ZPoly) : Option (Array AlgebraicRoot) :=
  if p.natDegree = 0 then some #[] else
    let q := ZPoly.squareFreeCore p
    if hprim : ZPoly.content q = 1 then
      if hpos : 0 < q.leadingCoeff then
        if hdeg : 0 < q.natDegree then
          if hsimple : HasOnlySimpleRoots q then do
            let isolations ← ZPoly.isolateComplexRoots? q hsimple (separationDepth q : Int)
            let refined ← isolations.mapM DyadicRootIsolation.toRefined?
            pure (refined.map (AlgebraicRoot.ofRefined q hprim hpos hdeg hsimple))
          else none
        else none
      else none
    else none

end Hex.RootSelection
