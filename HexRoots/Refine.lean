/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Bisection
public import HexRoots.Cauchy
public import HexRoots.MahlerPrec

public section

/-!
The shared fuel-based driver loop of the complex root isolator, and the
thin `DyadicRootIsolation.refineTo?` wrapper over it.

`isolateLoop` refines a worklist of components round by round: each round
tries to certify every component, and if all certify at stored precision at
least `target` with pairwise disjoint circumscribed discs, it emits them;
otherwise every component that did not adopt a strictly finer certified
result subdivides one level and the loop recurses on the smaller fuel. The
fuel counts down structurally on a `Nat`, so the recursion needs no
termination proof; `stopDepth p target` fixes the depth at which the drivers
give up, following the SPEC "Termination" and "Separation of the output"
sections. Every quantity here is exact: the emission test is a pairwise
`DyadicSquare.discsMeet` comparison of stored squares, and the precision
comparisons are on the exact `Int` precs.
-/
namespace Hex

/-- The fixed give-up margin above `separationDepth` used by `stopDepth`.
    Overshooting costs only a few extra subdivision rounds in the rare case
    certification had not already happened, and nothing else. -/
@[expose] def stopSlack : Nat := 8

/-- SPEC Termination: the depth at which the drivers give up,
    `max target (separationDepth p) + stopSlack`. A `none` from the drivers
    means precisely that no certificate the selected strategy attempts had
    appeared by this depth. -/
@[expose] def stopDepth (p : ZPoly) (target : Int) : Int :=
  max target (separationDepth p : Int) + (stopSlack : Int)

namespace Component

/-- The common `prec` of a component's squares (`0` for the empty component,
    which the drivers never produce). -/
@[expose] def prec (c : Component) : Int :=
  (c.squares[0]?.map (·.prec)).getD 0

end Component

/-- The stored square of a certification result: the atom's square, or the
    cluster's enclosing square. The separation check and the emission
    precision test read this. -/
@[expose] def Certified.square {p : ZPoly} : Certified p → DyadicSquare
  | .atom iso => iso.square
  | .cluster cl => encSquare cl.squares

/-- Re-enter a certification result into the worklist as a component: the
    atom becomes a one-square component with `candidateK = 1`, the cluster
    keeps its squares and root count. -/
def Certified.toComponent {p : ZPoly} : Certified p → Component
  | .atom iso => ⟨#[iso.square], 1⟩
  | .cluster cl => ⟨cl.squares, cl.k⟩

/-- All stored squares' circumscribed discs are pairwise disjoint, i.e.
    `!discsMeet` holds for every pair. One exact dyadic comparison per pair,
    as in the `SimpleRoot` intersection test. -/
@[expose] def pairwiseDisjoint (ss : Array DyadicSquare) : Bool :=
  (List.range ss.size).all fun i =>
    (List.range ss.size).all fun j =>
      if i < j then
        !(ss.getD i ⟨0, 0, 0⟩).discsMeet (ss.getD j ⟨0, 0, 0⟩)
      else
        true

/-- The shared driver loop over the worklist. Each round certifies every
    component; if all certify at stored prec at least `target` with pairwise
    disjoint circumscribed discs (SPEC "Separation of the output"), the round
    emits them. Otherwise every surviving component subdivides one level,
    except that a component adopting a strictly finer certified result keeps
    that result as a one-square component instead, so each non-emitting round
    strictly increases every surviving component's prec; the loop then
    recurses on the smaller fuel. `fuel = 0` returns `none`, the SPEC give-up
    semantics (up to a harmless constant of overshoot); a caller sizes the
    fuel as `(stopDepth p target − min prec).toNat + 1` so the loop reaches
    `stopDepth` before running out. The recursion is structural on the fuel
    `Nat`. -/
def isolateLoop (p : ZPoly) (target : Int) (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := work.map fun c => (c, Component.certify? p strategy c)
    let allReady := tried.all fun t => match t.2 with
      | some r => target ≤ r.square.prec
      | none => false
    let disjoint := pairwiseDisjoint (tried.filterMap fun t => t.2.map (·.square))
    if allReady && disjoint then
      some (tried.filterMap (·.2))
    else
      isolateLoop p target strategy fuel <| tried.flatMap fun (c, r) =>
        match r with
        | some res =>
          let c' := res.toComponent
          if c.prec < c'.prec then #[c'] else c.refine1 p
        | none => c.refine1 p

/-- Refine to `target` precision: speculative Newton steps, falling back to
    subdivision of the atom's square as a one-square component. `none` only
    if certification has not reappeared by `stopDepth p target`. -/
def DyadicRootIsolation.refineTo? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option (DyadicRootIsolation p) :=
  if target ≤ iso.square.prec then some iso else
  let fuel := (stopDepth p target - iso.square.prec).toNat + 1
  match isolateLoop p target strategy fuel #[⟨#[iso.square], 1⟩] with
  | some rs =>
    if rs.size = 1 then
      match rs[0]? with
      | some (Certified.atom iso') => some iso'
      | _ => none
    else none
  | none => none

end Hex
