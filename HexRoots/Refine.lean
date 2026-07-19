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

`isolateLoop` refines a worklist of components round by round. Up to the
fixed `completenessDepth`, every round globally subdivides and reglues all
survivors; this eliminates rootless halo components and is the invariant used
by the completeness proof. Once that depth has been reached, a round emits
when all components certify at stored precision at least `target` with
pairwise disjoint circumscribed discs. Otherwise the hold/adopt optimization
takes over while the loop recurses on the smaller fuel. The fuel counts down
structurally on a `Nat`, so the recursion needs no termination proof;
`stopDepth p target` fixes the depth at which the drivers give up, following
the SPEC "Termination" and "Separation of the output" sections. Every
quantity here is exact: the emission test is a pairwise
`DyadicSquare.discsMeet` comparison of stored squares, and the precision
comparisons are on the exact `Int` precs.
-/
namespace Hex

/-- The fixed give-up margin above `separationDepth` used by `stopDepth`.
    Overshooting costs only a few extra subdivision rounds in the rare case
    certification had not already happened, and nothing else. The globally
    normalized prefix ends three levels before this bound. -/
@[expose] def stopSlack : Nat := 8

/-- SPEC Termination: the depth at which the drivers give up,
    `max target (separationDepth p) + stopSlack`. A `none` from a driver means
    that its full emission condition was not reached within this fuel bound. -/
@[expose] def stopDepth (p : ZPoly) (target : Int) : Int :=
  max target (separationDepth p : Int) + (stopSlack : Int)

/-- The depth through which the Cauchy-started driver uses globally glued,
uniform subdivision rounds. Two levels pay for `encSquare`; the other three
cover the quadrupled Pellet base (or doubled NK base) with one strict margin
level. -/
@[expose] def completenessDepth (p : ZPoly) (target : Int) : Int :=
  max target (separationDepth p : Int) + 5

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

/-- Re-enter a certification result into the worklist as a component.

    The retained square must *cover* the certified region, not merely be
    certified: refinement preserves exactly the roots that lie in the
    retained squares themselves (children partition the square, and the
    `T₀` discard is sound), while a Pellet certificate counts roots in
    the stored square's circumscribed *disc*. A root in the disc but
    outside the square would be silently lost by the next subdivision;
    with repeated Newton-jump adoptions this loses far roots of a
    many-root cluster (the certified disc shrinks toward the cluster's
    Newton centroid while still counting every root). Retaining the
    *doubled* stored square (half-width `2·2^{−prec}` ≥ the disc radius
    `√2·2^{−prec}`) restores the cover for both certificate forms, at
    the cost of one precision level, which the strictly-finer adoption
    guard in `isolateLoop` still absorbs (a Newton jump gains at least
    two levels). -/
@[expose] def Certified.toComponent {p : ZPoly} : Certified p → Component
  | .atom iso => ⟨#[iso.square.doubled], 1⟩
  | .cluster cl => ⟨#[(encSquare cl.squares).doubled], cl.k⟩

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

/-- Fuel for `isolateLoop`: the laggard's climb from the worklist's
    coarsest prec to `stopDepth`, plus a second climb from `target` to
    `stopDepth` for a held component forced back into refinement by a
    late-certifying overlapping sibling (see `isolateLoop`). -/
@[expose] def fuelFor (p : ZPoly) (target : Int) (start : Int) : Nat :=
  (stopDepth p target - start).toNat + (stopDepth p target - target).toNat + 1

namespace IsolationLoop

/-- Every component has reached the globally normalized completeness depth. -/
@[expose] def normalized (p : ZPoly) (target : Int)
    (tried : Array (Component × Option (Certified p))) : Bool :=
  tried.all fun t => completenessDepth p target ≤ t.1.prec

/-- Attempt certification on every component in a worklist. -/
@[expose] def attempts (p : ZPoly) (strategy : AtomStrategy)
    (work : Array Component) : Array (Component × Option (Certified p)) :=
  work.map fun c => (c, Component.certify? p strategy c)

/-- Every attempted component certified at the requested stored precision. -/
@[expose] def allReady {p : ZPoly} (target : Int)
    (tried : Array (Component × Option (Certified p))) : Bool :=
  tried.all fun t => match t.2 with
    | some r => target ≤ r.square.prec
    | none => false

/-- The successful certificates in an attempts array. -/
@[expose] def outputs {p : ZPoly}
    (tried : Array (Component × Option (Certified p))) : Array (Certified p) :=
  tried.filterMap (·.2)

/-- The stored squares of successful attempts are pairwise disjoint. -/
@[expose] def disjoint {p : ZPoly}
    (tried : Array (Component × Option (Certified p))) : Bool :=
  pairwiseDisjoint (outputs tried |>.map (·.square))

/-- Whether a successful result overlaps another successful result in the
attempts array. -/
@[expose] def overlaps {p : ZPoly}
    (tried : Array (Component × Option (Certified p))) (i : Nat)
    (res : Certified p) : Bool :=
  let certSquares := tried.map fun t => t.2.map (·.square)
  (Array.range tried.size).any fun j =>
    i ≠ j && (match certSquares.getD j none with
              | some sj => res.square.discsMeet sj
              | none => false)

/-- The contribution of one attempted component to a non-emitting round. -/
@[expose] def step (p : ZPoly) (target : Int)
    (tried : Array (Component × Option (Certified p))) (i : Nat) :
    Array Component :=
  match tried.getD i (⟨#[], 0⟩, none) with
  | (c, some res) =>
    let ready := target ≤ res.square.prec
    if ready && !overlaps tried i res then #[c]
    else
      let c' := res.toComponent
      if c.prec < c'.prec then #[c'] else c.refine1 p
  | (c, none) => c.refine1 p

/-- Worklist for a non-emitting round. Ready certificates disjoint from all
other successful certificates hold their input component; other successes
adopt a strictly finer doubled result or refine, and failures refine. -/
@[expose] def nextLocal (p : ZPoly) (target : Int)
    (tried : Array (Component × Option (Certified p))) : Array Component :=
  (Array.range tried.size).flatMap (step p target tried)

/-- Worklist for a non-emitting full-isolation round. Before normalization,
all squares refine and reglue globally; afterwards this is `nextLocal`. -/
@[expose] def next (p : ZPoly) (target : Int)
    (tried : Array (Component × Option (Certified p))) : Array Component :=
  if normalized p target tried then
    nextLocal p target tried
  else
    Component.refineAll p (tried.map (·.1))

end IsolationLoop

/-- The shared driver loop over the worklist. Before every component reaches
    `completenessDepth`, the round globally refines and reglues the retained
    squares, irrespective of attempted certificates. At and beyond that depth,
    if all components certify at stored prec at least `target` with pairwise
    disjoint circumscribed discs (SPEC "Separation of the output"), the round
    emits them. Otherwise: a component already certified at target whose disc
    is disjoint from every other certified disc holds its position; every
    other surviving component subdivides one level, except that one adopting
    a strictly finer certified result keeps that result as a one-square
    component instead. Each post-normalization non-emitting round strictly
    increases every non-held component's prec, and held components sit at
    target, so the laggard's prec reaches `stopDepth` within
    `(stopDepth − min prec)` rounds. A held component can be forced back
    into refinement late, when a slow sibling finally certifies with an
    overlapping disc, so `fuelFor` budgets a second climb on top: past
    `separationDepth` every certified disc is below `sep/4` and distinct
    roots' discs are disjoint, so `(stopDepth − target)` further rounds
    suffice. `fuel = 0` returns `none`, the SPEC give-up semantics (up to a
    harmless constant of overshoot). The recursion is structural on the
    fuel `Nat`. -/
@[expose] def isolateLoop (p : ZPoly) (target : Int) (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := IsolationLoop.attempts p strategy work
    if IsolationLoop.normalized p target tried &&
        (IsolationLoop.allReady target tried && IsolationLoop.disjoint tried) then
      some (IsolationLoop.outputs tried)
    else
      -- A component whose certification already meets the target and whose
      -- disc is disjoint from every other certified disc holds its position
      -- (re-entering unchanged) while the laggards catch up; only
      -- disjointness violators and unready components keep refining (SPEC
      -- "Separation of the output"). Without the hold, a waiting component
      -- would keep adopting Newton results, doubling its precision every
      -- round and blowing the working bit-length while a slow sibling
      -- (e.g. a tight cluster forced down to its separation depth)
      -- subdivides.
      isolateLoop p target strategy fuel <|
        IsolationLoop.next p target tried

/-- Local refinement loop for one already-isolated atom. Unlike the
Cauchy-started full driver, it does not pay the global halo-normalization
prefix: there are no sibling lineages to reglue. -/
@[expose] def refineLoop (p : ZPoly) (target : Int) (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := IsolationLoop.attempts p strategy work
    if IsolationLoop.allReady target tried && IsolationLoop.disjoint tried then
      some (IsolationLoop.outputs tried)
    else
      refineLoop p target strategy fuel <|
        IsolationLoop.nextLocal p target tried

/-- Refine to `target` precision: speculative Newton steps, falling back to
    local subdivision of the atom's square as a one-square component. This
    path does not use the global completeness prefix. `none` only if the full
    ready/disjoint emission condition has not appeared within its fuel bound. -/
@[expose] def DyadicRootIsolation.refineTo? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option (DyadicRootIsolation p) :=
  if target ≤ iso.square.prec then some iso else
  let fuel := fuelFor p target iso.square.prec
  match refineLoop p target strategy fuel #[⟨#[iso.square.doubled], 1⟩] with
  | some rs =>
    if rs.size = 1 then
      match rs[0]? with
      | some (Certified.atom iso') => some iso'
      | _ => none
    else none
  | none => none

end Hex
