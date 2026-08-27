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

`isolateLoop` refines a worklist of components round by round. A round emits
when all components certify at stored precision at least `target`, their
circumscribed discs are pairwise disjoint, and either every certificate is
already an atom or the worklist has reached the fixed `completenessDepth`.
Before that depth, a non-emitting round globally subdivides and reglues all
survivors; this eliminates rootless halo components and is the invariant used
by the completeness proof. Afterwards the hold/adopt optimization takes over
while the loop recurses on the smaller fuel. The fuel counts down
structurally on a `Nat`, so the recursion needs no termination proof;
`stopDepth p target` fixes the depth at which the drivers give up. Every
quantity here is exact: the emission test is a pairwise
`DyadicSquare.discsMeet` comparison of stored squares, and the precision
comparisons are on the exact `Int` precs.

The public one-atom wrapper first tries a bounded lineage-local speculative
pass, preserving Newton's logarithmic precision growth. If that pass cannot
emit exactly one target-ready atom, `refineLoop` restarts from the original
atom and uses the same globally reglued prefix as the full driver; subdivision
can split even a single starting square into sibling survivor lineages.

`findAtomLoop` starts instead from an uncertified caller-selected square. It
searches only that region and stops as soon as any component certifies as an
atom, then hands that atom to the ordinary one-atom refiner. The returned
certificate is self-contained, so this path needs neither all roots nor a
pairwise-disjoint output family.
-/
namespace Hex

/-- The fixed give-up margin above `separationDepth` used by `stopDepth`.
    Overshooting costs only a few extra subdivision rounds in the rare case
    certification had not already happened, and nothing else. The globally
    normalized prefix ends three levels before this bound. -/
@[expose] def stopSlack : Nat := 8

/-- The depth at which the drivers give up,
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

/-- Every attempted component certified as an atom. This stronger form is
also the guard for leaving global reglue early: failures and cluster results
must remain in the globally normalized subdivision path. -/
@[expose] def allAtoms {p : ZPoly}
    (tried : Array (Component × Option (Certified p))) : Bool :=
  tried.all fun t => match t.2 with
    | some (.atom _) => true
    | _ => false

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

/-- Refinement loop for one already-isolated atom.  Subdivision can split even
one starting component into several survivor lineages, so before the fixed
completeness depth this uses the same globally reglued transition as the full
driver.  A result is emitted only when it is the single target-ready atom
required by `refineAtom?`. -/
@[expose] def refineLoop (p : ZPoly) (target : Int) (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := IsolationLoop.attempts p strategy work
    if IsolationLoop.allReady target tried && IsolationLoop.disjoint tried &&
        IsolationLoop.allAtoms tried && (IsolationLoop.outputs tried).size == 1 then
      some (IsolationLoop.outputs tried)
    else
      refineLoop p target strategy fuel <|
        IsolationLoop.next p target tried

/-- Small speculative budget used before the globally normalized completeness
fallback. Successful Newton adoption normally needs only logarithmically many
rounds, while failure simply restarts from the original atom on `refineLoop`. -/
@[expose] def fastRefineFuel : Nat := 64

/-- Opportunistic lineage-local refinement. This loop is only a fast path: its
result is accepted under the same singleton-atom guard as `refineLoop`, and any
failure falls back to the globally reglued complete loop. -/
@[expose] def refineFastLoop (p : ZPoly) (target : Int)
    (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := IsolationLoop.attempts p strategy work
    if IsolationLoop.allReady target tried && IsolationLoop.disjoint tried &&
        IsolationLoop.allAtoms tried && (IsolationLoop.outputs tried).size == 1 then
      some (IsolationLoop.outputs tried)
    else
      refineFastLoop p target strategy fuel <|
        IsolationLoop.nextLocal p target tried

/-- Bounded speculative refinement of one atom. A rejected or exhausted run
returns `none`, so callers can fall back without trusting this optimization. -/
@[expose] def refineFastAtom? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy) : Option (DyadicRootIsolation p) :=
  match refineFastLoop p target strategy fastRefineFuel
      #[⟨#[iso.square.doubled], 1⟩] with
  | some rs =>
    if rs.size = 1 then
      match rs[0]? with
      | some (Certified.atom iso') => some iso'
      | _ => none
    else none
  | none => none

/-- Internal atom refiner shared by the public one-atom API and the
all-atoms fast path in the full isolation driver. -/
@[expose] def refineAtom? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy) : Option (DyadicRootIsolation p) :=
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

/-- Find and refine the first atom among a round's certification attempts.
    Array order makes the choice deterministic; clusters, failed
    certifications, and atoms that fail to refine are skipped. -/
@[expose] def firstRefinedAtom? {p : ZPoly} (target : Int)
    (strategy : AtomStrategy)
    (tried : Array (Component × Option (Certified p))) :
    Option (DyadicRootIsolation p) :=
  tried.toList.findSome? fun t => match t.2 with
    | some (.atom iso) => refineAtom? iso target strategy
    | _ => none

/-- Refine every component of a one-atom search round. A certified cluster is
    re-entered through its tighter certified region when that makes progress;
    otherwise it, and every failed component, is subdivided locally. -/
@[expose] def nextAtomSearch {p : ZPoly}
    (tried : Array (Component × Option (Certified p))) : Array Component :=
  tried.flatMap fun t => match t with
    | (c, some result) =>
      let c' := result.toComponent
      if c.prec < c'.prec then #[c'] else c.refine1 p
    | (c, none) => c.refine1 p

/-- Search a caller-selected region for one certified simple root, then refine
    that atom to `target`. Unlike `isolateLoop`, this loop does not construct a
    complete, pairwise-disjoint family: an atom certificate already states
    that its own region contains exactly one simple root. Consequently a
    successful result is sound without examining or refining any other root.
    `none` means the region was exhausted or no atom was found within fuel. -/
@[expose] def findAtomLoop (p : ZPoly) (target : Int)
    (strategy : AtomStrategy) :
    Nat → Array Component → Option (DyadicRootIsolation p)
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then none else
    let tried := IsolationLoop.attempts p strategy work
    match firstRefinedAtom? target strategy tried with
    | some iso => some iso
    | none => findAtomLoop p target strategy fuel (nextAtomSearch tried)

namespace IsolationLoop

/-- Refine the atom returned by one successful component attempt. -/
@[expose] def refineAttempt? {p : ZPoly} (target : Int)
    (strategy : AtomStrategy) (t : Component × Option (Certified p)) :
    Option (DyadicRootIsolation p) :=
  match t.2 with
  | some (.atom iso) => refineAtom? iso target strategy
  | _ => none

/-- Strategy-parametric implementation of the all-atoms finishing pass. -/
@[expose] def finishAllAtoms? (p : ZPoly) (target : Int)
    (strategy : AtomStrategy)
    (tried : Array (Component × Option (Certified p))) :
    Option (Array (Certified p)) :=
  if allAtoms tried && disjoint tried then
    match tried.mapM (refineAttempt? target strategy) with
    | none => none
    | some atoms =>
      if pairwiseDisjoint (atoms.map (·.square)) then
        some (atoms.map Certified.atom)
      else none
  else none

/-- Opportunistically refine every successful atom to the requested target.
The nested work starts only when every attempt is an atom and the current
discs are pairwise disjoint; the result is accepted only when every local
refinement succeeds and the refined discs remain pairwise disjoint. The
NK-only strategy keeps its existing proof-specialized loop path. -/
@[expose] def finishAtoms? (p : ZPoly) (target : Int) (strategy : AtomStrategy)
    (tried : Array (Component × Option (Certified p))) :
    Option (Array (Certified p)) :=
  match strategy with
  | .nk => none
  | .pellet | .nkThenPellet => finishAllAtoms? p target strategy tried

/-- Ordinary output guard after the optional local finisher. Normalized
worklists may emit any ready, disjoint certificates. The NK-only strategy also
retains its historical early all-atoms emission; Pellet-bearing strategies use
the stronger local finisher above. -/
@[expose] def emitReady {p : ZPoly} (target : Int) (strategy : AtomStrategy)
    (tried : Array (Component × Option (Certified p))) : Bool :=
  (normalized p target tried || match strategy with
    | .nk => allAtoms tried
    | .pellet | .nkThenPellet => false) &&
    (allReady target tried && disjoint tried)

end IsolationLoop

/-- The shared driver loop over the worklist. It may emit before
    `completenessDepth` when every result is already an atom and target-ready,
    with pairwise-disjoint discs. Before
    that depth, every non-emitting round globally refines and reglues the
    retained squares, irrespective of attempted certificates. At and beyond
    that depth, ready and disjoint cluster results may emit too. Otherwise: a
    component already certified at target whose disc
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
    suffice. `fuel = 0` returns `none` (up to a
    harmless constant of overshoot). The recursion is structural on the
    fuel `Nat`. -/
@[expose] def isolateLoop (p : ZPoly) (target : Int) (strategy : AtomStrategy) :
    Nat → Array Component → Option (Array (Certified p))
  | 0, _ => none
  | fuel + 1, work =>
    if work.isEmpty then some #[] else
    let tried := IsolationLoop.attempts p strategy work
    match IsolationLoop.finishAtoms? p target strategy tried with
    | some rs => some rs
    | none =>
      if IsolationLoop.emitReady target strategy tried then
        some (IsolationLoop.outputs tried)
      else
        -- A component whose certification already meets the target and whose
        -- disc is disjoint from every other certified disc holds its position
        -- (re-entering unchanged) while the laggards catch up.
        isolateLoop p target strategy fuel <|
          IsolationLoop.next p target tried

/-- Refine to `target` precision. A bounded lineage-local pass preserves the
usual logarithmic speculative-Newton path. If it does not produce exactly one
target-ready atom, refinement restarts from the input under the globally
reglued complete loop. -/
@[expose] def DyadicRootIsolation.refineTo? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option (DyadicRootIsolation p) :=
  if target ≤ iso.square.prec then some iso else
  match refineFastAtom? iso target strategy with
  | some iso' => some iso'
  | none => refineAtom? iso target strategy

end Hex
