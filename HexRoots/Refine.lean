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
def Certified.toComponent {p : ZPoly} : Certified p → Component
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

/-- The shared driver loop over the worklist. Each round certifies every
    component; if all certify at stored prec at least `target` with pairwise
    disjoint circumscribed discs (SPEC "Separation of the output"), the round
    emits them. Otherwise: a component already certified at target whose
    disc is disjoint from every other certified disc holds its position;
    every other surviving component subdivides one level, except that one
    adopting a strictly finer certified result keeps that result as a
    one-square component instead. Each non-emitting round strictly
    increases every non-held component's prec, and held components are at
    target already, so the laggard's prec still reaches `stopDepth` within
    the fuel; the loop recurses on the smaller fuel. `fuel = 0` returns `none`, the SPEC give-up
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
      -- A component whose certification already meets the target and whose
      -- disc is disjoint from every other certified disc holds its position
      -- (re-entering unchanged) while the laggards catch up; only
      -- disjointness violators and unready components keep refining (SPEC
      -- "Separation of the output"). Without the hold, a waiting component
      -- would keep adopting Newton results, doubling its precision every
      -- round and blowing the working bit-length while a slow sibling
      -- (e.g. a tight cluster forced down to its separation depth)
      -- subdivides.
      let certSquares := tried.map fun t => t.2.map (·.square)
      isolateLoop p target strategy fuel <|
        (Array.range tried.size).flatMap fun i =>
          match tried.getD i (⟨#[], 0⟩, none) with
          | (c, some res) =>
            let ready := target ≤ res.square.prec
            let overlaps := (Array.range tried.size).any fun j =>
              i ≠ j && (match certSquares.getD j none with
                        | some sj => res.square.discsMeet sj
                        | none => false)
            if ready && !overlaps then #[c]
            else
              let c' := res.toComponent
              if c.prec < c'.prec then #[c'] else c.refine1 p
          | (c, none) => c.refine1 p

/-- Refine to `target` precision: speculative Newton steps, falling back to
    subdivision of the atom's square as a one-square component. `none` only
    if certification has not reappeared by `stopDepth p target`. -/
def DyadicRootIsolation.refineTo? {p : ZPoly} (iso : DyadicRootIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option (DyadicRootIsolation p) :=
  if target ≤ iso.square.prec then some iso else
  let fuel := (stopDepth p target - iso.square.prec).toNat + 1
  match isolateLoop p target strategy fuel #[⟨#[iso.square.doubled], 1⟩] with
  | some rs =>
    if rs.size = 1 then
      match rs[0]? with
      | some (Certified.atom iso') => some iso'
      | _ => none
    else none
  | none => none

end Hex
