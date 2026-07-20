/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Newton
public import HexRoots.Kantorovich

public section

/-!
Four-way subdivision, the `T₀` discard, and component gluing: the
worklist operations of the complex root isolator. `Component.refine1`
splits every square of a component into four children one bit finer,
discards children whose disc certifiably contains no root, and glues the
survivors back into edge-or-corner-connected components; it is total, requiring no
certification. `Component.certify?` tries to certify a component, first
by the Newton-Kantorovich atom witness on the doubled enclosing square
(with a speculative Newton recentring attempted first under the coverage
guard), then by the Pellet witness on a quadrupled enclosing square.

The geometry helpers `DyadicSquare.subdivide`, `DyadicSquare.adjacent`,
and `glue` are exact: subdivision offsets by exact dyadics, adjacency is
a comparison of exact dyadic centre differences, and gluing folds squares
into a component partition, merging every component touched by the new
square. Corner adjacency is included: at the completeness depth every
retained square is at most one king move from the square containing its
associated root.
The witness re-checks for certification and the coverage guard run at runtime
on the compiled code; the `decide`-reducible witness
predicates themselves live in `Pellet.lean` and `Kantorovich.lean`.
-/
namespace Hex

/-- The four children of `s`, one bit finer, in a fixed order
    (SW, SE, NW, NE). They partition `s`: each child has half-width
    `2^{−(prec+1)}` and centre offset by that half-width from `s`'s
    centre along each axis. -/
@[expose] def DyadicSquare.subdivide (s : DyadicSquare) : Array DyadicSquare :=
  let q := s.prec + 1
  let h : Dyadic := .ofIntWithPrec 1 q
  #[⟨s.re - h, s.im - h, q⟩, ⟨s.re + h, s.im - h, q⟩,
    ⟨s.re - h, s.im + h, q⟩, ⟨s.re + h, s.im + h, q⟩]

/-- Edge-or-corner adjacency of two same-`prec` grid squares, by exact
dyadic centre differences. Centres must be less than four half-widths apart
on both axes. On a common subdivision grid the centre
spacing is two half-widths, so this is exactly one king move; the geometric
form also handles translated grids without a lattice-origin side condition. -/
@[expose] def DyadicSquare.adjacent (s t : DyadicSquare) : Bool :=
  if s.prec = t.prec then
    let fourH : Dyadic := .ofIntWithPrec 1 (s.prec - 2) -- 4·2^{−prec}
    let dre := Hex.Dyadic.abs (s.re - t.re)
    let dim := Hex.Dyadic.abs (s.im - t.im)
    decide (dre < fourH) && decide (dim < fourH)
  else
    false

/-- Whether a square touches some member of a partial glued component. -/
@[expose] def DyadicSquare.touches (s : DyadicSquare)
    (component : List DyadicSquare) : Bool :=
  component.any fun t => s.adjacent t || t.adjacent s

/-- Insert one square into a component partition. Every component touched by
the new square is merged with it; untouched components retain their order. -/
@[expose] def glueInsert (s : DyadicSquare)
    (components : List (List DyadicSquare)) : List (List DyadicSquare) :=
  let (touching, separate) := components.partition s.touches
  (s :: touching.flatten) :: separate

/-- Edge-or-corner-connected components of a list of squares. This union-by-insertion
form makes coverage, connectedness, and maximality structural induction
invariants while retaining the `O(m²)` adjacency complexity. -/
@[expose] def glueList : List DyadicSquare → List (List DyadicSquare)
  | [] => []
  | s :: sqs => glueInsert s (glueList sqs)

/-- Edge-or-corner-connected components of an array of squares. -/
@[expose] def glue (sqs : Array DyadicSquare) : Array (Array DyadicSquare) :=
  (glueList sqs.toList).map List.toArray |>.toArray

/-- Connected-component gluing with an executable coverage guard. The normal
`glue` result is used when every input square occurs in an output component;
the defensive fallback returns singleton components. The Mathlib companion
proves the structural `glueList` implementation always passes this guard, so
the fallback is unreachable in the current implementation. -/
@[expose] def glueCovered (sqs : Array DyadicSquare) : Array (Array DyadicSquare) :=
  let cs := glue sqs
  if ∀ s ∈ sqs.toList, ∃ c ∈ cs.toList, s ∈ c.toList then
    cs
  else
    sqs.map (#[·])

namespace Component

/-- One subdivision round: split every square into four children one bit
    finer, discard children whose disc certifiably contains no root (the
    `T₀` test; a child whose `T₀` test fails to certify is kept, which is
    always sound), and glue the survivors into edge-or-corner-connected
    components.
    Total: no certification is required during refinement. -/
@[expose] def refine1 (p : ZPoly) (c : Component) : Array Component :=
  let survivors := (c.squares.flatMap DyadicSquare.subdivide).filter
    (fun s => !rootFree p s)
  (glueCovered survivors).map fun ss => { squares := ss, candidateK := c.candidateK }

/-- One globally normalized subdivision round. All component squares are
subdivided, filtered, and glued together. The root-count hint is reset to
one; it affects attempt order only, and every candidate is rechecked.

The isolation driver uses this operation until its completeness depth. Thus
all Cauchy-started survivors remain on one common grid, and components that
approach the same root can rejoin even if an earlier round separated their
lineages. -/
@[expose] def refineAll (p : ZPoly) (work : Array Component) : Array Component :=
  let squares := work.flatMap (·.squares)
  let survivors := (squares.flatMap DyadicSquare.subdivide).filter
      (fun s => !rootFree p s)
  (glueCovered survivors).map fun ss => { squares := ss, candidateK := 1 }

/-- Attempt Pellet certification for one positive candidate count, including
the same-count speculative Newton jump and its disc-containment guard. -/
@[expose] def certifyPelletAt? (p : ZPoly) (c : Component)
    (k : Nat) : Option (Certified p) :=
  let enc := encSquare c.squares
  if hk : 0 < k then
    if hw : witnessCheck p enc k = true then
      let cluster : DyadicRootCluster p := ⟨c.squares, k, hk, hw⟩
      let base : Certified p :=
        if hk1 : k = 1 then .atom (cluster.atomize hk1) else .cluster cluster
      let s' := newtonSquare p enc k
      if _hins : (encSquare #[s']).discInside enc = true then
        if hw' : witnessCheck p (encSquare #[s']) k = true then
          let cluster' : DyadicRootCluster p := ⟨#[s'], k, hk, hw'⟩
          if hk1 : k = 1 then some (.atom (cluster'.atomize hk1))
          else some (.cluster cluster')
        else some base
      else some base
    else none
  else none

/-- First successful Pellet certificate in a candidate-count list. -/
@[expose] def certifyPelletList? (p : ZPoly) (c : Component)
    : List Nat → Option (Certified p)
  | [] => none
  | k :: ks => (certifyPelletAt? p c k).orElse
      fun _ => certifyPelletList? p c ks

/-- The Pellet half of component certification, factored from `certify?` so
its base and speculative same-count branches have a narrow correspondence
theorem in the Mathlib companion. -/
@[expose] def certifyPellet? (p : ZPoly) (c : Component) : Option (Certified p) :=
  let deg := p.degree?.getD 0
  let ks := #[c.candidateK] ++ ((Array.range (deg + 1)).filter (· != c.candidateK))
  certifyPelletList? p c ks.toList

/-- Try to certify the component. Per `strategy`, first the
    Newton-Kantorovich atom witness on the doubled enclosing square (with a
    speculative Newton recentring attempted first), then the Pellet witness
    on a quadrupled enclosing square with `k = candidateK` first and then the
    remaining `k ≤ deg p`; a `k = 1` Pellet success is returned as an atom
    via `atomize`. Speculative Newton results are accepted only under the
    coverage guard: the base region must certify the same count in the same
    certificate form, and the recentred certified region must be contained
    in the base one. -/
@[expose] def certify? (p : ZPoly) (strategy : AtomStrategy := .nkThenPellet)
    (c : Component) : Option (Certified p) := Id.run do
  let enc := encSquare c.squares
  -- Newton-Kantorovich attempt, on the doubled enclosing square.
  match strategy with
  | .nk | .nkThenPellet =>
    let base := enc.doubled
    if h : nkWitnessCheck p base = true then
      -- `base` certifies; try to sharpen with a speculative Newton jump,
      -- accepted only when the recentred square stays inside `base` and
      -- certifies in the same (NK) form.
      let cand := (newtonSquare p base 1).doubled
      if cand.squareInside base = true then
        if h' : nkWitnessCheck p cand = true then
          return some (.atom ⟨cand, Or.inl h'⟩)
      return some (.atom ⟨base, Or.inl h⟩)
  | .pellet => pure ()
  -- Pellet attempt, on a quadrupled enclosing square. The original component
  -- lies in its central quarter, giving the converse theorem a uniform
  -- recentering margin independent of the root's leaf-grid position.
  match strategy with
  | .pellet | .nkThenPellet =>
    let wide : Component :=
      { squares := #[enc.doubled.doubled], candidateK := c.candidateK }
    return certifyPellet? p wide
  | .nk => pure ()
  return none

end Component

end Hex
