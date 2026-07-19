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
survivors back into edge-connected components; it is total, requiring no
certification. `Component.certify?` tries to certify a component, first
by the Newton-Kantorovich atom witness on the doubled enclosing square
(with a speculative Newton recentring attempted first under the coverage
guard), then by the Pellet witness on the enclosing square's disc.

The geometry helpers `DyadicSquare.subdivide`, `DyadicSquare.adjacent`,
and `glue` are exact: subdivision offsets by exact dyadics, adjacency is
a comparison of exact dyadic centre differences, and gluing is a
fuel-bounded depth-first search with mark-before-push, so each index is
visited once and the output components are deterministic in index order.
The witness re-checks that certification and the coverage guard perform
run at runtime on the compiled code; the `decide`-reducible witness
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

/-- Edge adjacency of two same-`prec` grid squares, by exact dyadic centre
    differences: the centres differ by exactly `2·2^{−prec}` on one axis
    and `0` on the other. Works for translated grids (Newton lineages)
    because gluing only ever compares children of one component's squares,
    which share a grid. -/
@[expose] def DyadicSquare.adjacent (s t : DyadicSquare) : Bool :=
  if s.prec = t.prec then
    let twoH : Dyadic := .ofIntWithPrec 1 (s.prec - 1)   -- 2·2^{−prec}
    let dre := Hex.Dyadic.abs (s.re - t.re)
    let dim := Hex.Dyadic.abs (s.im - t.im)
    (decide (dre = twoH) && decide (dim = 0))
      || (decide (dre = 0) && decide (dim = twoH))
  else
    false

/-- Edge-connected components of a set of same-`prec` squares. Depth-first
    (stack-based) search with mark-before-push (each index is pushed at most once, so
    `n+1` pop rounds of fuel suffice); the output is deterministic in index
    order. `O(m²)` adjacency scans. -/
@[expose] def glue (sqs : Array DyadicSquare) : Array (Array DyadicSquare) := Id.run do
  let n := sqs.size
  let mut seen : Array Bool := Array.replicate n false
  let mut result : Array (Array DyadicSquare) := #[]
  for i in [0:n] do
    if !(seen.getD i false) then
      let mut comp : Array DyadicSquare := #[]
      let mut stack : Array Nat := #[i]
      seen := seen.setIfInBounds i true
      for _ in [0:n+1] do
        match stack.back? with
        | none => break
        | some cur =>
          stack := stack.pop
          let curSq := sqs.getD cur ⟨0, 0, 0⟩
          comp := comp.push curSq
          for j in [0:n] do
            if !(seen.getD j false) && curSq.adjacent (sqs.getD j ⟨0, 0, 0⟩) then
              seen := seen.setIfInBounds j true
              stack := stack.push j
      result := result.push comp
  return result

/-- Connected-component gluing with an executable coverage guard. The normal
`glue` result is used when every input square occurs in an output component;
the defensive fallback returns singleton components. This preserves coverage
and makes every fallback component trivially connected, but does not preserve
the maximal connected grouping if the imperative DFS is ever changed
incorrectly. -/
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
    always sound), and glue the survivors into edge-connected components.
    Total: no certification is required during refinement. -/
@[expose] def refine1 (p : ZPoly) (c : Component) : Array Component :=
  let survivors := (c.squares.flatMap DyadicSquare.subdivide).filter
    (fun s => !rootFree p s)
  (glueCovered survivors).map fun ss => { squares := ss, candidateK := c.candidateK }

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
    on the enclosing square's disc with `k = candidateK` first and then the
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
  -- Pellet attempt, on the enclosing square's disc.
  match strategy with
  | .pellet | .nkThenPellet =>
    return certifyPellet? p c
  | .nk => pure ()
  return none

end Component

end Hex
