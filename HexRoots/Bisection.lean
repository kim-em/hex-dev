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

/-- Attempt Pellet certification for one positive candidate count from the
    cached Taylor shift at the component's enclosing-square centre. The proof
    argument ties the cache to that centre; it is erased from compiled code. -/
@[expose] def certifyPelletAtShift? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center)
    (k : Nat) : Option (Certified p) :=
  let enc := encSquare c.squares
  if hk : 0 < k then
    if hw : TaylorShift.combinedWitnessCheck enc shift k = true then
      have hw₀ : witnessCheck p enc k = true := by
        simpa using hw
      let cluster : DyadicRootCluster p := ⟨c.squares, k, hk, hw₀⟩
      let base : Certified p :=
        if hk1 : k = 1 then .atom (cluster.atomize hk1) else .cluster cluster
      let s' := TaylorShift.newtonSquare enc shift k
      if _hins : (encSquare #[s']).discInside enc = true then
        let cand := encSquare #[s']
        let shift' := TaylorShift.compute p cand.center
        if hw' : TaylorShift.combinedWitnessCheck cand shift' k = true then
          have hw₀' : witnessCheck p cand k = true := by
            simpa using hw'
          let cluster' : DyadicRootCluster p := ⟨#[s'], k, hk, hw₀'⟩
          if hk1 : k = 1 then some (.atom (cluster'.atomize hk1))
          else some (.cluster cluster')
        else some base
      else some base
    else none
  else none

/-- Build a certificate directly from the first all-count soft Graeffe
candidate.  The threshold keeps bounded-precision setup off the small-degree
path where the exact dyadic kernel is already cheaper. -/
@[expose] def certifyPelletSoft? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center)
    (ks : List Nat) : Option (Certified p) :=
  let enc := encSquare c.squares
  if 32 ≤ p.size && 8 ≤ enc.prec then
    match h : shift.softRefinementCandidate? enc ks with
    | none => none
    | some k =>
      have hpublic : softRefinementCandidate? p enc ks = some k := by
        rw [← shift.softRefinementCandidate?_eq enc ks]
        exact h
      have hs := softRefinementCandidate?_sound hpublic
      have hs' : (TaylorShift.compute p enc.center).softWitnessCheck enc k = true := by
        rw [TaylorShift.softWitnessCheck_eq]
        exact hs.2
      have hw : witnessCheck p enc k = true := by
        by_cases hprec : enc.prec < 32 <;>
          simp [witnessCheck, TaylorShift.combinedWitnessCheck, hprec, hs']
      let cluster : DyadicRootCluster p := ⟨c.squares, k, hs.1, hw⟩
      if hk1 : k = 1 then some (.atom (cluster.atomize hk1))
      else some (.cluster cluster)
  else none

/-- Exact cached-Taylor certification for one count, used after the all-count
soft search has failed. -/
@[expose] def certifyPelletExactAt? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center)
    (k : Nat) : Option (Certified p) :=
  let enc := encSquare c.squares
  if hk : 0 < k then
    if hw : TaylorShift.witnessCheck enc shift k = true then
      have hw₀ : witnessCheck p enc k = true :=
        TaylorShift.witnessCheck_implies enc shift k hw
      let cluster : DyadicRootCluster p := ⟨c.squares, k, hk, hw₀⟩
      let base : Certified p :=
        if hk1 : k = 1 then .atom (cluster.atomize hk1) else .cluster cluster
      let s' := TaylorShift.newtonSquare enc shift k
      if _hins : (encSquare #[s']).discInside enc = true then
        let cand := encSquare #[s']
        let shift' := TaylorShift.compute p cand.center
        if hw' : TaylorShift.witnessCheck cand shift' k = true then
          have hw₀' : witnessCheck p cand k = true :=
            TaylorShift.witnessCheck_implies cand shift' k hw'
          let cluster' : DyadicRootCluster p := ⟨#[s'], k, hk, hw₀'⟩
          if hk1 : k = 1 then some (.atom (cluster'.atomize hk1))
          else some (.cluster cluster')
        else some base
      else some base
    else none
  else none

/-- Public one-count Pellet attempt. It computes the enclosing-centre Taylor
    shift once and passes it to the cached implementation. -/
@[expose] def certifyPelletAt? (p : ZPoly) (c : Component)
    (k : Nat) : Option (Certified p) :=
  let shift := TaylorShift.compute p (encSquare c.squares).center
  certifyPelletAtShift? p c shift k

/-- First exact Pellet certificate in a candidate-count list, reusing one
enclosing-centre Taylor shift for every failed count. -/
@[expose] def certifyPelletExactList? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center)
    : List Nat → Option (Certified p)
  | [] => none
  | k :: ks => (certifyPelletExactAt? p c shift k).orElse
      fun _ => certifyPelletExactList? p c shift ks

/-- First soft all-count certificate. On success, rerun its single selected
count through the cached-shift certifier so the guarded Newton candidate is
reused instead of returning the coarse soft base square. Failure falls back
to the exact cached list. -/
@[expose] def certifyPelletListShift? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center)
    (ks : List Nat) : Option (Certified p) :=
  match certifyPelletSoft? p c shift ks with
  | some (.atom _) => certifyPelletAtShift? p c shift 1
  | some (.cluster cl) => certifyPelletAtShift? p c shift cl.k
  | none => certifyPelletExactList? p c shift ks

/-- Public candidate-count search. The exact Taylor shift is shared by every
    attempt; only a successful count's speculative candidate needs a new
    shift for its witness recheck. -/
@[expose] def certifyPelletList? (p : ZPoly) (c : Component)
    (ks : List Nat) : Option (Certified p) :=
  let shift := TaylorShift.compute p (encSquare c.squares).center
  certifyPelletListShift? p c shift ks

/-- The Pellet half of component certification using a supplied shift. -/
@[expose] def certifyPelletShift? (p : ZPoly) (c : Component)
    (shift : TaylorShift p (encSquare c.squares).center) : Option (Certified p) :=
  let deg := p.degree?.getD 0
  let ks := #[c.candidateK] ++ ((Array.range (deg + 1)).filter (· != c.candidateK))
  certifyPelletListShift? p c shift ks.toList

/-- The public Pellet half of component certification. This proof-facing
    compatibility surface computes its own shift; `certify?` supplies the
    already-cached shift to `certifyPelletShift?`. -/
@[expose] def certifyPellet? (p : ZPoly) (c : Component) : Option (Certified p) :=
  let deg := p.degree?.getD 0
  let ks := #[c.candidateK] ++ ((Array.range (deg + 1)).filter (· != c.candidateK))
  certifyPelletList? p c ks.toList

/-- Try to certify the component. For Pellet-enabled strategies, run the
    all-count bounded-precision Graeffe filter before the exact candidate
    fallback. Share one exact shift between the
    Newton-Kantorovich atom witness and the exact Pellet fallback. Pellet uses
    a quadrupled enclosing square with `k = candidateK` first and then the
    remaining `k ≤ deg p`; a `k = 1` Pellet success is returned as an atom
    via `atomize`. Speculative Newton results are accepted only under the
    coverage guard: the base region must certify the same count in the same
    certificate form, and the recentred certified region must be contained
    in the base one. -/
@[expose] def certify? (p : ZPoly) (strategy : AtomStrategy := .nkThenPellet)
    (c : Component) : Option (Certified p) := Id.run do
  let enc := encSquare c.squares
  let shift := TaylorShift.compute p enc.center
  -- Newton-Kantorovich attempt, on the doubled enclosing square.
  match strategy with
  | .nk | .nkThenPellet =>
    let base := enc.doubled
    let baseShift : TaylorShift p base.center := shift.cast (by rfl)
    if h : TaylorShift.nkWitnessCheck base baseShift = true then
      have h₀ : nkWitnessCheck p base = true := by
        rw [TaylorShift.nkWitnessCheck_eq] at h
        exact h
      -- `base` certifies; try to sharpen with a speculative Newton jump,
      -- accepted only when the recentred square stays inside `base` and
      -- certifies in the same (NK) form.
      let cand := (TaylorShift.newtonSquare base baseShift 1).doubled
      if cand.squareInside base = true then
        let shift' := TaylorShift.compute p cand.center
        if h' : TaylorShift.nkWitnessCheck cand shift' = true then
          have h₀' : nkWitnessCheck p cand = true := by
            rw [TaylorShift.nkWitnessCheck_eq] at h'
            exact h'
          return some (.atom ⟨cand, Or.inl h₀'⟩)
      return some (.atom ⟨base, Or.inl h₀⟩)
  | .pellet => pure ()
  -- Pellet attempt, on a quadrupled enclosing square. The original component
  -- lies in its central quarter, giving the converse theorem a uniform
  -- recentering margin independent of the root's leaf-grid position.
  match strategy with
  | .pellet | .nkThenPellet =>
    let wide : Component :=
      { squares := #[enc.doubled.doubled], candidateK := c.candidateK }
    let wideCenter := (encSquare wide.squares).center
    let wideShift : TaylorShift p wideCenter :=
      if hcenter : enc.center = wideCenter then shift.cast hcenter
      else TaylorShift.compute p wideCenter
    let deg := p.degree?.getD 0
    let ks := #[wide.candidateK] ++
      ((Array.range (deg + 1)).filter (· != wide.candidateK))
    return certifyPelletListShift? p wide wideShift ks.toList
  | .nk => pure ()
  return none

end Component

end Hex
