/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Refine
public import HexRoots.SimpleRoot

public section

/-!
The end-to-end drivers `isolateAll?`, `isolate`, and `isolateOne?`, thin
wrappers over the shared refinement loops.

`isolateAll?` globally refines and reglues an arbitrary worklist through
`completenessDepth`, then continues until every component certifies at prec
at least `target` with pairwise disjoint circumscribed discs. It sizes the
fuel from the worklist's coarsest prec so the loop reaches
`stopDepth p target` before giving up. `isolate` is the all-atoms driver for
polynomials with only simple roots: it starts from `Component.cauchy`, uses
`target := max atom_prec (separationDepth p)`, and requires every result to
be an atom, pinning the degenerate inputs (nonzero constant to `some #[]`,
zero polynomial to `none`).

`isolateOne?` starts its search from a caller-selected square and returns the
first atom found, refined only to the precision needed by `SimpleRoot`. Its
atom certificate says that one region contains exactly one simple root, so it
does not pay for a complete pairwise-disjoint family. The returned atom need
not remain inside the seed: subdivision retains squares whose tests cannot yet
discard them, and certification uses their circumscribed discs.
-/
namespace Hex

/-- Extract an atom from a certified result, failing on clusters. -/
@[expose] def Certified.asAtom? {p : ZPoly} : Certified p →
    Option (DyadicRootIsolation p)
  | .atom iso => some iso
  | .cluster _ => none

/-- Refine every component to precision at least `target` and require the
circumscribed discs of the certified squares to be pairwise disjoint. Before
`completenessDepth`, refinement is global so rootless survivor halos rejoin the
root-bearing component. The fuel is sized from the worklist's coarsest
precision so the loop reaches `stopDepth p target`. `none` means the full
emission condition was not reached within that fuel bound. -/
@[expose] def isolateAll? (p : ZPoly) (target : Int) (worklist : Array Component)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (Certified p)) :=
  let start := worklist.foldl (fun m c => min m c.prec)
    ((worklist[0]?.map (·.prec)).getD 0)
  isolateLoop p target strategy (fuelFor p target start) worklist

/-- All-atoms output for polynomials with only simple roots: run
    {name}`Hex.isolateAll?` from {name}`Hex.Component.cauchy` with
    `target := max atom_prec (separationDepth p)`, and require every result to
    be an atom. `none` if {name}`Hex.isolateAll?` fails or (impossible for squarefree
    `p`, proven in the companion) some result is a `k ≥ 2` cluster.
    {name}`Hex.HasOnlySimpleRoots` does not force positive degree, so the degenerate
    inputs are pinned here: a nonzero constant returns `some #[]` (no roots to
    isolate), and the zero polynomial returns `none`. -/
@[expose] def isolate (p : ZPoly) (_h : HasOnlySimpleRoots p) (atom_prec : Int)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (DyadicRootIsolation p)) :=
  if hd : 0 < p.degree?.getD 0 then
    let target := max atom_prec (separationDepth p : Int)
    (isolateAll? p target #[Component.cauchy p hd] strategy).bind fun rs =>
      rs.mapM Certified.asAtom?
  else if p.size = 0 then none else some #[]

/-- Start a local search for one simple root from a caller-selected square and
    refine its atom to at
    least `max atomPrec (mahlerPrec p)`. This is a deliberately local search:
    unlike {name}`Hex.isolate`, it neither certifies every root nor establishes
    pairwise disjointness against roots outside the returned atom. The
    self-contained {name}`Hex.AtomCertificate` is exactly the weaker fact
    needed by {name}`Hex.SimpleRoot.mk`. The returned atom is not promised to
    lie inside `seed`; `seed` selects the initial search region. `none` means
    the search was exhausted or the bounded search did not find an atom. -/
@[expose] def isolateOne? (p : ZPoly) (atomPrec : Int) (seed : DyadicSquare)
    (strategy : AtomStrategy := .nkThenPellet) : Option (RefinedIsolation p) := do
  let target := max atomPrec (mahlerPrec p : Int)
  let iso ← findAtomLoop p target strategy (fuelFor p target seed.prec)
    #[{ squares := #[seed], candidateK := 1 }]
  iso.toRefined?

/-- Refine a refined isolation, staying in the refined type and returning
    the proof that the result isolates the same root. The refinement target
    is floored at `mahlerPrec p` so the subtype re-wrap always succeeds on a
    `some`, and the identity proof comes from the decidable `Intersects`
    re-check via `Quot.sound`. This is the threading-pattern operation the
    `SimpleRoot` module docstring describes: refine once, store the returned
    representative, and substitute it wherever the original was used. -/
@[expose] def RefinedIsolation.refineTo? {p : ZPoly} (r : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    Option {r' : RefinedIsolation p // SimpleRoot.mk r' = SimpleRoot.mk r} := do
  let iso' ← r.1.refineTo? (max target (mahlerPrec p : Int)) strategy
  if h : (mahlerPrec p : Int) ≤ iso'.square.prec then
    let r' : RefinedIsolation p := ⟨iso', h⟩
    if hI : Intersects r' r then
      some ⟨r', Quot.sound hI⟩
    else none
  else none

end Hex
