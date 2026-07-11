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
The end-to-end drivers `isolateAll?` and `isolate`, thin wrappers over the
shared `isolateLoop`.

`isolateAll?` refines an arbitrary worklist until every component certifies
at prec at least `target` with pairwise disjoint circumscribed discs, sizing
the fuel from the worklist's coarsest prec so the loop reaches
`stopDepth p target` before giving up. `isolate` is the all-atoms driver for
polynomials with only simple roots: it starts from `Component.cauchy`, uses
`target := max atom_prec (separationDepth p)`, and requires every result to
be an atom, pinning the degenerate inputs (nonzero constant to `some #[]`,
zero polynomial to `none`).
-/
namespace Hex

/-- Refine every component until certified at prec at least `target`, with
    the certified stored squares' circumscribed discs pairwise disjoint (SPEC
    "Separation of the output"). The fuel is sized from the worklist's
    coarsest prec so the loop reaches `stopDepth p target`. `none` only if
    certification with disjoint discs has not happened by that depth. -/
def isolateAll? (p : ZPoly) (target : Int) (worklist : Array Component)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (Certified p)) :=
  let start := worklist.foldl (fun m c => min m c.prec)
    ((worklist[0]?.map (·.prec)).getD 0)
  isolateLoop p target strategy (fuelFor p target start) worklist

/-- All-atoms output for polynomials with only simple roots: run
    `isolateAll?` from `Component.cauchy` with
    `target := max atom_prec (separationDepth p)`, and require every result to
    be an atom. `none` if `isolateAll?` fails or (impossible for squarefree
    `p`, proven in the companion) some result is a `k ≥ 2` cluster.
    `HasOnlySimpleRoots` does not force positive degree, so the degenerate
    inputs are pinned here: a nonzero constant returns `some #[]` (no roots to
    isolate), and the zero polynomial returns `none`. -/
def isolate (p : ZPoly) (h : HasOnlySimpleRoots p) (atom_prec : Int)
    (strategy : AtomStrategy := .nkThenPellet) :
    Option (Array (DyadicRootIsolation p)) :=
  if hd : 0 < p.degree?.getD 0 then
    let target := max atom_prec (separationDepth p : Int)
    (isolateAll? p target #[Component.cauchy p hd] strategy).bind fun rs =>
      rs.mapM fun r => match r with
        | .atom iso => some iso
        | .cluster _ => none
  else if p.size = 0 then none else some #[]

/-- Refine a refined isolation, staying in the refined type and returning
    the proof that the result isolates the same root. The refinement target
    is floored at `mahlerPrec p` so the subtype re-wrap always succeeds on a
    `some`, and the identity proof comes from the decidable `Intersects`
    re-check via `Quot.sound`. This is the threading-pattern operation the
    `SimpleRoot` module docstring describes: refine once, store the returned
    representative, and substitute it wherever the original was used. -/
def RefinedIsolation.refineTo? {p : ZPoly} (r : RefinedIsolation p)
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
