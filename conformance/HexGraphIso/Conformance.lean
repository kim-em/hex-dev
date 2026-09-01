/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso

/-!
Core conformance for `HexGraphIso`.

- **Oracle:** `scripts/oracle/graphiso_nauty.py` (pinned external
  nauty 2.9.3 through the project-owned shim), over the committed fixture
  `conformance-fixtures/HexGraphIso/graphiso.jsonl` emitted by
  `HexGraphIso.EmitFixtures`. This module is the Lean-only `core`
  profile.
- **Mode:** `required` for the external leg in release CI
  (`HEX_REQUIRE_ORACLES=1`); this module itself has no external
  dependency.
- **Covered operations:** `Graph.ofEdges?`, `Graph.relabel`,
  `Perm.ofVector?`/`inv`/`comp`, `Label` round trips,
  `Coloring.ofVector?`, `Colored.relabel`, `checkIso`, `isIso`,
  `findIso`, `findIso?`, `checkIso?`, `canon?`, `canonicalize`, `canon`,
  `label`, `Reference.canon`, `Nauty.runColored`, `Nauty.canonicalize?`.
- **Covered properties:** builder rejection and duplicate collapse;
  permutation inverse and composition laws; `relabel G (label G) =
  canon G` evaluated on committed inputs; canonical-form invariance
  under committed relabellings; colour-cell contiguity of canonical
  forms; verdict agreement between the reference implementation and the
  nauty-compatible search; found transporters accepted by `checkIso`;
  exhaustion returning `none`, never `false`.
- **Covered edge cases:** the empty graph (`n = 0`, `k = 0`), a single
  vertex, discrete and one-cell colourings, complete and empty graphs,
  duplicate and reversed edges in the builder, out-of-range and loop
  edges rejected, zero search and replay limits.
-/

namespace Hex.GraphIso.Conformance

open Hex Hex.GraphIso

/-! # Builder -/

#guard (Graph.ofEdges? 3 [(0, 1), (1, 2)]).isSome
#guard (Graph.ofEdges? 3 [(0, 3), (1, 2)]).isNone          -- out of range
#guard (Graph.ofEdges? 3 [(1, 1)]).isNone                  -- loop
#guard (Graph.ofEdges? 0 []).isSome                        -- empty graph
-- duplicate and reversed edges collapse
#guard
  (Graph.ofEdges? 3 [(0, 1), (1, 0), (0, 1)]) == (Graph.ofEdges? 3 [(0, 1)])

private def p3 : Colored 3 1 :=
  { graph := (Graph.ofEdges? 3 [(0, 1), (1, 2)]).getD (Graph.empty 3)
    coloring := Coloring.trivial 3 (by omega) }

private def p3' : Colored 3 1 :=
  { graph := (Graph.ofEdges? 3 [(0, 1), (0, 2)]).getD (Graph.empty 3)
    coloring := Coloring.trivial 3 (by omega) }

private def k3 : Colored 3 1 :=
  { graph := (Graph.ofEdges? 3 [(0, 1), (1, 2), (0, 2)]).getD (Graph.empty 3)
    coloring := Coloring.trivial 3 (by omega) }

private def c4 : Colored 4 1 :=
  { graph := (Graph.ofEdges? 4 [(0, 1), (1, 2), (2, 3), (0, 3)]).getD (Graph.empty 4)
    coloring := Coloring.trivial 4 (by omega) }

private def path4 : Colored 4 1 :=
  { graph := (Graph.ofEdges? 4 [(0, 1), (1, 2), (2, 3)]).getD (Graph.empty 4)
    coloring := Coloring.trivial 4 (by omega) }

/-! # Permutations and labels -/

-- checked construction rejects duplicates and accepts permutations
#guard (Perm.ofVector? (n := 3) #v[(0 : Fin 3), 0, 2]).isNone
#guard (Perm.ofVector? (n := 3) #v[(2 : Fin 3), 0, 1]).isSome

private def rot3 : Perm 3 :=
  (Perm.ofVector? #v[(1 : Fin 3), 2, 0]).getD (Perm.id 3)

#guard rot3.comp rot3.inv == Perm.id 3
#guard rot3.inv.comp rot3 == Perm.id 3
#guard rot3.inv.inv == rot3
#guard (rot3.toLabel.toPerm) == rot3

/-! # Isomorphism decisions -/

#guard checkIso p3 p3 (Perm.id 3)
#guard isIso p3 p3'
#guard !isIso p3 k3
#guard isIso c4 c4
#guard !isIso c4 path4
-- the found transporter is accepted by the executable checker
#guard
  match findIso p3 p3' with
  | some p => checkIso p3 p3' p
  | none => false

/-! # Canonical forms -/

-- relabelling by the canonical label produces the canonical form
#guard p3.relabel (label p3) == canon p3
#guard c4.relabel (label c4) == canon c4
-- canonical forms have contiguous colour cells
#guard decide (ColorSorted (canon p3))
#guard decide (ColorSorted (canon c4))
-- invariance under a committed relabelling
#guard canon (p3.relabel rot3.toLabel) == canon p3

/-! # Bounded operations: exhaustion is `none`, never `false` -/

#guard (findIso? { maxNodes := 0, maxCertNodes := 0 } p3 p3').isNone
#guard (checkIso? { maxCheckerSteps := 0 } p3 p3' (Perm.id 3)).isNone
#guard (canon? { maxNodes := 0, maxCertNodes := 0 } {} p3).isNone
#guard (findIso? {} p3 p3') == some (findIso p3 p3')
#guard
  match checkIso? {} p3 p3 (Perm.id 3) with
  | some b => b
  | none => false

/-! # Reference and nauty-compatible agreement

The nauty-compatible search and the proven reference implementation must
agree on every isomorphism verdict. Their canonical representatives are
not required to coincide. -/

private def nautyForm {n k : Nat} (G : Colored n k) : Option (Colored n k) :=
  (Nauty.canonicalize? G).map (·.form)

private def sameVerdict {n k : Nat} (G H : Colored n k) : Bool :=
  match nautyForm G, nautyForm H with
  | some fG, some fH => (fG == fH) == isIso G H
  | _, _ => false

#guard sameVerdict p3 p3'
#guard sameVerdict p3 k3
#guard sameVerdict c4 path4
#guard sameVerdict c4 c4

-- the public canonical form now carries nauty's canonical rows: the
-- certificate-checked `canon` and the transcribed search agree on the
-- adjacency rows of the canonical representative
private def canonRowsAgree {n k : Nat} (G : Colored n k) : Bool :=
  Nauty.rowsOf (canon G) == (Nauty.runColored G).canong

#guard canonRowsAgree p3
#guard canonRowsAgree p3'
#guard canonRowsAgree k3
#guard canonRowsAgree c4
#guard canonRowsAgree path4

-- the nauty label is a genuine transporter to the nauty form
#guard
  match Nauty.canonicalize? c4 with
  | some r => checkIso c4 r.form r.label.toPerm && r.form == c4.relabel r.label
  | none => false

/-! # The Petersen pair at `n = 10`

`Reference.canon` is factorially infeasible at `n = 10`; these checks
exercise only the nauty-compatible search: the generalized Petersen
presentation `G(5, 2)` and the Kneser presentation `K(5, 2)` receive the
same canonical form, and the pentagonal prism receives a different one
although it is also cubic on ten vertices. -/

private def petersen : Colored 10 1 :=
  { graph := (Graph.ofEdges? 10
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]).getD (Graph.empty 10)
    coloring := Coloring.trivial 10 (by omega) }

/-- `K(5, 2)` on the lexicographic two-element subsets
`01 02 03 04 12 13 14 23 24 34` of `Fin 5`, joined when disjoint. -/
private def kneser52 : Colored 10 1 :=
  { graph := (Graph.ofEdges? 10
      [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8),
       (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)]).getD (Graph.empty 10)
    coloring := Coloring.trivial 10 (by omega) }

private def prism5 : Colored 10 1 :=
  { graph := (Graph.ofEdges? 10
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 6), (6, 7), (7, 8), (8, 9), (5, 9),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]).getD (Graph.empty 10)
    coloring := Coloring.trivial 10 (by omega) }

#guard (nautyForm petersen).isSome
#guard nautyForm petersen == nautyForm kneser52
#guard nautyForm petersen != nautyForm prism5
#guard
  match Nauty.canonicalize? petersen with
  | some r => decide (ColorSorted r.form) && checkIso petersen r.form r.label.toPerm
  | none => false
-- transporter between the two Petersen presentations through the two
-- nauty labels
#guard
  match Nauty.canonicalize? petersen, Nauty.canonicalize? kneser52 with
  | some rP, some rK =>
      checkIso petersen kneser52 ((rK.label.toPerm.inv).comp rP.label.toPerm)
  | _, _ => false

/-! # Deterministic families -/

-- colexicographic unranking of the pairs over `Fin 5`
#guard (List.range 10).map (Families.unrankColex 5 2) ==
  [[1, 0], [2, 0], [2, 1], [3, 0], [3, 1], [3, 2], [4, 0], [4, 1], [4, 2], [4, 3]]
-- the Kneser graph K(5,2) is the Petersen graph
#guard Families.choose 5 2 == 10
#guard
  (Nauty.runColored (Families.plain (Families.kneser 5 2) (by decide))).canong ==
    (Nauty.runColored petersen).canong
-- regularity spot checks: T(5) and Paley 13 are 6-regular, Q3 cubic
#guard (Families.triangular 5).degree ⟨0, by decide⟩ == 6
#guard (Families.paley 13).degree ⟨0, by omega⟩ == 6
#guard (Families.hypercube 3).degree ⟨5, by decide⟩ == 3
#guard (Families.grid 3 4).degree ⟨0, by decide⟩ == 2
#guard (Families.copies 3 (Families.cycle 3)).degree ⟨4, by decide⟩ == 2
#guard (Families.completeMultipartite [2, 3]).degree ⟨0, by decide⟩ == 3
-- the verified pairwise decision agrees with the nauty search on a
-- structured pair: C6 versus two triangles
#guard
  Pairwise.decideIso? {}
    (Families.plain (Families.cycle 6) (by omega))
    (Families.plain (Families.copies 2 (Families.cycle 3)) (by decide)) ==
    some false

/-! # The empty graph -/

private def empty0 : Colored 0 0 :=
  { graph := Graph.empty 0
    coloring := { cells := ⟨#[], rfl⟩, onto := fun c => absurd c.isLt (by omega) } }

#guard isIso empty0 empty0
#guard canon empty0 == empty0
#guard (Nauty.canonicalize? empty0).isSome

end Hex.GraphIso.Conformance
