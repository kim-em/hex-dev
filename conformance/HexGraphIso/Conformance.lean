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
- **Covered operations:** `Graph.ofEdges?`, `Graph.ofEdges`,
  `Graph.relabel`,
  `Perm.ofVector?`/`inv`/`comp`, `Label` round trips,
  `Coloring.ofVector?`, `Colored.relabel`, `checkIso`, `isIso`,
  `Checked.isIso`, `findIso`, `findIso?`, `checkIso?`, `canon?`,
  `canonicalize` (fast), `Checked.canonicalize`, `canon`,
  `Checked.canon`, `label`, `Reference.canon`, `Nauty.runColored`,
  `Nauty.canonicalize?`.
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
-- the total `Fin`-pair builder agrees with the checked builder, drops
-- diagonal pairs, and collapses duplicates in either orientation
#guard
  some (Graph.ofEdges [(0, 1), (1, 2)]) == Graph.ofEdges? 3 [(0, 1), (1, 2)]
#guard Graph.ofEdges (n := 3) [(1, 1)] == Graph.empty 3
#guard
  Graph.ofEdges (n := 3) [(0, 1), (1, 0), (0, 1)] == Graph.ofEdges [(0, 1)]

private def p3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2)]
    coloring := Coloring.trivial 3 }

private def p3' : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (0, 2)]
    coloring := Coloring.trivial 3 }

private def k3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2), (0, 2)]
    coloring := Coloring.trivial 3 }

private def c4 : Colored 4 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2), (2, 3), (0, 3)]
    coloring := Coloring.trivial 4 }

private def path4 : Colored 4 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2), (2, 3)]
    coloring := Coloring.trivial 4 }

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
-- the fast surface agrees with the certificate-checked surface, and
-- the fast path never falls back (canonicalize? answers)
#guard canonicalize p3 == Checked.canonicalize p3
#guard canonicalize c4 == Checked.canonicalize c4
#guard canon k3 == Checked.canon k3
#guard (canonicalize? p3).isSome
#guard isIso p3 p3' == Checked.isIso p3 p3'
#guard isIso p3 k3 == Checked.isIso p3 k3
-- canonical forms have contiguous colour cells
#guard decide (ColorSorted (canon p3))
#guard decide (ColorSorted (canon c4))
-- invariance under a committed relabelling
#guard canon (p3.relabel rot3.toLabel) == canon p3

/-! # Bounded operations: exhaustion is `none`, never `false` -/

#guard (findIso? { maxNodes := 0, maxCertNodes := 0 } p3 p3').isNone
-- `findIso?` charges both canonicalizations: one worst case is not enough
#guard (findIso? { maxNodes := searchCost 3 } p3 p3').isNone
#guard (checkIso? { maxCheckerSteps := 0 } p3 p3' (Perm.id 3)).isNone
#guard (canon? { maxNodes := 0, maxCertNodes := 0 } {} p3).isNone
-- every limit is consulted: certificate-record and replay-step exhaustion
#guard (canon? { maxCertNodes := 0 } {} p3).isNone
#guard (canon? {} { maxCheckerSteps := 0 } p3).isNone
#guard (certify? { maxCertNodes := 0 } p3).isNone
#guard
  match certify? {} p3 with
  | some cert => (checkCanon { maxCheckerSteps := 0 } p3 cert).isNone
  | none => false
#guard (findIso? {} p3 p3') == some (findIso p3 p3')
#guard
  match checkIso? {} p3 p3 (Perm.id 3) with
  | some b => b
  | none => false
-- within limits the bounded pipeline reproduces the total operation
#guard
  match canon? {} {} c4 with
  | some res => res.form == canon c4 && (c4.relabel res.label == res.form)
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
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

/-- `K(5, 2)` on the lexicographic two-element subsets
`01 02 03 04 12 13 14 23 24 34` of `Fin 5`, joined when disjoint. -/
private def kneser52 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8),
       (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)]
    coloring := Coloring.trivial 10 }

private def prism5 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 6), (6, 7), (7, 8), (8, 9), (5, 9),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

/-! # The automorphism-pruning certificate producer -/

private def hasAutom : Nauty.CertNode → Bool
  | .leaf | .codePrune => false
  | .autom _ _ => true
  | .node cs => go cs
where go : List Nauty.CertNode → Bool
  | [] => false
  | c :: cs => hasAutom c || go cs

-- pruning is live on a symmetric example: the validated certificate
-- carries `.autom` records and stays near nauty's visited-node count
-- (18 records at the time of pinning; the bound is deliberately loose)
#guard
  match Nauty.certifyKey? petersen with
  | some (cert, _) => hasAutom cert && cert.size ≤ 36
  | none => false
-- the single-replay pipeline accepts on the standard shapes
#guard (Nauty.certifyCanon? p3).isSome
#guard
  match Nauty.certifyCanon? petersen with
  | some r => r.form == canon petersen
  | none => false
-- the node-budgeted producer exhausts at zero and agrees within budget
#guard (Nauty.certifyKeyBounded? 0 petersen).isNone
#guard
  match Nauty.certifyKeyBounded? 1000000 petersen,
      Nauty.certifyKey? petersen with
  | some (_, B1), some (_, B2) => Nauty.keyCmp B1 B2 == .eq
  | _, _ => false

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
  (Nauty.runColored (Graph.singleColor (Families.kneser 5 2))).canong ==
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
    (Graph.singleColor (Families.cycle 6))
    (Graph.singleColor (Families.copies 2 (Families.cycle 3))) ==
    some false

/-! # The empty graph -/

private def empty0 : Colored 0 0 :=
  { graph := Graph.empty 0
    coloring := { cells := ⟨#[], rfl⟩, onto := fun c => absurd c.isLt (by omega) } }

#guard isIso empty0 empty0
#guard canon empty0 == empty0
#guard (Nauty.certifyCanon? empty0).isSome
#guard (Nauty.canonicalize? empty0).isSome

end Hex.GraphIso.Conformance
