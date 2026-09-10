/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Tactic
public import HexGraphIso.Random
public import HexGraphIso.TestGraphs
public meta import HexGraphIso.Tactic
public meta import HexGraphIso.Random
public meta import HexGraphIso.TestGraphs

/-!
Tests for the Mathlib-free `graph_iso` tactic: positive and negative
goals, coloured and uncoloured goals, the limit syntax, and the
diagnostic messages. The kernel replays every closing proof. Each
failure case asserts its message and leaves the goal unchanged.
-/

namespace Hex.GraphIso.TacticTests

open Hex Hex.GraphIso Hex.GraphIso.TestGraphs

def p3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2)]
    coloring := Coloring.trivial 3 }

def p3' : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (0, 2)]
    coloring := Coloring.trivial 3 }

def k3 : Colored 3 1 :=
  { graph := Graph.ofEdges [(0, 1), (1, 2), (0, 2)]
    coloring := Coloring.trivial 3 }

example : Isomorphic p3 p3' := by graph_iso
example : ¬ Isomorphic p3 k3 := by graph_iso
example : Isomorphic p3 p3' := by
  graph_iso (maxSearchNodes := 200000) (maxKernelSteps := 10000000)
example : Isomorphic p3 p3' := by
  graph_iso (maxKernelSteps := 10000000) (maxCertRecords := 200000)
-- A zero certificate budget must still close the goal. This pair is
-- irregular, so the root separator closes it before the certificate leg.
example : ¬ Isomorphic p3 k3 := by graph_iso (maxCertRecords := 0)

/-- error: graph_iso: the graphs are not isomorphic; the positive goal is not provable -/
#guard_msgs in
example : Isomorphic p3 k3 := by graph_iso

/-- error: graph_iso: the graphs are isomorphic; the negative goal is not provable -/
#guard_msgs in
example : ¬ Isomorphic p3 p3' := by graph_iso

/-- error: graph_iso: search exhausted: visited 6 nodes but maxSearchNodes := 0 -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxSearchNodes := 0)

/-- error: graph_iso: replay exhausted: checking the transporter takes 12 steps but maxKernelSteps := 0 -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxKernelSteps := 0)

/-- error: Invalid configuration option `maxFoo` for `Tactic.Config` -/
#guard_msgs in
example : Isomorphic p3 p3' := by graph_iso (maxFoo := 1)

/-!
The Petersen pair at `n = 10`: two genuinely different presentations of
the same graph, and a cubic ten-vertex non-example.
-/

def petersenG : Graph 10 :=
  Graph.ofEdges
    [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
     (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

def kneser52G : Graph 10 :=
  Graph.ofEdges
    [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8),
     (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)]

/-- The pentagonal prism: also cubic on ten vertices, so degree
refinement alone cannot separate it from the Petersen graph. The
negative goal replays the two canonical-key certificates in the
kernel. -/
def prism5G : Graph 10 :=
  Graph.ofEdges
    [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
     (5, 6), (6, 7), (7, 8), (8, 9), (5, 9),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

def petersen : Colored 10 1 := petersenG.singleColor

def kneser52 : Colored 10 1 := kneser52G.singleColor

def prism5 : Colored 10 1 := prism5G.singleColor

example : Isomorphic petersen kneser52 := by graph_iso

set_option maxRecDepth 100000 in
example : ¬ Isomorphic petersen prism5 := by graph_iso

/-!
This pair is cubic, so the root refinement codes agree and only the
certificate leg is left. Withdrawing its record budget leaves every
negative route exhausted, and the message names the limit that ran out.
-/

/-- error: graph_iso: every negative route is exhausted: the root refinement codes agree, and the certificates hold 18 and 13 records but maxCertRecords := 0 -/
#guard_msgs in
example : ¬ Isomorphic petersen prism5 := by
  graph_iso (maxCertRecords := 0)

/-!
The same pair stated on bare `Graph 10` values: the tactic colours both
sides with the single colour zero and transports the conclusion back,
so the uncoloured goals need no wrapping at the call.
-/

example : Graph.Isomorphic petersenG kneser52G := by graph_iso

example : Graph.Isomorphic petersenG kneser52G := by
  graph_iso (maxSearchNodes := 200000) (maxKernelSteps := 10000000)

set_option maxRecDepth 100000 in
example : ¬ Graph.Isomorphic petersenG prism5G := by graph_iso

/-- error: graph_iso: the graphs are not isomorphic; the positive goal is not provable -/
#guard_msgs in
example : Graph.Isomorphic petersenG prism5G := by graph_iso

/-- error: graph_iso: the graphs are isomorphic; the negative goal is not provable -/
#guard_msgs in
example : ¬ Graph.Isomorphic petersenG kneser52G := by graph_iso

/-!
Coloured goals at `n = 6`: ordered colours constrain isomorphisms.
Colour `0` marks an adjacent pair of the six-cycle in the first two
colourings and a non-adjacent pair in the third.
-/

def c6 : Graph 6 :=
  Graph.ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]

def modFallback : Coloring 6 2 := Coloring.mod 6 2

def edgeMarkA : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(0 : Fin 2), 0, 1, 1, 1, 1]).getD modFallback⟩

def edgeMarkB : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(1 : Fin 2), 1, 1, 0, 0, 1]).getD modFallback⟩

def nonedgeMark : Colored 6 2 :=
  ⟨c6, (Coloring.ofVector? #v[(0 : Fin 2), 1, 1, 0, 1, 1]).getD modFallback⟩

example : Isomorphic edgeMarkA edgeMarkB := by graph_iso
example : ¬ Isomorphic edgeMarkA nonedgeMark := by graph_iso

/-!
The recorded random `n = 12` corpus pair of `HexGraphIso.TestGraphs`:
the `G(12, 1/2)` graph of the first seed against its image under the
recorded Fisher-Yates relabelling, and against the graph of the second
seed.
-/

example : Isomorphic g12 g12relabelled := by graph_iso

set_option maxRecDepth 400000 in
example : ¬ Isomorphic g12 g12b := by graph_iso

end Hex.GraphIso.TacticTests
