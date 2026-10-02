/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexGraphIso.Nauty.Sparse.LimitCount
import HexGraphIso.SparseTestGraphs
import HexGraphIso.Sparse.TacticSupport
meta import HexGraphIso.Nauty.Sparse.Limited
meta import HexGraphIso.SparseTestGraphs
meta import HexGraphIso.Sparse.TacticSupport

open Hex Hex.GraphIso
open Nauty.Sparse

-- Compare canonical rows, literal labels and codes, generator emissions,
-- exact group data and all seven nauty diagnostic counters.
private def sameResult (a b : State n) : Bool :=
  a.canonlab == b.canonlab && a.canoncode == b.canoncode &&
  a.canong.offsets == b.canong.offsets && a.canong.neighbors == b.canong.neighbors &&
  a.genTrace == b.genTrace && a.orbits == b.orbits && a.order == b.order &&
  a.numnodes == b.numnodes && a.numorbits == b.numorbits &&
  a.numgenerators == b.numgenerators && a.numbadleaves == b.numbadleaves &&
  a.maxlevel == b.maxlevel && a.tctotal == b.tctotal && a.canupdates == b.canupdates

private def boundary (G : Sparse.Colored n k) : Bool :=
  let direct := runColored G
  (Limited.runColored? 0 G).isNone &&
  (Limited.runColored? (direct.numnodes - 1) G).isNone &&
  (match Limited.runColored? direct.numnodes G with
   | none => false
   | some s => sameResult s.value direct && s.visited == direct.numnodes &&
       s.remaining == 0 && !s.exhausted) &&
  (match Limited.runColored? (direct.numnodes + 1) G with
   | none => false
   | some s => sameResult s.value direct && s.remaining == 1)

private def pairBoundary (G H : Sparse.Colored n k) : Bool :=
  let a := runColored G
  let b := runColored H
  let total := a.numnodes + b.numnodes
  (Limited.runPair? (total - 1) G H).isNone &&
  (match Limited.runPair? total G H with
   | none => false
   | some (sa, sb) => sameResult sa.value a && sameResult sb.value b &&
       sa.visited + sb.visited == total && sb.remaining == 0)

#guard boundary SparseTestGraphs.empty
#guard boundary SparseTestGraphs.random12
#guard boundary SparseTestGraphs.random12b
#guard boundary SparseTestGraphs.edgeMarkA
#guard boundary SparseTestGraphs.edgeMarkB
#guard boundary SparseTestGraphs.nonedgeMark
#guard pairBoundary SparseTestGraphs.empty SparseTestGraphs.empty
#guard pairBoundary SparseTestGraphs.random12 SparseTestGraphs.random12relabeled
#guard pairBoundary SparseTestGraphs.edgeMarkA SparseTestGraphs.edgeMarkB

private def certBoundary (G : Sparse.Colored n k) : Bool :=
  let direct := runColored G
  match Compact.produceCand G with
  | none => false
  | some c =>
    let records := c.tree.stats.records
    (Compact.candidate? 0 G direct).isNone &&
    (Compact.candidate? (records - 1) G direct).isNone &&
    (match Compact.candidate? records G direct with
     | none => false
     | some (out, rest) => rest == 0 && out.tree.stats.records == records &&
         out.lab == c.lab && out.key.codes == c.key.codes &&
         Literal.Compact.checkKey G out.tree out.key) &&
    (match Compact.candidate? (records + 1) G direct with
     | none => false
     | some (out, rest) => rest == 1 && Literal.Compact.checkKey G out.tree out.key)

#guard certBoundary SparseTestGraphs.empty
#guard certBoundary SparseTestGraphs.random12
#guard certBoundary SparseTestGraphs.random12b
#guard certBoundary SparseTestGraphs.edgeMarkA
#guard certBoundary SparseTestGraphs.edgeMarkB
#guard certBoundary SparseTestGraphs.nonedgeMark

-- Exhaustion propagates through the actual transporter backend, including
-- when the first search finished but the second cannot start.
#guard (Sparse.Tactic.findWitness 0 SparseTestGraphs.empty SparseTestGraphs.empty).isNone
#guard (Sparse.Tactic.findWitness 1 SparseTestGraphs.empty SparseTestGraphs.empty).isNone
#guard match Sparse.Tactic.findWitness 2 SparseTestGraphs.empty SparseTestGraphs.empty with
  | some (some _, 2) => true
  | _ => false

#guard match Sparse.Tactic.findCandidates 100000 0 SparseTestGraphs.random12 SparseTestGraphs.random12b with
  | .error _ => true
  | .ok _ => false

#guard match Sparse.Tactic.findCandidates 0 100000 SparseTestGraphs.random12 SparseTestGraphs.random12b with
  | .error _ => true
  | .ok _ => false

example (G : Sparse.Colored n k) : Limited.runColored? 0 G = none :=
  Limited.runColored?_zero G

example {G H : Sparse.Colored n k} {a b : Limited.State n}
    (h : Limited.runPair? limit G H = some (a, b)) :
    a.value.numnodes + b.value.numnodes ≤ limit := Limited.runPair?_nodes h

example {G H : Sparse.Colored n k} {a b : Limited.State n}
    (h : Limited.runPair? limit G H = some (a, b)) :
    a.value = runColored G ∧ b.value = runColored H := Limited.runPair?_eq h

-- The public import exposes correctness of the actual bounded pipeline,
-- including literal replay and the declarative canonical key.
example {G : Sparse.Colored n k} {s : Limited.State n} {c : CertCandidate n} {rest : Nat}
    (hs : Limited.runColored? nodes G = some s)
    (hc : Compact.candidate? records G s.value = some (c, rest)) :
    Literal.Compact.checkKey G c.tree c.key = true := by
  rw [Literal.Compact.checkKey_eq]
  exact Compact.candidate?_replays hs hc

example {G : Sparse.Colored n k} {s : Limited.State n} {c : CertCandidate n} {rest : Nat}
    (hs : Limited.runColored? nodes G = some s)
    (hc : Compact.candidate? records G s.value = some (c, rest)) :
    c.key = canonSpecKey G := Compact.produceCand_key (Compact.candidate?_from_run hs hc)
