/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.GenerateComplete
public import HexGraphIso.Nauty.Sparse.Cert.Candidate
public import HexGraphIso.Nauty.Sparse.GenerationTrace

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Produce a compact root certificate from native stable colour buckets.
The generator list supplies proposals, all checked before pruning. -/
@[expose] def produceRoot (G : GraphIso.Sparse.Colored n k) (gens : List (Perm n))
    (B : Key n) : CertNode :=
  if n = 0 then .leaf else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    produceNode G.graph 100 gens (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length B

/-- Unlimited compact root production succeeds, even without usable
generators. Full expansion supplies every branch without a checked witness. -/
theorem produceRoot_replays (G : GraphIso.Sparse.Colored n k) (gens : List (Perm n)) :
    checkKey G (produceRoot G gens (canonSpecKey G)) (canonSpecKey G) = true := by
  by_cases hn : n = 0
  · simpa only [checkKey, produceRoot, Sparse.produceRoot, hn, ite_true] using
      Sparse.produceRoot_replays G
  · let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    have hv := SpecNode.initial G (by omega : 0 < n)
    dsimp only at hv
    have hb : ∀ l ∈ specLeaves G.graph 100 (n + 2) 1 p.1
        (initPtn n (n + 2) p.2) (initActive n p.2) p.2.length,
        Key.Le (l.key G.graph) (canonSpecKey G) := by
      intro l hl
      apply canonSpecKey_bound G
      simpa only [rootLeaves, hn, ite_false] using hl
    obtain ⟨a, ha⟩ := produceNode_replays (gens := gens)
      hv.label hv.node hv.count hv.depth (by omega) hb
    have hs := checkNode_valid hv ha
    have ha' : a = true := hs.attains.mpr ⟨specBest G, by
      simpa only [rootLeaves, hn, ite_false] using specBest_mem G, rfl⟩
    subst a
    simpa only [checkKey, produceRoot, hn, ite_false, beq_iff_eq] using ha

/-- Run the optimized search once, retaining its key, literal label and
generator trace. Expand only those proof subtrees lacking checked witnesses. -/
@[expose] def produceCand (G : GraphIso.Sparse.Colored n k) : Option (CertCandidate n) :=
  let s := runColored G
  let best := if n = 0 then some (⟨[codeSentinel], G.graph⟩ : Key n)
    else State.best G.graph s
  best.map fun B => ⟨produceRoot G s.generators B, B, s.canonlab⟩

theorem produceCand_eq (G : GraphIso.Sparse.Colored n k) :
    produceCand G = some ⟨produceRoot G (runColored G).generators (canonSpecKey G),
      canonSpecKey G, (runColored G).canonlab⟩ := by
  by_cases hn : n = 0
  · simp only [produceCand, hn, ite_true, canonSpecKey_zero hn, Option.map_some]
  · have hb : State.best G.graph (runColored G) = some (canonSpecKey G) :=
      run_max G (by omega)
    simp only [produceCand, hn, ite_false, hb, Option.map_some]

theorem produceCand_isSome (G : GraphIso.Sparse.Colored n k) : (produceCand G).isSome := by
  rw [produceCand_eq]
  rfl

theorem produceCand_replays {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : checkKey G c.tree c.key = true := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  exact produceRoot_replays G _

theorem produceCand_key {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : c.key = canonSpecKey G := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  rfl

theorem produceCand_label {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) : c.lab = (runColored G).canonlab := by
  rw [produceCand_eq] at h
  cases Option.some.inj h
  rfl

@[expose] def validateKey? (G : GraphIso.Sparse.Colored n k) (c : CertCandidate n) : Option (Key n) :=
  if checkKey G c.tree c.key then some c.key else none

theorem validateKey?_sound {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n} {B : Key n}
    (h : validateKey? G c = some B) : canonSpecKey G = B := by
  rw [validateKey?] at h
  split at h
  · rename_i hc
    cases Option.some.inj h
    exact checkKey_sound hc
  · cases h

/-- Produce and replay a compact sparse canonical-key certificate. -/
@[expose] def certifyKey? (G : GraphIso.Sparse.Colored n k) : Option (Key n) :=
  (produceCand G).bind (validateKey? G)

theorem certifyKey?_eq (G : GraphIso.Sparse.Colored n k) :
    certifyKey? G = some (canonSpecKey G) := by
  simp only [certifyKey?, produceCand_eq, Option.bind_some, validateKey?, produceRoot_replays, ite_true]

end Hex.GraphIso.Nauty.Sparse.Compact
