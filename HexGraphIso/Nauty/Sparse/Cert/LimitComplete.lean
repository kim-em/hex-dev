/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Limited

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- The exact unlimited certificate size is a sufficient record quota.
This follows the executed bounded recursion, including lazy witness reuse. -/
theorem produceNode?_complete {G : Hex.SparseGraph n} {tcLevel : Nat} {gens : List (Perm n)}
    (fuel : Nat) {level : Nat} {lab ptn : Array Nat} {active : VSet n} {nc : Nat}
    {B : Key n} {remaining : Nat}
    (hq : (produceNode G tcLevel gens fuel level lab ptn active nc B).stats.records ≤ remaining) :
    produceNode? G tcLevel gens fuel level lab ptn active nc B remaining =
      some (produceNode G tcLevel gens fuel level lab ptn active nc B,
        remaining - (produceNode G tcLevel gens fuel level lab ptn active nc B).stats.records) := by
  induction fuel generalizing level lab ptn active nc B remaining with
  | zero =>
    simp only [produceNode, CertNode.stats] at hq ⊢
    simp only [produceNode?, show remaining ≠ 0 by omega, ite_false]
  | succ fuel ih =>
    have hp := (produceNode G tcLevel gens (fuel + 1) level lab ptn active nc B).records_pos
    have hne : remaining ≠ 0 := by omega
    cases hb : B.codes with
    | nil => simp only [produceNode?, produceNode, hne, ite_false, hb, CertNode.stats]
    | cons b bs =>
      let r := refine (.ofGraph G) level lab ptn active nc
      by_cases hc : compare r.longcode b = .lt
      · dsimp only [r] at hc
        simp only [produceNode?, produceNode, hne, ite_false, hb, hc, ite_true, CertNode.stats]
      · dsimp only [r] at hc
        by_cases hd : discreteAt r.ptn level n = true
        · dsimp only [r] at hd
          simp only [produceNode?, produceNode, hne, ite_false, hb, hc, hd, ite_true, CertNode.stats]
        · dsimp only [r] at hd
          let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
          let child := fun o => breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
          let proposals := choose (n := n) r.lab t.1 (usable gens r.lab r.ptn level)
          let witness := fun o earlier raw => Replay.checkAutom G (level + 1)
            (child earlier).1 (child o).1 (child o).2.1 raw
          let plain := fun o => produceNode G tcLevel gens fuel (level + 1)
            (child o).1 (child o).2.1 (child o).2.2 (r.numcells + 1) ⟨bs, B.graph⟩
          let bounded := fun o q => produceNode? G tcLevel gens fuel (level + 1)
            (child o).1 (child o).2.1 (child o).2.2 (r.numcells + 1) ⟨bs, B.graph⟩ q
          let cs := (List.range t.2.2).map (Replay.emit proposals witness plain)
          have hsize : (CertNode.statsList cs).records ≤ remaining - 1 := by
            simp only [produceNode, hb, hc, hd, ite_false] at hq
            change (CertNode.statsList cs).records + 1 ≤ remaining at hq
            omega
          have hh : Quota.collect (Quota.emit proposals witness bounded)
              (List.range t.2.2) (remaining - 1) =
              some (cs, remaining - 1 - (CertNode.statsList cs).records) := by
            apply Quota.collect_complete
            · intro o _ q ho
              apply Quota.emit_complete
              · intro q hq
                exact ih hq
              · exact ho
            · exact hsize
          simp only [produceNode?, produceNode, hne, ite_false, hb, hc, hd]
          change (Quota.collect (Quota.emit proposals witness bounded)
            (List.range t.2.2) (remaining - 1)).map (fun (cs, rest) => (CertNode.node cs, rest)) =
              some (CertNode.node cs, remaining - (CertNode.node cs).stats.records)
          rw [hh]
          simp only [Option.map_some, CertNode.stats, Nat.sub_sub, Nat.add_comm]

theorem produceRoot?_complete {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {B : Key n}
    (hq : (produceRoot G gens B).stats.records ≤ maxRecords) :
    produceRoot? maxRecords G gens B =
      some (produceRoot G gens B, maxRecords - (produceRoot G gens B).stats.records) := by
  by_cases hn : n = 0
  · simp only [produceRoot, hn, ite_true, CertNode.stats] at hq ⊢
    simp only [produceRoot?, hn, ite_true, show maxRecords ≠ 0 by omega, ite_false]
  · simp only [produceRoot?, produceRoot, hn, ite_false] at hq ⊢
    exact produceNode?_complete (n + 2) hq

/-- Exhaustion occurs exactly when the unlimited tree exceeds the record cap. -/
theorem produceRoot?_none {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {B : Key n} :
    produceRoot? maxRecords G gens B = none ↔
      maxRecords < (produceRoot G gens B).stats.records := by
  constructor
  · intro h
    by_cases hq : (produceRoot G gens B).stats.records ≤ maxRecords
    · rw [produceRoot?_complete hq] at h
      cases h
    · omega
  · intro hq
    cases h : produceRoot? maxRecords G gens B with
    | none => rfl
    | some r =>
      obtain ⟨c, rest⟩ := r
      have hb := produceRoot?_records h
      rw [produceRoot?_eq h] at hb
      omega

/-- A sufficient record quota packages exactly the unlimited candidate
from the optimized native search, retaining its key and literal label. -/
theorem candidate?_complete {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {c : CertCandidate n} (hc : produceCand G = some c)
    (hq : c.tree.stats.records ≤ maxRecords) :
    candidate? maxRecords G (runColored G) = some (c, maxRecords - c.tree.stats.records) := by
  rw [produceCand_eq] at hc
  cases Option.some.inj hc
  have hb : (if n = 0 then some (⟨[codeSentinel], G.graph⟩ : Key n)
      else State.best G.graph (runColored G)) = some (canonSpecKey G) := by
    by_cases hn : n = 0
    · simp only [hn, ite_true, canonSpecKey_zero hn]
    · simp only [hn, ite_false]
      exact run_max G (by omega)
  simp only [candidate?, hb, Option.bind_some, produceRoot?_complete hq, Option.map_some]

/-- Every successful bounded candidate from the direct run is exactly
the unlimited candidate, without any extra assumption on its proposed key. -/
theorem candidate?_agrees {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {c : CertCandidate n} {rest : Nat}
    (h : candidate? maxRecords G (runColored G) = some (c, rest)) : produceCand G = some c := by
  unfold candidate? at h
  obtain ⟨B, hb, hc⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨tree, final⟩, ht, he⟩ := Option.map_eq_some_iff.mp hc
  cases he
  simp only [produceCand, hb, Option.map_some, ← produceRoot?_eq ht]

/-- Accepted bounded search and bounded certificate production retain the
optimized producer's full candidate. Both limits may be arbitrary. -/
theorem candidate?_from_run {maxNodes maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {s : Limited.State n} {c : CertCandidate n} {rest : Nat}
    (hs : Limited.runColored? maxNodes G = some s)
    (hc : candidate? maxRecords G s.value = some (c, rest)) : produceCand G = some c := by
  rw [Limited.runColored?_eq hs] at hc
  exact candidate?_agrees hc

theorem candidate?_replays {maxNodes maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {s : Limited.State n} {c : CertCandidate n} {rest : Nat}
    (hs : Limited.runColored? maxNodes G = some s)
    (hc : candidate? maxRecords G s.value = some (c, rest)) : checkKey G c.tree c.key = true :=
  produceCand_replays (candidate?_from_run hs hc)

end Hex.GraphIso.Nauty.Sparse.Compact
