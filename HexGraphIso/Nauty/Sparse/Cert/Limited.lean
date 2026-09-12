/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Quota
public import HexGraphIso.Nauty.Sparse.LimitAgreement

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- The compact proof walk with a shared record quota. Admission precedes
refinement or witness proposals, and each sibling receives only unused quota.
The native splitter, target, witness checks and lazy fallback are unchanged. -/
def produceNode? (G : Hex.SparseGraph n) (tcLevel : Nat) (gens : List (Perm n)) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → Key n → Nat →
      Option (CertNode × Nat)
  | 0, _, _, _, _, _, _, remaining =>
    if remaining = 0 then none else some (.leaf, remaining - 1)
  | fuel + 1, level, lab, ptn, active, numcells, B, remaining =>
    if remaining = 0 then none else
      let r := refine (.ofGraph G) level lab ptn active numcells
      match B.codes with
      | [] => some (.leaf, remaining - 1)
      | b :: bs =>
        if compare r.longcode b = .lt then some (.codePrune, remaining - 1)
        else if discreteAt r.ptn level n then some (.leaf, remaining - 1)
        else
          let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
          let child := fun o => breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
          let proposals := choose (n := n) r.lab t.1 (usable gens r.lab r.ptn level)
          let witness := fun o earlier raw => Replay.checkAutom G (level + 1)
            (child earlier).1 (child o).1 (child o).2.1 raw
          let fallback := fun o q => produceNode? G tcLevel gens fuel (level + 1)
            (child o).1 (child o).2.1 (child o).2.2 (r.numcells + 1) ⟨bs, B.graph⟩ q
          (Quota.collect (Quota.emit proposals witness fallback)
            (List.range t.2.2) (remaining - 1)).map fun (cs, rest) => (.node cs, rest)
  termination_by structural fuel => fuel

/-- The bounded producer's counter is exactly the size of its emitted
certificate, including all compact references. -/
theorem produceNode?_budget {G : Hex.SparseGraph n} {tcLevel : Nat} {gens : List (Perm n)}
    (fuel : Nat) {level : Nat} {lab ptn : Array Nat} {active : VSet n} {nc : Nat}
    {B : Key n} {remaining final : Nat} {c : CertNode}
    (h : produceNode? G tcLevel gens fuel level lab ptn active nc B remaining = some (c, final)) :
    c.stats.records + final = remaining := by
  induction fuel generalizing level lab ptn active nc B remaining final c with
  | zero =>
    simp only [produceNode?] at h
    split at h
    · cases h
    · cases Option.some.inj h
      simp only [CertNode.stats]
      omega
  | succ fuel ih =>
    simp only [produceNode?] at h
    split at h
    · cases h
    · rename_i hq
      split at h
      · cases Option.some.inj h
        simp only [CertNode.stats]
        omega
      · split at h
        · cases Option.some.inj h
          simp only [CertNode.stats]
          omega
        · split at h
          · cases Option.some.inj h
            simp only [CertNode.stats]
            omega
          · obtain ⟨⟨cs, rest⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
            cases he
            have hb := Quota.collect_budget
              (fun _ _ _ _ _ he => Quota.emit_budget (fun _ _ _ hf => ih hf) he) hc
            dsimp only [CertNode.stats]
            omega

/-- Successful quota-limited production retains the unlimited compact
producer's exact tree, including its literal automorphism references. -/
theorem produceNode?_eq {G : Hex.SparseGraph n} {tcLevel : Nat} {gens : List (Perm n)}
    (fuel : Nat) {level : Nat} {lab ptn : Array Nat} {active : VSet n} {nc : Nat}
    {B : Key n} {remaining final : Nat} {c : CertNode}
    (h : produceNode? G tcLevel gens fuel level lab ptn active nc B remaining = some (c, final)) :
    c = produceNode G tcLevel gens fuel level lab ptn active nc B := by
  induction fuel generalizing level lab ptn active nc B remaining final c with
  | zero =>
    simp only [produceNode?, produceNode] at h ⊢
    split at h
    · cases h
    · exact (Prod.mk.inj (Option.some.inj h)).1.symm
  | succ fuel ih =>
    by_cases hq : remaining = 0
    · simp only [produceNode?, hq, ite_true, reduceCtorEq] at h
    · cases hb : B.codes with
      | nil =>
        simp only [produceNode?, produceNode, hq, ite_false, hb] at h ⊢
        exact (Prod.mk.inj (Option.some.inj h)).1.symm
      | cons b bs =>
        let r := refine (.ofGraph G) level lab ptn active nc
        by_cases hc : compare r.longcode b = .lt
        · dsimp only [r] at hc
          simp only [produceNode?, produceNode, hq, ite_false, hb, hc, ite_true] at h ⊢
          exact (Prod.mk.inj (Option.some.inj h)).1.symm
        · dsimp only [r] at hc
          by_cases hd : discreteAt r.ptn level n = true
          · dsimp only [r] at hd
            simp only [produceNode?, produceNode, hq, ite_false, hb, hc, hd, ite_true] at h ⊢
            exact (Prod.mk.inj (Option.some.inj h)).1.symm
          · dsimp only [r] at hd
            simp only [produceNode?, produceNode, hq, ite_false, hb, hc, hd] at h ⊢
            obtain ⟨⟨cs, rest⟩, hcs, he⟩ := Option.map_eq_some_iff.mp h
            cases he
            apply congrArg CertNode.node
            apply Quota.collect_eq (h := hcs)
            intro o _ q c rest he
            apply Quota.emit_eq (h := he)
            intro q c rest hf
            exact ih hf

/-- Initialize the bounded proof walk with the native stable colour cells.
The empty graph has one leaf record. -/
def produceRoot? (maxRecords : Nat) (G : GraphIso.Sparse.Colored n k)
    (gens : List (Perm n)) (B : Key n) : Option (CertNode × Nat) :=
  if n = 0 then
    if maxRecords = 0 then none else some (.leaf, maxRecords - 1)
  else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    produceNode? G.graph 100 gens (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length B maxRecords

theorem produceRoot?_budget {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {B : Key n} {c : CertNode} {rest : Nat}
    (h : produceRoot? maxRecords G gens B = some (c, rest)) :
    c.stats.records + rest = maxRecords := by
  unfold produceRoot? at h
  split at h
  · split at h
    · cases h
    · cases Option.some.inj h
      simp only [CertNode.stats]
      omega
  · exact produceNode?_budget (n + 2) h

theorem produceRoot?_records {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {B : Key n} {c : CertNode} {rest : Nat}
    (h : produceRoot? maxRecords G gens B = some (c, rest)) : c.stats.records ≤ maxRecords := by
  have hb := produceRoot?_budget h
  omega

theorem produceRoot?_eq {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {B : Key n} {c : CertNode} {rest : Nat}
    (h : produceRoot? maxRecords G gens B = some (c, rest)) : c = produceRoot G gens B := by
  by_cases hn : n = 0
  · simp only [produceRoot?, produceRoot, hn, ite_true] at h ⊢
    split at h
    · cases h
    · exact (Prod.mk.inj (Option.some.inj h)).1.symm
  · simp only [produceRoot?, produceRoot, hn, ite_false] at h ⊢
    exact produceNode?_eq (n + 2) h

theorem produceRoot?_replays {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {gens : List (Perm n)} {c : CertNode} {rest : Nat}
    (h : produceRoot? maxRecords G gens (canonSpecKey G) = some (c, rest)) :
    checkKey G c (canonSpecKey G) = true := by
  rw [produceRoot?_eq h]
  exact produceRoot_replays G gens

/-- Retain a supplied native search's key, label and generators while
bounding certificate construction. The caller can share a search quota
across graphs without repeating either optimized search. -/
def candidate? (maxRecords : Nat) (G : GraphIso.Sparse.Colored n k) (s : State n) :
    Option (CertCandidate n × Nat) :=
  let best := if n = 0 then some (⟨[codeSentinel], G.graph⟩ : Key n)
    else State.best G.graph s
  best.bind fun B => (produceRoot? maxRecords G s.generators B).map fun (tree, rest) =>
    (⟨tree, B, s.canonlab⟩, rest)

theorem candidate?_budget {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k} {s : State n}
    {c : CertCandidate n} {rest : Nat} (h : candidate? maxRecords G s = some (c, rest)) :
    c.tree.stats.records + rest = maxRecords := by
  unfold candidate? at h
  obtain ⟨B, _, hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨tree, final⟩, ht, he⟩ := Option.map_eq_some_iff.mp hb
  cases he
  exact produceRoot?_budget ht

theorem candidate?_label {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k} {s : State n}
    {c : CertCandidate n} {rest : Nat} (h : candidate? maxRecords G s = some (c, rest)) :
    c.lab = s.canonlab := by
  unfold candidate? at h
  obtain ⟨B, _, hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨tree, final⟩, _, he⟩ := Option.map_eq_some_iff.mp hb
  cases he
  rfl

end Hex.GraphIso.Nauty.Sparse.Compact
