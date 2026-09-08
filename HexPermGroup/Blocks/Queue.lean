/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Blocks.Check

public section

namespace Hex.PermGroup.Blocks

/-- Pending generator images in the supplied generator order. -/
@[expose] def images (S : Array (Perm n)) (x y : Fin n) : List (Fin n × Fin n) :=
  S.toList.map fun s => (s.get x, s.get y)

/-- Closure obligations are retained in the pending queue. Any equivalence
relation containing both the current blocks and the queue must contain the
generator images of the current blocks. -/
@[expose] def Closed (S : Array (Perm n)) (p : Partition n) (todo : List (Fin n × Fin n)) : Prop :=
  ∀ R, Equivalence R → p.Refines R → (∀ q ∈ todo, R q.1 q.2) →
    ∀ s ∈ S, ∀ x y, p.Same x y → R (s.get x) (s.get y)

/-- The processed blocks together with the queue still imply every input seed. -/
@[expose] def Covers (seeds : List (Fin n × Fin n)) (p : Partition n)
    (todo : List (Fin n × Fin n)) : Prop :=
  ∀ R, Equivalence R → p.Refines R → (∀ q ∈ todo, R q.1 q.2) →
    ∀ q ∈ seeds, R q.1 q.2

/-- An effective-union trace and the proof invariants of its FIFO queue.
Only the trace survives proof erasure. -/
structure State (S : Array (Perm n)) (seeds : List (Fin n × Fin n))
    (p : Partition n) (todo : List (Fin n × Fin n)) where
  trace : List (Fin n × Fin n)
  replayed : replay S seeds (Partition.discrete n) trace = some p
  pending : ∀ q ∈ todo, Forced S seeds p q.1 q.2
  closed : Closed S p todo
  covers : Covers seeds p todo

namespace State

variable {S : Array (Perm n)} {seeds : List (Fin n × Fin n)}
  {p : Partition n} {x y : Fin n} {todo : List (Fin n × Fin n)}

/-- Start with singleton blocks and the supplied seed queue. -/
@[expose] def initial (S : Array (Perm n)) (seeds : List (Fin n × Fin n)) :
    State S seeds (Partition.discrete n) seeds where
  trace := []
  replayed := rfl
  pending q hq := Or.inl hq
  closed R hR _ _ _ _ x y hxy := by
    have he := (Partition.discrete_same x y).mp hxy
    subst y
    exact hR.refl _
  covers _ _ _ ht := ht

/-- Drop a request whose two points are already joined. -/
@[expose] def skip (st : State S seeds p ((x, y) :: todo)) (h : p.Same x y) :
    State S seeds p todo where
  trace := st.trace
  replayed := st.replayed
  pending q hq := st.pending q (List.mem_cons_of_mem _ hq)
  closed R hR hp ht := st.closed R hR hp (by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp _ _ h
    · exact ht q hq)
  covers R hR hp ht := st.covers R hR hp (by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp _ _ h
    · exact ht q hq)

/-- Join the requested blocks and enqueue one image pair per generator.
Previously queued requests remain justified after this coarsening. -/
@[expose] def merge (st : State S seeds p ((x, y) :: todo)) (h : ¬p.Same x y) :
    State S seeds (p.merge x y) (todo ++ images S x y) where
  trace := st.trace ++ [(x, y)]
  replayed := by
    rw [replay_append, st.replayed]
    simp only [Option.bind_some, replay]
    rw [ite_eq_left ⟨st.pending _ List.mem_cons_self, h⟩]
  pending q hq := by
    rcases List.mem_append.mp hq with hq | hq
    · exact (st.pending q (List.mem_cons_of_mem _ hq)).mono (p.merge_coarsens x y)
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (show s ∈ S by simpa using hs)
      refine Or.inr ⟨⟨i, hi⟩, ?_⟩
      simpa using p.merge_pair x y
  closed R hR hp ht := by
    have ho : p.Refines R := fun a b hab => hp a b (p.merge_coarsens x y a b hab)
    have hq : ∀ q ∈ (x, y) :: todo, R q.1 q.2 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp x y (p.merge_pair x y)
      · exact ht q (List.mem_append_left _ hq)
    intro s hs
    apply p.merge_least x y
      (R := fun a b => R (s.get a) (s.get b))
      ⟨fun _ => hR.refl _, hR.symm, hR.trans⟩
    · exact st.closed R hR ho hq s hs
    · exact ht (s.get x, s.get y) (List.mem_append_right _
        (List.mem_map.mpr ⟨s, by simpa using hs, rfl⟩))
  covers R hR hp ht := by
    apply st.covers R hR (fun a b hab => hp a b (p.merge_coarsens x y a b hab))
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp x y (p.merge_pair x y)
    · exact ht q (List.mem_append_left _ hq)

/-- Empty pending queues give complete checked block systems. -/
theorem check (st : State S seeds p []) : Blocks.check S seeds p st.trace = true := by
  have hc : Invariant S p.Same := st.closed p.Same p.equivalence (fun _ _ h => h)
    (by simp)
  have hs := st.covers p.Same p.equivalence (fun _ _ h => h) (by simp)
  simp only [Blocks.check, Bool.and_eq_true, decide_eq_true_eq, checkInvariant_iff]
  exact ⟨⟨st.replayed, hc⟩, hs⟩

end State

end Hex.PermGroup.Blocks
