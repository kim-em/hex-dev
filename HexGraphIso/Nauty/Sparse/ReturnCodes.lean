/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ComparisonOps
public import HexGraphIso.Nauty.Sparse.Canonical
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native incumbent growth, including the absence of an incumbent before
the first leaf. Parsed sparse keys are compared without row expansion. -/
def Grows (before after : Option (Key n)) : Prop :=
  ∀ b, before = some b → ∃ a, after = some a ∧ Key.Le b a

namespace Grows

theorem refl (key : Option (Key n)) : Grows key key := fun b hb => ⟨b, hb, Key.le_refl b⟩

theorem trans {a b c : Option (Key n)} (hab : Grows a b) (hbc : Grows b c) : Grows a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hab x hx
  obtain ⟨z, hz, hyz⟩ := hbc y hy
  exact ⟨z, hz, Key.le_trans hxy hyz⟩

theorem some {a b : Key n} (h : Key.Le a b) : Grows (some a) (some b) := by
  intro x hx
  cases hx
  exact ⟨b, rfl, h⟩

end Grows

/-- A completed native call retains settled comparisons on an extension
of its entry path. Recovery truncates that path at the receiving ancestor. -/
structure ReturnCodes (G : Hex.SparseGraph n) (stem bs fs : List Nat) (st : State n) : Prop where
  machine : ∃ cs, stem <+: cs ∧ Settled cs bs st ∧ FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  nonempty : bs ≠ []
  lower : ∃ f c : Label n, Label.ofArray? n st.firstlab = some f ∧
    Label.ofArray? n st.canonlab = some c ∧
      Key.Le ⟨fs ++ [codeSentinel], G.relabel f.perm⟩ ⟨bs ++ [codeSentinel], G.relabel c.perm⟩

theorem Comparison.returned {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs st) (hn : st.compCanon ≤ 0) : ReturnCodes G cs bs fs st :=
  ⟨⟨cs, ⟨[], List.append_nil _⟩, .codes h.canonical hn, h.first⟩, h.nonempty, h.lower⟩

namespace ReturnCodes

variable {G : Hex.SparseGraph n} {stem cs bs fs : List Nat} {st out : State n}

theorem «prefix» (h : ReturnCodes G cs bs fs st) (hp : stem <+: cs) : ReturnCodes G stem bs fs st := by
  obtain ⟨ds, hd, hm, hf⟩ := h.machine
  exact ⟨⟨ds, hp.trans hd, hm, hf⟩, h.nonempty, h.lower⟩

theorem read (h : ReturnCodes G stem bs fs st) : State.best G st = State.key G bs st := by
  obtain ⟨_, _, hm, _⟩ := h.machine
  exact settled_read hm

theorem nonpos (h : ReturnCodes G stem bs fs st) : st.compCanon ≤ 0 := by
  obtain ⟨_, _, hm, _⟩ := h.machine
  cases hm with
  | codes _ hn => exact hn
  | rows _ hn => omega

/-- Bookkeeping that retains canonical and first-reference fields
preserves the semantic comparison result, including both parsed labels. -/
theorem fields (h : ReturnCodes G stem bs fs st) (hc : out.canonical = st.canonical)
    (hr : out.reference = st.reference) (he : out.eqlevFirst = st.eqlevFirst) :
    ReturnCodes G stem bs fs out := by
  have hfc := congrArg Prod.fst hr
  have hfl := congrArg (fun r => r.2.2) hr
  have hcl := congrArg (fun r => r.2.2.2.2.1) hc
  change out.firstcode = st.firstcode at hfc
  change out.firstlab = st.firstlab at hfl
  change out.canonlab = st.canonlab at hcl
  obtain ⟨cs, hp, hm, hf⟩ := h.machine
  refine ⟨⟨cs, hp, hm.canonical hc, ?_⟩, h.nonempty, ?_⟩
  · rw [hfc, he]
    exact hf
  · rw [hfl, hcl]
    exact h.lower

theorem leave (h : ReturnCodes G stem bs fs st) (tv : Nat) :
    ReturnCodes G stem bs fs ((policy (n := n)).leaveChild tv st) := h.fields rfl rfl rfl

theorem afterSweep (h : ReturnCodes G stem bs fs st) (first : Bool) (level size index : Nat) :
    ReturnCodes G stem bs fs ((policy (n := n)).afterSweep first level size index st) := by
  change ReturnCodes G stem bs fs (if first then { Nauty.afterSweep first level size index st with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st)
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> exact h.fields rfl rfl rfl

/-- Actual native recovery reconstructs both code machines at the exact
entry prefix, even when the last compared leaf lay several levels below it. -/
theorem recover (h : ReturnCodes G stem bs fs st) (inf : Nat) :
    Comparison G stem bs fs ((policy (n := n)).recover inf stem.length st) := by
  obtain ⟨cs, hp, hm, hf⟩ := h.machine
  have ht : cs.take stem.length = stem := by obtain ⟨tail, rfl⟩ := hp; simp
  refine ⟨?_, ?_, h.nonempty, ?_⟩
  · have hc := hm.recover hp.length_le inf
    rw [ht] at hc
    exact hc
  · have hc := recover_firstCodeInv (st := st) (inf := inf) hf hp.length_le
    rw [← recover_eq, ht] at hc
    exact hc
  · rw [(recover_labels inf stem.length st).1, (recover_labels inf stem.length st).2]
    exact h.lower

end ReturnCodes

/-- Finishing the actual native sweep changes no semantic incumbent. -/
theorem afterSweep_key (G : Hex.SparseGraph n) (bs : List Nat) (first : Bool)
    (level size index : Nat) (st : State n) :
    State.key G bs ((policy (n := n)).afterSweep first level size index st) = State.key G bs st := by
  change State.key G bs (if first then { Nauty.afterSweep first level size index st with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st) = _
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> rfl

/-- Native recovery retains a settled comparison's nonpositive sign. -/
theorem recover_nonpos {st : State n} (h : st.compCanon ≤ 0) (inf level : Nat) :
    ((policy (n := n)).recover inf level st).compCanon ≤ 0 := by
  change (recoverLevels level (recoverPtn inf level st)).compCanon ≤ 0
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.compCanon]
  repeat' split
  all_goals first | exact h | omega

theorem ReturnCodes.resumed {G : Hex.SparseGraph n} {stem bs fs : List Nat} {st : State n}
    (h : ReturnCodes G stem bs fs st) (inf : Nat) :
    ReturnCodes G stem bs fs ((policy (n := n)).recover inf stem.length st) :=
  (h.recover inf).returned (recover_nonpos h.nonpos inf stem.length)

end Hex.GraphIso.Nauty.Sparse
