/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagEncode
public import Std.Data.HashMap.Lemmas

public section

namespace Hex.SignDet.Dag

variable {α : Type w} {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]

/-- Every successful lookup retains the exact value when a memo grows. -/
@[expose] def Prefix (before after : Array α) : Prop :=
  ∀ (i : Nat) t, before[i]? = some t → after[i]? = some t

theorem Prefix.refl (memo : Array α) : Prefix memo memo :=
  fun _ _ h => h

theorem Prefix.trans {x y z : Array α}
    (hxy : Prefix x y) (hyz : Prefix y z) : Prefix x z :=
  fun i t h => hyz i t (hxy i t h)

theorem Prefix.push (memo : Array α) (t) :
    Prefix memo (memo.push t) := by
  intro i v h
  obtain ⟨hi, hv⟩ := Array.getElem?_eq_some_iff.mp h
  simpa only [Array.getElem?_push_lt hi] using congrArg some hv

variable [DecidableEq Ctx] [Hashable E] [Hashable Ctx]

/-- The supplied step function succeeds on the actual graph fold, and each
cached index resolves to that function's exact result. This invariant serves
both checked replay and structural expansion. -/
structure Encoder.Valid (f : Array α → Entry E Ctx → Option α) (state : Encoder E Ctx)
    (memo : Array α) : Prop where
  fold : state.entries.foldlM (init := #[]) (fun memo entry => do
    let next ← f memo entry
    pure (memo.push next)) = some memo
  size : state.entries.size = memo.size
  indices : ∀ entry (i : Nat), state.indices[entry]? = some i →
    ∃ t, memo[i]? = some t ∧ f memo entry = some t

/-- An empty encoder has no unvalidated entries or cache bindings. -/
theorem Encoder.valid_empty (f : Array α → Entry E Ctx → Option α) : Encoder.Valid f ({} : Encoder E Ctx)
    (#[] : Array α) := by
  constructor
  · simp
  · rfl
  · intro entry i h
    simp at h

/-- Interning preserves a successful prefix and binds the returned index to
its exact local result, even when hashes collide. -/
theorem Encoder.insert_valid {f : Array α → Entry E Ctx → Option α}
    (mono : ∀ {before after}, Prefix before after → ∀ {entry t},
      f before entry = some t → f after entry = some t) {state : Encoder E Ctx}
    {memo : Array α} (hv : state.Valid f memo)
    {entry : Entry E Ctx} {t : α}
    (ht : f memo entry = some t) :
    ∃ next : Array α,
      (state.insert entry).1.Valid f next ∧ Prefix memo next ∧
      next[(state.insert entry).2]? = some t := by
  cases hi : state.indices[entry]? with
  | some i =>
    obtain ⟨u, hu, hs⟩ := hv.indices entry i hi
    have he : u = t := Option.some.inj (hs.symm.trans ht)
    subst u
    exact ⟨memo, by simpa only [Encoder.insert, hi] using hv,
      Prefix.refl memo, by simpa only [Encoder.insert, hi] using hu⟩
  | none =>
    refine ⟨memo.push t, ?_, Prefix.push memo t, ?_⟩
    · constructor
      · simp only [Encoder.insert, hi]
        rw [Array.foldlM_push, hv.fold]
        simp only [bind, Option.bind, ht, pure]
      · simp only [Encoder.insert, hi, Array.size_push, hv.size]
      · intro e i h
        simp only [Encoder.insert, hi, Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i he
          have heq : entry = e := eq_of_beq he
          subst e
          cases Option.some.inj h
          exact ⟨t, by simpa only [hv.size] using (Array.getElem?_push_size (xs := memo) (x := t)), mono (Prefix.push memo t) ht⟩
        · obtain ⟨u, hu, hs⟩ := hv.indices e i h
          exact ⟨u, Prefix.push memo t i u hu, mono (Prefix.push memo t) hs⟩
    · simpa only [Encoder.insert, hi, hv.size] using (Array.getElem?_push_size (xs := memo) (x := t))

end Hex.SignDet.Dag
