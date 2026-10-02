/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Records

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Quota

/-- Produce siblings in order, passing only the unused record quota to the
next sibling. Failure stops the walk before producing another record. -/
def collect (f : Nat → Nat → Option (CertNode × Nat)) :
    List Nat → Nat → Option (List CertNode × Nat)
  | [], remaining => some ([], remaining)
  | o :: os, remaining =>
    (f o remaining).bind fun (c, rest) =>
      (collect f os rest).map fun (cs, final) => (c :: cs, final)

/-- An automorphism reference costs one record. Failed proposals delegate
to the lazy bounded fallback without consuming an additional record. -/
def emit (choose : Nat → Option (Nat × Array Nat))
    (witness : Nat → Nat → Array Nat → Bool)
    (fallback : Nat → Nat → Option (CertNode × Nat)) (o remaining : Nat) :
    Option (CertNode × Nat) :=
  if remaining = 0 then none else
    match choose o with
    | some (earlier, images) =>
      if earlier < o ∧ witness o earlier images = true then
        some (.autom earlier images, remaining - 1)
      else fallback o remaining
    | none => fallback o remaining

/-- The sibling traversal charges exactly the records it actually returns. -/
theorem collect_budget {f : Nat → Nat → Option (CertNode × Nat)}
    {os : List Nat} {remaining final : Nat} {cs : List CertNode}
    (hf : ∀ o ∈ os, ∀ q c rest, f o q = some (c, rest) → c.stats.records + rest = q)
    (h : collect f os remaining = some (cs, final)) :
    (CertNode.statsList cs).records + final = remaining := by
  induction os generalizing remaining final cs with
  | nil =>
    simp only [collect, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [CertNode.statsList, Nat.zero_add]
  | cons o os ih =>
    simp only [collect] at h
    cases he : f o remaining with
    | none => simp only [he, Option.bind_none, reduceCtorEq] at h
    | some r =>
      obtain ⟨c, rest⟩ := r
      simp only [he, Option.bind_some] at h
      cases ht : collect f os rest with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some r =>
        obtain ⟨tail, last⟩ := r
        simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc := hf o (by simp) remaining c rest he
        have hs := ih (fun i hi => hf i (by simp [hi])) ht
        dsimp only [CertNode.statsList]
        omega

theorem emit_budget {choose : Nat → Option (Nat × Array Nat)}
    {witness : Nat → Nat → Array Nat → Bool}
    {fallback : Nat → Nat → Option (CertNode × Nat)} {o remaining final : Nat} {c : CertNode}
    (hf : ∀ q c rest, fallback o q = some (c, rest) → c.stats.records + rest = q)
    (h : emit choose witness fallback o remaining = some (c, final)) :
    c.stats.records + final = remaining := by
  unfold emit at h
  split at h
  · cases h
  · rename_i hq
    split at h
    · split at h
      · cases Option.some.inj h
        simp only [CertNode.stats]
        omega
      · exact hf _ _ _ h
    · exact hf _ _ _ h

/-- Quota threading retains every successfully produced sibling verbatim. -/
theorem collect_eq {f : Nat → Nat → Option (CertNode × Nat)} {plain : Nat → CertNode}
    {os : List Nat} {remaining final : Nat} {cs : List CertNode}
    (hf : ∀ o ∈ os, ∀ q c rest, f o q = some (c, rest) → c = plain o)
    (h : collect f os remaining = some (cs, final)) : cs = os.map plain := by
  induction os generalizing remaining final cs with
  | nil =>
    simp only [collect, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  | cons o os ih =>
    simp only [collect] at h
    cases he : f o remaining with
    | none => simp only [he, Option.bind_none, reduceCtorEq] at h
    | some r =>
      obtain ⟨c, rest⟩ := r
      simp only [he, Option.bind_some] at h
      cases ht : collect f os rest with
      | none => simp only [ht, Option.map_none, reduceCtorEq] at h
      | some r =>
        obtain ⟨tail, last⟩ := r
        simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [List.map_cons, hf o (by simp) _ _ _ he, ih (fun i hi => hf i (by simp [hi])) ht]

/-- A successful bounded emission is exactly the unlimited emission. -/
theorem emit_eq {choose : Nat → Option (Nat × Array Nat)}
    {witness : Nat → Nat → Array Nat → Bool}
    {fallback : Nat → Nat → Option (CertNode × Nat)} {plain : Nat → CertNode}
    {o remaining final : Nat} {c : CertNode}
    (hf : ∀ q c rest, fallback o q = some (c, rest) → c = plain o)
    (h : emit choose witness fallback o remaining = some (c, final)) :
    c = Replay.emit choose witness plain o := by
  unfold emit at h
  split at h
  · cases h
  · unfold Replay.emit
    cases he : choose o with
    | none =>
      simp only [he] at h ⊢
      exact hf _ _ _ h
    | some r =>
      obtain ⟨earlier, raw⟩ := r
      simp only [he] at h ⊢
      by_cases hw : earlier < o ∧ witness o earlier raw = true
      · simp only [hw] at h ⊢
        exact (Prod.mk.inj (Option.some.inj h)).1.symm
      · simp only [hw, ite_false] at h ⊢
        exact hf _ _ _ h

/-- A quota covering all sibling records suffices for their sequential
production, with exactly their total cost subtracted. -/
theorem collect_complete {f : Nat → Nat → Option (CertNode × Nat)} {plain : Nat → CertNode}
    (os : List Nat) (remaining : Nat)
    (hf : ∀ o ∈ os, ∀ q, (plain o).stats.records ≤ q →
      f o q = some (plain o, q - (plain o).stats.records))
    (hq : (CertNode.statsList (os.map plain)).records ≤ remaining) :
    collect f os remaining =
      some (os.map plain, remaining - (CertNode.statsList (os.map plain)).records) := by
  induction os generalizing remaining with
  | nil => simp only [collect, List.map_nil, CertNode.statsList, Nat.sub_zero]
  | cons o os ih =>
    have hhead : (plain o).stats.records ≤ remaining := by
      simp only [List.map_cons, CertNode.statsList] at hq
      omega
    have htail : (CertNode.statsList (os.map plain)).records ≤
        remaining - (plain o).stats.records := by
      simp only [List.map_cons, CertNode.statsList] at hq
      omega
    rw [collect, hf o (by simp) remaining hhead]
    simp only [Option.bind_some]
    rw [ih _ (fun i hi => hf i (by simp [hi])) htail]
    simp only [Option.map_some, List.map_cons, CertNode.statsList, Nat.sub_sub]

/-- A reference or fallback succeeds when its actual record size fits.
Proposals that fail checking consume no record before the fallback. -/
theorem emit_complete {choose : Nat → Option (Nat × Array Nat)}
    {witness : Nat → Nat → Array Nat → Bool}
    {fallback : Nat → Nat → Option (CertNode × Nat)} {plain : Nat → CertNode}
    (o remaining : Nat)
    (hf : ∀ q, (plain o).stats.records ≤ q →
      fallback o q = some (plain o, q - (plain o).stats.records))
    (hq : (Replay.emit choose witness plain o).stats.records ≤ remaining) :
    emit choose witness fallback o remaining = some (Replay.emit choose witness plain o,
      remaining - (Replay.emit choose witness plain o).stats.records) := by
  have hpos := (Replay.emit choose witness plain o).records_pos
  have hne : remaining ≠ 0 := by omega
  simp only [emit, hne, ite_false, Replay.emit]
  cases he : choose o with
  | none =>
    exact hf remaining (by simpa only [Replay.emit, he] using hq)
  | some r =>
    obtain ⟨earlier, raw⟩ := r
    by_cases hw : earlier < o ∧ witness o earlier raw = true
    · simp only [hw, and_self, ite_true, CertNode.stats]
    · simp only [hw, ite_false]
      exact hf remaining (by simpa only [Replay.emit, he, hw, ite_false] using hq)

end Hex.GraphIso.Nauty.Sparse.Quota
