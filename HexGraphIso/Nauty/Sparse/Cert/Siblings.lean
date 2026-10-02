/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Check

public section

namespace Hex.GraphIso.Nauty.Sparse.Replay

/-- Check one sibling or copy a previously checked attainment flag after
validating the reference's strict order and automorphism witness. -/
@[expose] def sibling (check : Nat → CertNode → Option Bool)
    (witness : Nat → Nat → Array Nat → Bool) (seen : Array Bool) (c : CertNode) : Option Bool :=
  match c with
  | .autom earlier images =>
    if earlier < seen.size ∧ witness seen.size earlier images = true then
      some seen[earlier]!
    else none
  | _ => check seen.size c

/-- Process sibling records in order. Only successful checks enter the flag
array; forward, cyclic, and out-of-range references are rejected. -/
@[expose] def scan (check : Nat → CertNode → Option Bool)
    (witness : Nat → Nat → Array Nat → Bool) : Array Bool → List CertNode → Option (Array Bool)
  | seen, [] => some seen
  | seen, c :: cs => do
    let a ← sibling check witness seen c
    scan check witness (seen.push a) cs

theorem sibling_valid {P : Nat → Bool → Prop} {check : Nat → CertNode → Option Bool}
    {witness : Nat → Nat → Array Nat → Bool} {seen : Array Bool} {c : CertNode} {a : Bool}
    (hcheck : ∀ o c b, check o c = some b → P o b)
    (hcopy : ∀ o earlier raw b, earlier < o → P earlier b →
      witness o earlier raw = true → P o b)
    (hs : ∀ o, o < seen.size → P o seen[o]!)
    (h : sibling check witness seen c = some a) : P seen.size a := by
  cases c with
  | leaf => exact hcheck _ _ _ h
  | codePrune => exact hcheck _ _ _ h
  | node _ => exact hcheck _ _ _ h
  | autom earlier images =>
    simp only [sibling] at h
    split at h
    · rename_i hw
      cases Option.some.inj h
      exact hcopy _ _ _ _ hw.1 (hs _ hw.1) hw.2
    · cases h

private theorem push_valid {P : Nat → Bool → Prop} {seen : Array Bool} {a : Bool}
    (hs : ∀ o, o < seen.size → P o seen[o]!) (ha : P seen.size a) :
    ∀ o, o < (seen.push a).size → P o (seen.push a)[o]! := by
  intro o ho
  by_cases hi : o < seen.size
  · rw [getElem!_pos (seen.push a) o ho, Array.getElem_push_lt hi]
    simpa only [getElem!_pos seen o hi] using hs o hi
  · have he : o = seen.size := by simp only [Array.size_push] at ho; omega
    subst o
    simpa using ha

/-- Every stored flag has a checked justification, and exactly one flag is
stored per accepted record. This includes chains of earlier references. -/
theorem scan_valid {P : Nat → Bool → Prop} {check : Nat → CertNode → Option Bool}
    {witness : Nat → Nat → Array Nat → Bool} {seen flags : Array Bool} {cs : List CertNode}
    (hcheck : ∀ o c b, check o c = some b → P o b)
    (hcopy : ∀ o earlier raw b, earlier < o → P earlier b →
      witness o earlier raw = true → P o b)
    (hs : ∀ o, o < seen.size → P o seen[o]!)
    (h : scan check witness seen cs = some flags) :
    flags.size = seen.size + cs.length ∧ ∀ o, o < flags.size → P o flags[o]! := by
  induction cs generalizing seen with
  | nil =>
    cases Option.some.inj h
    exact ⟨by simp, hs⟩
  | cons c cs ih =>
    rw [scan] at h
    cases he : sibling check witness seen c with
    | none => simp [he] at h
    | some a =>
      simp only [he] at h
      have ha := sibling_valid hcheck hcopy hs he
      have hh := ih (push_valid hs ha) h
      exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh.1, hh.2⟩

/-- A scan succeeds when each record can be checked at its actual offset.
No assumptions about the values of earlier attainment flags are needed. -/
theorem scan_exists {check : Nat → CertNode → Option Bool}
    {witness : Nat → Nat → Array Nat → Bool} {seen : Array Bool} {cs : List CertNode}
    (hsteps : ∀ i (hi : i < cs.length) (s : Array Bool), s.size = seen.size + i →
      ∃ a, sibling check witness s cs[i] = some a) :
    ∃ flags, scan check witness seen cs = some flags := by
  induction cs generalizing seen with
  | nil => exact ⟨seen, rfl⟩
  | cons c cs ih =>
    obtain ⟨a, ha⟩ := hsteps 0 (by simp) seen (by simp)
    have htail : ∀ i (hi : i < cs.length) (s : Array Bool),
        s.size = (seen.push a).size + i → ∃ b, sibling check witness s cs[i] = some b := by
      intro i hi s hs
      have he : s.size = seen.size + (i + 1) := by simp only [Array.size_push] at hs; omega
      exact hsteps (i + 1) (by simp; omega) s he
    obtain ⟨flags, hf⟩ := ih htail
    exact ⟨flags, by simp only [scan, List.getElem_cons_zero] at ha ⊢; rw [ha]; exact hf⟩

end Hex.GraphIso.Nauty.Sparse.Replay
