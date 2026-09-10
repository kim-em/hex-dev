/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Orbit
public import HexPermGroup.Word.Build

public section

namespace Hex.PermGroup.Action

/-- A signed reference to an original input generator. -/
abbrev Step (G : Group n) := Fin G.generators.size × Bool

namespace Step

variable {G : Group n}

@[expose] def element (s : Step G) : Element G :=
  let p : Element G := ⟨G.generators[s.1.val], .generator (Array.getElem_mem s.1.isLt)⟩
  if s.2 then p.inv else p

@[expose] def all (G : Group n) : List (Step G) :=
  (List.finRange G.generators.size).flatMap fun i => [(i, false), (i, true)]

@[simp] theorem mem_all (s : Step G) : s ∈ all G := by
  obtain ⟨i, b⟩ := s
  cases b <;> simp [all]

/-- Append a signed generator and its left product with an earlier root. -/
@[expose] def advance (s : Step G) (b : Program.Builder G.generators) (r : Fin b.values.size) :
    Program.Builder G.generators :=
  if s.2 then
    let g := b.generator s.1
    let v := g.inv ⟨b.values.size, by simp [g]⟩
    v.comp ⟨b.values.size + 1, by simp [v, g, Program.Builder.inv, Program.Builder.push]⟩
      ⟨r.val, by simp [v, g, Program.Builder.inv, Program.Builder.push]; omega⟩
  else b.act s.1 r

theorem advance_size (s : Step G) (b : Program.Builder G.generators) (r : Fin b.values.size) :
    (s.advance b r).values.size = b.values.size + if s.2 then 3 else 2 := by
  unfold advance
  split <;> simp_all [Program.Builder.inv, Program.Builder.push, Nat.add_assoc]

theorem advance_le (s : Step G) (b : Program.Builder G.generators) (r : Fin b.values.size) :
    b.values.size ≤ (s.advance b r).values.size := by rw [advance_size]; omega

theorem advance_pos (s : Step G) (b : Program.Builder G.generators) (r : Fin b.values.size) :
    0 < (s.advance b r).values.size := by
  rw [advance_size]
  split <;> omega

theorem advance_get (s : Step G) (b : Program.Builder G.generators) (r i : Fin b.values.size) :
    (s.advance b r).values[i.val]'(Nat.lt_of_lt_of_le i.isLt (s.advance_le b r)) = b.values[i.val] := by
  unfold advance
  split
  · simp [Program.Builder.comp, Program.Builder.inv, Program.Builder.generator, Program.Builder.push,
      Array.getElem_push, i.isLt, Nat.lt_succ_of_lt i.isLt,
      Nat.lt_succ_of_lt (Nat.lt_succ_of_lt i.isLt)]
  · exact b.get_act s.1 r i

/-- The appended root denotes precisely the edge permutation times its parent. -/
theorem advance_last (s : Step G) (b : Program.Builder G.generators) (r : Fin b.values.size) :
    (s.advance b r).values[(s.advance b r).values.size - 1]'(by have := s.advance_pos b r; omega) =
      s.element.comp b.values[r.val] := by
  apply Subtype.ext
  unfold advance
  split <;> rename_i hs
  · simp [Program.Builder.comp, Program.Builder.inv, Program.Builder.generator, Program.Builder.push,
      Array.getElem_push, r.isLt, Nat.lt_succ_of_lt r.isLt, element, hs, Nat.add_assoc]
  · simpa [element, hs, b.size_act] using b.last_act s.1 r

end Step

end Hex.PermGroup.Action
