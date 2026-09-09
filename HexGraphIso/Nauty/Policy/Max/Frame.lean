/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Canon.Witness
public import HexGraphIso.Nauty.Policy.First.Compare
import all HexGraphIso.Nauty.Policy.Generic.Maximum
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A frozen node and the refinement codes preceding its entry. -/
structure Frame (n : Nat) where
  level : Nat
  numcells : Nat
  codes : List Nat
  entry : Search n

/-- The full specification subtree at a frozen node. -/
def Frame.key (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) : Key n :=
  prefixKey f.codes (specNode ctx tcLevel (n + 1 - f.level) f.level
    f.entry.lab f.entry.ptn f.entry.active f.numcells)

/-- The first refinement code of a frozen node. -/
def Frame.code (ctx : Ctx n) (f : Frame n) : Nat :=
  (refine ctx f.level f.entry.lab f.entry.ptn f.entry.active f.numcells).longcode

/-- The specification of a nonexhausted frame begins with its refinement code. -/
theorem Frame.tail {ctx : Ctx n} {tcLevel : Nat} {f : Frame n}
    (hlevel : f.level ≤ n) :
    ∃ tail : Key n, f.key ctx tcLevel = prefixKey (f.codes ++ [f.code ctx]) tail := by
  have hfuel : n + 1 - f.level = (n - f.level) + 1 := by omega
  obtain ⟨cs, hcs⟩ := specNode_codes_head ctx tcLevel (n - f.level) f.level
    f.entry.lab f.entry.ptn f.entry.active f.numcells
  refine ⟨⟨cs, (specNode ctx tcLevel (n - f.level + 1) f.level
    f.entry.lab f.entry.ptn f.entry.active f.numcells).rows⟩, ?_⟩
  simp only [Frame.key, hfuel, prefixKey, Frame.code, hcs, List.append_assoc,
    List.singleton_append]

/-- Either a specific ancestor subtree is covered, or a frozen downward
comparison bounds every extension of its first refinement code. -/
def Frame.Witness (ctx : Ctx n) (tcLevel : Nat) (f : Frame n)
    (best : Option (Key n)) : Prop :=
  Generic.Covers (f.key ctx tcLevel) best ∨
    ∀ tail : Key n, Generic.Covers (prefixKey (f.codes ++ [f.code ctx]) tail) best

/-- Both return justifications cover the actual frozen specification subtree. -/
theorem Frame.Witness.resolve {ctx : Ctx n} {tcLevel : Nat} {f : Frame n}
    {best : Option (Key n)} (h : f.Witness ctx tcLevel best) (hlevel : f.level ≤ n) :
    Generic.Covers (f.key ctx tcLevel) best := by
  rcases h with h | h
  · exact h
  · obtain ⟨tail, he⟩ := f.tail (ctx := ctx) (tcLevel := tcLevel) hlevel
    rw [he]
    exact h tail

/-- Frozen ancestor subtrees are indexed by their receiving sweep level. -/
abbrev Frames (n : Nat) := Nat → Option (Frame n)

/-- Install the current node's subtree at its receiving parent. -/
def Frames.insert (frames : Frames n) (f : Frame n) : Frames n :=
  fun level => if level = f.level - 1 then some f else frames level

/-- A nonlocal return carries a justification for the ancestor it names. -/
def Witness (ctx : Ctx n) (tcLevel : Nat) (frames : Frames n)
    (target : Nat) (best : Option (Key n)) : Prop :=
  ∃ f, frames target = some f ∧ f.level ≤ n ∧ f.Witness ctx tcLevel best

/-- A return to the current node's parent resolves its own frozen key. -/
theorem Witness.resolve {ctx : Ctx n} {tcLevel : Nat} {frames : Frames n}
    {f : Frame n} {best : Option (Key n)}
    (h : Witness ctx tcLevel (frames.insert f) (f.level - 1) best) :
    Generic.Covers (f.key ctx tcLevel) best := by
  obtain ⟨other, he, hl, hw⟩ := h
  simp only [Frames.insert, ↓reduceIte, Option.some.injEq] at he
  subst other
  exact hw.resolve hl

/-- Pushing a descendant frame leaves every earlier ancestor unchanged. -/
theorem Witness.below {ctx : Ctx n} {tcLevel target : Nat} {frames : Frames n}
    {f : Frame n} {best : Option (Key n)} (ht : target < f.level - 1) :
    Witness ctx tcLevel (frames.insert f) target best ↔
      Witness ctx tcLevel frames target best := by
  simp only [Witness, Frames.insert, ite_eq_right (by omega : target ≠ f.level - 1)]

end Hex.GraphIso.Nauty.Max
