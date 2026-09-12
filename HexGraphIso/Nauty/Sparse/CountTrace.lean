/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MinimaUnique

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- The observable control fields of count splitting. This projection is
used only in proofs; the executable retains its original working state. -/
structure Control (n : Nat) where
  active : VSet n
  queue : Array Nat
  code : Nat

@[expose] def control (s : RefineSt n) : Control n := ⟨s.active, s.queue, s.longcode⟩

@[expose] def Control.hash (s : Control n) (v : Nat) : Control n :=
  { s with code := mash s.code v }

@[expose] def Control.push (s : Control n) (v : Nat) : Control n :=
  { s with active := s.active.insert v, queue := s.queue.push v }

/-- The exact hash and insertion performed when entering a later count run. -/
@[expose] def Control.advance (s : Control n) (distance : Bool) (k value : Nat) : Control n :=
  let s := (if distance then s.hash k else s).push (k + 1)
  if distance then s else s.hash value

/-- The executed update of the saved largest fragment, including the
singleton guard and strict comparison that retains the earlier tie. -/
@[expose] def Control.choose (s : Control n) (pos : Option Nat) (big size : Nat) : Option Nat × Nat :=
  if size == 1 then (pos, big)
  else if big < size then (some (s.queue.size - 1), size)
  else (pos, big)

/-- Final largest-fragment replacement, with its distance-only hash. -/
@[expose] def Control.finish (s : Control n) (distance : Bool) (first : Nat) (pos : Option Nat) : Control n :=
  match pos with
  | none => s
  | some p =>
    if s.active.mem first then s
    else
      let s := if distance then s.hash p else s
      { s with
        active := (s.active.erase s.queue[p]!).insert first
        queue := s.queue.set! p first }

/-- A derivation of the actual tail scan's control transitions. Each step
consumes one maximal constant-count run; completion includes replacement.
This relation does not run another refinement algorithm. -/
inductive Tail {n : Nat} (distance : Bool) (lab hits : Array Nat) (first last : Nat) :
    Nat → Control n → Option Nat → Nat → Control n → Prop
  | done (hk : last ≤ k + 1) :
      Tail distance lab hits first last k s pos big (s.finish distance first pos)
  | step (hk : k + 1 < last)
      (hr : Index.Run lab hits (k + 1) (last - 1) (k + 1) b)
      (ht : Tail distance lab hits first last b
        (s.advance distance k hits[lab[k + 1]!]!)
        ((s.advance distance k hits[lab[k + 1]!]!).choose pos big (b - (k + 1) + 1)).1
        ((s.advance distance k hits[lab[k + 1]!]!).choose pos big (b - (k + 1) + 1)).2 out) :
      Tail distance lab hits first last k s pos big out

/-- A fixed count sequence determines all tail hashes, queue entries and
the saved-largest tie rule uniquely. -/
theorem Tail.deterministic (h : Tail distance lab hits first last k s pos big out)
    (h' : Tail distance lab hits first last k s pos big other) : out = other := by
  induction h with
  | done hk =>
    cases h' with
    | done => rfl
    | step hh => omega
  | step hk hr ht ih =>
    cases h' with
    | done hh => omega
    | step hh hr' ht' =>
      have bounds := hr.bounds
      have bounds' := hr'.bounds
      have he := hr.disjoint_or_eq hr'
      have heq : _ = _ := he.resolve_left (by omega) |>.resolve_left (by omega) |>.2
      subst heq
      exact ih ht'

/-- Equal count sequences transport the complete tail trace, without
requiring literal equality of the vertex arrays. -/
theorem Tail.congr (h : Tail distance lab hits first last k s pos big out)
    (hk : ∀ q, k + 1 ≤ q → q < last → hits[lab[q]!]! = keys[vertices[q]!]!) :
    Tail distance vertices keys first last k s pos big out := by
  induction h with
  | done hh => exact .done hh
  | @step k b out s pos big hh hr ht ih =>
    have bounds := hr.bounds
    have hr' : Index.Run vertices keys (k + 1) (last - 1) (k + 1) b := by
      refine ⟨bounds, Or.inl rfl, ?_, ?_⟩
      · intro q hq he
        rw [← hk q hq (by omega), ← hk (k + 1) (by omega) hh]
        exact hr.equal q hq he
      · rcases hr.right with he | he
        · exact Or.inl he
        · by_cases hb : b = last - 1
          · exact Or.inl hb
          · right
            rw [← hk b (by omega) (by omega), ← hk (b + 1) (by omega) (by omega)]
            exact he
    have hi := ih (fun q hq he => hk q (by omega) he)
    rw [hk (k + 1) (by omega) hh] at hi
    exact .step hh hr' hi

end Hex.GraphIso.Nauty.Sparse.CountTrace
