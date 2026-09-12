/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LimitNode
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Limited

/-- Exact projection to the native recursion on every successful return.
No validity assumption on the raw search state is needed for this comparison. -/
def agreement (g : Graph n) (inf tcLevel : Nat) : Generic.Contract (State n) n where
  nodePre _ _ _ _ _ := True
  nodePost fuel first level nc s r := Ready r.2 →
    Ready s ∧ nodeValue r = Generic.node first g inf tcLevel fuel level nc s.value
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost fuel cfuel first level nc tc tv1 cursor cell index s r := Ready r.2.2 →
    Ready s ∧ sweepValue r =
      Generic.sweep first g inf tcLevel fuel cfuel level nc tc tv1 cursor cell index s.value

/-- The actual bounded callbacks satisfy all local rules of the shared
engine; the recursive premises concern only its supplied smaller calls. -/
theorem agreementPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.SoundPolicy g inf tcLevel (agreement g inf tcLevel) where
  node_zero := by
    intro first level nc s _ hr
    exact ⟨hr, by rw [Generic.node]; rfl⟩
  node_step := by
    intro fuel next hn first level nc s _ hr
    change Ready s ∧ nodeValue (Generic.nodeStep g tcLevel next first level nc s) =
      Generic.node first g inf tcLevel (fuel + 1) level nc s.value
    rw [Generic.node]
    exact nodeStep_value (fun first level nc tc tv1 cursor cell index s h =>
      hn first level nc tc tv1 cursor cell index s trivial h) g tcLevel first level nc s hr
  sweep_none := by
    intro fuel cfuel first level nc tc tv1 cell index s _ hr
    exact ⟨hr, by rw [Generic.sweep]; rfl⟩
  sweep_zero := by
    intro fuel first level nc tc tv1 tv cell index s _ hr
    exact ⟨hr, by rw [Generic.sweep]; rfl⟩
  sweep_step := by
    intro fuel cfuel descend next hd hn first level nc tc tv1 tv cell index s _ hr
    change Ready s ∧ sweepValue (Generic.sweepStep inf descend next first level nc tc tv1 tv cell index s) =
      Generic.sweep first g inf tcLevel fuel (cfuel + 1) level nc tc tv1 (some tv) cell index s.value
    rw [Generic.sweep]
    exact sweepStep_eq (fun first level nc s h => hd first level nc s trivial h)
      (fun first level nc tc tv1 cursor cell index s h => hn first level nc tc tv1 cursor cell index s trivial h)
      inf first level nc tc tv1 tv index cell s hr

/-- Every successful bounded node has the native engine's exact exit and
complete state, including scratch, generator trace and all diagnostics. -/
theorem node_eq (g : Graph n) (inf tcLevel fuel level nc : Nat) (first : Bool) (s : State n)
    (h : Ready (Generic.node first g inf tcLevel fuel level nc s).2) :
    Ready s ∧ nodeValue (Generic.node first g inf tcLevel fuel level nc s) =
      Generic.node first g inf tcLevel fuel level nc s.value :=
  Generic.node_sound (agreementPolicy g inf tcLevel) first fuel level nc s trivial h

theorem sweep_eq (g : Graph n) (inf tcLevel fuel cfuel level nc tc tv1 : Nat)
    (first : Bool) (cursor : Option Nat) (cell : VSet n) (index : Nat) (s : State n)
    (h : Ready (Generic.sweep first g inf tcLevel fuel cfuel level nc tc tv1 cursor cell index s).2.2) :
    Ready s ∧ sweepValue (Generic.sweep first g inf tcLevel fuel cfuel level nc tc tv1 cursor cell index s) =
      Generic.sweep first g inf tcLevel fuel cfuel level nc tc tv1 cursor cell index s.value :=
  Generic.sweep_sound (agreementPolicy g inf tcLevel) first fuel cfuel level nc tc tv1 cursor cell index s trivial h

/-- A successful bounded root returns the direct runner's entire state. -/
theorem run?_eq {limit : Nat} {g : Graph n} {lab : Array Nat} {ends : List Nat}
    {s : State n} (h : run? limit g lab ends = some s) : s.value = Sparse.run g lab ends := by
  unfold run? at h
  split at h
  · cases h
  · split at h
    · rename_i hn
      cases Option.some.inj h
      simp only [Sparse.run, Sparse.runState, hn, beq_self_eq_true, ite_true]
    · rename_i hn
      dsimp only at h
      split at h
      · cases h
      · rename_i hr
        cases Option.some.inj h
        have hready : Ready (Generic.node true g (n + 2) 100 (n + 2) 1 ends.length
            ({ value := Sparse.initial g lab ends, remaining := limit } : State n)).2 := by
          simp only [Bool.or_eq_true, not_or] at hr
          dsimp only [Ready]
          cases he : (Generic.node true g (n + 2) 100 (n + 2) 1 ends.length
            ({ value := Sparse.initial g lab ends, remaining := limit } : State n)).2.exhausted
          · rfl
          · exact False.elim (hr.1 he)
        have he := (node_eq g (n + 2) 100 (n + 2) 1 ends.length true _ hready).2
        change Sparse.finish g _ = Sparse.run g lab ends
        simp only [Sparse.run, Sparse.runState, beq_iff_eq, hn, ite_false]
        exact congrArg (Sparse.finish g) (congrArg Prod.snd he)

theorem runColored?_eq {limit : Nat} {G : GraphIso.Sparse.Colored n k} {s : State n}
    (h : runColored? limit G = some s) : s.value = Sparse.runColored G := run?_eq h

theorem runPair?_eq {limit : Nat} {G H : GraphIso.Sparse.Colored n k} {a b : State n}
    (h : runPair? limit G H = some (a, b)) :
    a.value = Sparse.runColored G ∧ b.value = Sparse.runColored H := by
  change (runColored? limit G).bind (fun sa =>
    (runColored? sa.remaining H).bind (fun sb => some (sa, sb))) = some (a, b) at h
  obtain ⟨sa, ha, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sb, hb, he⟩ := Option.bind_eq_some_iff.mp ht
  cases Option.some.inj he
  exact ⟨runColored?_eq ha, runColored?_eq hb⟩

end Hex.GraphIso.Nauty.Sparse.Limited
