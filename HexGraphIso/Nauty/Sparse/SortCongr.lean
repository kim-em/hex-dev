/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Window
public import HexGraphIso.Nauty.Sparse.LoopRel
import all HexGraphIso.Nauty.Sparse.LoopRel

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

/-- The two key arrays agree on entries currently stored in a bounded
segment. Neither array is constrained on vertices outside that segment. -/
structure Agree (y z : Array Nat) (lo hi : Nat) (x : Array Nat) : Prop where
  bound : hi ≤ x.size
  keys : ∀ q, lo ≤ q → q < hi → y[x[q]!]! = z[x[q]!]!

namespace Agree

theorem mono (h : Agree y z lo hi x) (hf : lo ≤ first) (hl : last ≤ hi) :
    Agree y z first last x :=
  ⟨by have := h.bound; omega, fun q hq hb => h.keys q (by omega) (by omega)⟩

theorem write (h : Agree y z lo hi x) (hk : y[v]! = z[v]!) (i : Nat) :
    Agree y z lo hi (x.set! i v) := by
  refine ⟨by simpa using h.bound, ?_⟩
  intro q hq hb
  rw [Sparse.get_set _ _ _ _ (by have := h.bound; omega)]
  split
  · exact hk
  · exact h.keys q hq hb

theorem swap (h : Agree y z lo hi x)
    (hi' : lo ≤ i ∧ i < hi) (hj : lo ≤ j ∧ j < hi) :
    Agree y z lo hi (x.swapIfInBounds i j) := by
  refine ⟨by simpa using h.bound, ?_⟩
  intro q hq hb
  have hs := h.bound
  rw [get_swap _ _ _ _ (by omega) (by omega) (by omega)]
  split
  · exact h.keys j hj.1 hj.2
  · split
    · exact h.keys i hi'.1 hi'.2
    · exact h.keys q hq hb

theorem window (h : Agree y z lo hi x) (hw : Window x out lo hi) :
    Agree y z lo hi out := by
  have hb : hi ≤ out.size := by rw [hw.size]; exact h.bound
  refine ⟨hb, ?_⟩
  intro q hq hq'
  obtain ⟨r, hr, hr', he⟩ := hw.mem hb ⟨hq, hq'⟩
  rw [he]
  exact h.keys r hr hr'

end Agree

/-- Both pinned pivot sampling schemes read only their nonempty segment. -/
theorem pivot_congr (h : Agree y z start (start + len) x) (hl : 0 < len) :
    pivot x y start len = pivot x z start len := by
  have hk (i : Nat) (hi : i < len) : y[x[start + i]!]! = z[x[start + i]!]! :=
    h.keys _ (by omega) (by omega)
  unfold pivot
  split <;> dsimp only
  · rw [hk 0 (by omega), hk (len / 2) (by omega), hk (len - 1) (by omega)]
  · rw [hk 0 (by omega), hk 1 (by omega), hk 2 (by omega),
      hk (len / 2 - 1) (by omega), hk (len / 2) (by omega), hk (len / 2 + 1) (by omega),
      hk (len - 3) (by omega), hk (len - 2) (by omega), hk (len - 1) (by omega)]

/-- One literal inner insertion loop and its final saved-entry write. -/
private noncomputable def insert (x y : Array Nat) (start i : Nat) : Array Nat :=
  let value := x[start + i]!
  let step (_ : Nat) (s : Array Nat × Nat) : Id (ForInStep (Array Nat × Nat)) :=
    if y[s.1[start + s.2 - 1]!]! ≤ y[value]! then .done s
    else
      let next := (s.1.set! (start + s.2) s.1[start + s.2 - 1]!, s.2 - 1)
      if next.2 == 0 then .done next else .yield next
  let r := forIn [0:i] (x, i) step
  r.1.set! (start + r.2) value

private theorem insert_congr (h : Agree y z start last x) (hi : 0 < i)
    (hb : start + i < last) :
    insert x y start i = insert x z start i ∧ Agree y z start last (insert x y start i) := by
  let value := x[start + i]!
  let step (keys : Array Nat) (_ : Nat) (s : Array Nat × Nat) : Id (ForInStep (Array Nat × Nat)) :=
    if keys[s.1[start + s.2 - 1]!]! ≤ keys[value]! then .done s
    else
      let next := (s.1.set! (start + s.2) s.1[start + s.2 - 1]!, s.2 - 1)
      if next.2 == 0 then .done next else .yield next
  let P (s : Array Nat × Nat) := Agree y z start last s.1 ∧ 0 < s.2 ∧ s.2 ≤ i
  let Q (s : Array Nat × Nat) := Agree y z start last s.1 ∧ s.2 ≤ i
  have hv : y[value]! = z[value]! := h.keys _ (by omega) hb
  have hr := Loop.range_congr 0 i (step y) (step z) P Q
    (fun s hs => ⟨hs.1, hs.2.2⟩) (by
      intro j hj hj' a ha
      have hk := ha.1.keys (start + a.2 - 1) (by have := ha.2; omega) (by have := ha.2; omega)
      refine ⟨?_, ?_⟩
      · dsimp only [step]
        rw [hk, hv]
      · dsimp only [step]
        split
        · exact ⟨ha.1, ha.2.2⟩
        · have hn := ha.1.write hk (start + a.2)
          split
          · exact ⟨hn, by have := ha.2; omega⟩
          · exact ⟨hn, by simp_all only [beq_iff_eq]; omega, by have := ha.2; omega⟩)
    (show P (x, i) from ⟨h, hi, Nat.le_refl _⟩)
  constructor
  · exact congrArg (fun r : Array Nat × Nat => r.1.set! (start + r.2) value) hr.1
  · exact hr.2.1.write hv _

/-- The exact short-segment insertion sort is unaffected by keys outside
the segment. Equal-key stability is retained literally. -/
theorem insertion_congr (h : Agree y z start (start + len) x) :
    insertion x y start len = insertion x z start len := by
  let step (keys : Array Nat) (i : Nat) (a : Array Nat) : Id (ForInStep (Array Nat)) :=
    .yield (insert a keys start i)
  have hr := Loop.range_congr 1 len (step y) (step z)
    (Agree y z start (start + len)) (Agree y z start (start + len)) (fun _ h => h) (by
      intro i hi hb a ha
      have hc := insert_congr (i := i) ha (by omega) (by omega)
      exact ⟨congrArg ForInStep.yield hc.1, hc.2⟩) h
  simpa only [insertion, insert, step, Id.run, bind, pure] using hr.1

end Hex.GraphIso.Nauty.Sparse.Sort
