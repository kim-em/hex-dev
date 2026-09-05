/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CanonSpec

public section

/-!
Leaf-comparison faithfulness: the transcription's `testcanlab` /
`updatecan` leaf handling implements model-level key comparison.

At a leaf tied on codes, `processnode` brings the stored canonical
graph up to date (`updatecan` overwrites rows `samerows..n-1` with
the incumbent `canonlab`'s rows) and compares the fresh leaf against
it row by row (`testcanlab`). This file characterizes both against
the specification's `leafRows`:

- `updatecan_inv`: under the store invariant `CanongInv`, the updated
  store holds exactly the leaf rows of `canonlab`;
- `testcanlab_fst` / `testcanlab_prefix` / `testcanlab_snd_le`:
  `testcanlab` returns the trichotomy of the lexicographic `VSet.rowCmp`
  comparison of `leafRows ctx lab` against the stored rows, and its
  second component is a leading-agreement count;
- `leafEvent_faithful`: the packaged per-leaf clause — the comparison
  outcome is `listCmp VSet.rowCmp (leafRows ctx lab) (leafRows ctx
  canonlab)`, and the out-state store satisfies the invariant both at
  `n` against the incumbent and at the returned prefix length against
  the fresh leaf, re-establishing `CanongInv` whichever way the leaf
  resolves (code `3` installs `lab` with `samerows := sr`, the other
  codes keep `canonlab` with `samerows = n`);
- `keyCmp_codes_eq`: on equal code lists the key comparison is the
  row comparison, connecting the trichotomy to `keyCmp` on leaf keys.

`CanongInv` is stated as an explicit hypothesis; its propagation
across the non-leaf events of the search is the simulation
induction's obligation.
-/

namespace Hex.GraphIso.Nauty

/-- The leaf row of `g^lab` at position `i`: entry `i` of the leaf
key's row list. -/
@[expose] def leafRow (ctx : Ctx n) (lab : Array Nat) (i : Nat) : VSet n :=
  ctx.g[lab[i]!]!.permset (invPerm lab)

theorem leafRows_eq_map (ctx : Ctx n) (lab : Array Nat) :
    leafRows ctx lab = (List.range n).map (leafRow ctx lab) := rfl

/-- The comparison trichotomy in nauty's `Int` convention. -/
@[expose] def ordInt : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- The stored-canonical-graph invariant at `samerows`: the store has
one row per vertex and its first `samerows` rows are the leaf rows of
`canonlab`. -/
def CanongInv (ctx : Ctx n) (canong : Array (VSet n)) (canonlab : Array Nat)
    (samerows : Nat) : Prop :=
  canong.size = n ∧
    ∀ i, i < samerows → canong[i]! = leafRow ctx canonlab i

/-- The store size, projected out of the invariant. -/
theorem canongInv_size {ctx : Ctx n} {canong : Array (VSet n)} {canonlab : Array Nat}
    {samerows : Nat} (hinv : CanongInv ctx canong canonlab samerows) :
    canong.size = n :=
  hinv.1

/-- The invariant with no rows recorded is the size fact alone: the
form every fresh install re-seeds. -/
theorem canongInv_zero {ctx : Ctx n} {canong : Array (VSet n)}
    (canonlab : Array Nat) (hsz : canong.size = n) :
    CanongInv ctx canong canonlab 0 :=
  ⟨hsz, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- A store satisfying the invariant at `n` holds the leaf rows
of its incumbent as its row list. -/
theorem rows_of_canongInv {ctx : Ctx n} {canong : Array (VSet n)} {canonlab : Array Nat}
    (hinv : CanongInv ctx canong canonlab n) :
    (List.range n).map (canong[·]!) = leafRows ctx canonlab := by
  rw [leafRows_eq_map]
  exact List.map_congr_left fun i hi => hinv.2 i (List.mem_range.mp hi)

/-! **Loop translations** -/

/-- `[s:e]` unfolds to a `forIn` over `List.range'`. -/
private theorem forIn_range'_eq {β : Type} (s e : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [s:e] init f : Id β) = forIn (List.range' s (e - s)) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [s:e].start [s:e].size [s:e].step
      = List.range' s (e - s) := by
    have hsize : [s:e].size = e - s := by
      simp [Std.Legacy.Range.size]
    rw [hsize]
  rw [hrange]

/-- `[0:n]` unfolds to a `forIn` over `List.range n`. -/
private theorem forIn_range_eq {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [forIn_range'_eq]
  have h : List.range' 0 (n - 0) = List.range n := by
    simp [List.range_eq_range']
  rw [h]

/-! **`updatecan`** -/

private theorem forIn_set_eq_foldl (ctx : Ctx n) (lab : Array Nat) :
    ∀ (L : List Nat) (g : Array (VSet n)),
      (forIn L g (fun i s =>
          pure (ForInStep.yield (s.set! i (leafRow ctx lab i)))) :
        Id (Array (VSet n))) =
        L.foldl (fun a i => a.set! i (leafRow ctx lab i)) g := by
  intro L
  induction L with
  | nil => intro g; rfl
  | cons a as ih =>
    intro g
    rw [List.forIn_cons]
    exact ih _

private theorem updatecan_eq_foldl (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (samerows : Nat) :
    updatecan ctx canong lab samerows =
      (List.range' samerows (n - samerows)).foldl
        (fun a i => a.set! i (leafRow ctx lab i)) canong := by
  have h0 : updatecan ctx canong lab samerows =
      (forIn [samerows:n] canong (fun i s =>
          pure (ForInStep.yield (s.set! i (leafRow ctx lab i)))) :
        Id (Array (VSet n))) := rfl
  rw [h0, forIn_range'_eq]
  exact forIn_set_eq_foldl ctx lab _ canong

private theorem foldl_set_size (ctx : Ctx n) (lab : Array Nat) :
    ∀ (len s : Nat) (g : Array (VSet n)),
      ((List.range' s len).foldl
        (fun a i => a.set! i (leafRow ctx lab i)) g).size = g.size := by
  intro len
  induction len with
  | zero => intro s g; rfl
  | succ m ih =>
    intro s g
    rw [List.range'_succ, List.foldl_cons, ih, Array.size_set!]

private theorem foldl_set_getElem! (ctx : Ctx n) (lab : Array Nat) :
    ∀ (len s : Nat) (g : Array (VSet n)) (j : Nat),
      ((List.range' s len).foldl
          (fun a i => a.set! i (leafRow ctx lab i)) g)[j]! =
        if s ≤ j ∧ j < s + len ∧ j < g.size then leafRow ctx lab j
        else g[j]! := by
  intro len
  induction len with
  | zero =>
    intro s g j
    rw [ite_eq_right (by omega)]
    rfl
  | succ m ih =>
    intro s g j
    rw [List.range'_succ, List.foldl_cons, ih, Array.size_set!]
    rcases Decidable.em (s + 1 ≤ j ∧ j < s + 1 + m ∧ j < g.size) with h1 | h1
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      rcases Decidable.em (j = s) with rfl | hne
      · rcases Nat.lt_or_ge j g.size with hlt | hge
        · rw [Array.getElem!_set!_self _ _ _ hlt, ite_eq_left (by omega)]
        · rw [getElem!_neg _ _ (by rw [Array.size_set!]; omega),
            ite_eq_right (by omega), getElem!_neg _ _ (by omega)]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne),
          ite_eq_right (by omega)]

theorem size_updatecan (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (samerows : Nat) :
    (updatecan ctx canong lab samerows).size = canong.size := by
  rw [updatecan_eq_foldl]
  exact foldl_set_size ctx lab _ _ canong

theorem getElem!_updatecan (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (samerows : Nat) (j : Nat) :
    (updatecan ctx canong lab samerows)[j]! =
      if samerows ≤ j ∧ j < n ∧ j < canong.size then
        leafRow ctx lab j
      else canong[j]! := by
  rw [updatecan_eq_foldl, foldl_set_getElem!]
  rcases Decidable.em
      (samerows ≤ j ∧ j < samerows + (n - samerows) ∧
        j < canong.size) with h | h
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Under the `samerows` invariant, `updatecan` installs exactly the
leaf rows of the incumbent. -/
theorem updatecan_inv {ctx : Ctx n} {canong : Array (VSet n)} {canonlab : Array Nat}
    {samerows : Nat} (hinv : CanongInv ctx canong canonlab samerows) :
    CanongInv ctx (updatecan ctx canong canonlab samerows)
      canonlab n := by
  obtain ⟨hsz, hpre⟩ := hinv
  refine ⟨by rw [size_updatecan, hsz], fun i hi => ?_⟩
  rw [getElem!_updatecan]
  rcases Nat.lt_or_ge i samerows with hlt | hge
  · rw [ite_eq_right (by omega)]
    exact hpre i hlt
  · rw [ite_eq_left (by omega)]

/-! **`testcanlab`** -/

/-- The first `some` value of `f` along a list. -/
private def firstHit {α β : Type} (f : α → Option β) :
    List α → Option β
  | [] => none
  | a :: as =>
    match f a with
    | some v => some v
    | none => firstHit f as

/-- A scan body over state `Option β × Unit` that on the live state
either yields (no hit) or is done with the element's hit value. -/
private def HitGate {β : Type}
    (body : Option β × Unit → Id (ForInStep (Option β × Unit)))
    (hit : Option β) : Prop :=
  (hit = none → body (none, ()) = pure (ForInStep.yield (none, ()))) ∧
  ∀ v, hit = some v →
    body (none, ()) = pure (ForInStep.done (some v, ()))

/-- A guarded scan's flag is the first hit. -/
private theorem forIn_scan_hits {α β : Type} (L : List α)
    (b : α → Option β × Unit → Id (ForInStep (Option β × Unit)))
    (f : α → Option β) (hgate : ∀ a, HitGate (b a) (f a)) :
    (forIn L (none, ()) b : Id (Option β × Unit)).1 = firstHit f L := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons]
    cases hf : f a with
    | none =>
      rw [(hgate a).1 hf]
      have hstep : firstHit f (a :: as) = firstHit f as := by
        simp only [firstHit, hf]
      rw [hstep]
      exact ih
    | some v =>
      rw [(hgate a).2 v hf]
      have hstep : firstHit f (a :: as) = some v := by
        simp only [firstHit, hf]
      rw [hstep]
      rfl

/-- The per-position hit of `testcanlab`'s scan. -/
private def tclHit (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) (i : Nat) :
    Option (Int × Nat) :=
  match VSet.rowCmp (leafRow ctx lab i) canong[i]! with
  | .lt => some (-1, i)
  | .gt => some (1, i)
  | .eq => none

/-- The loop body of `testcanlab`, spelled with the named matcher so
it is definitionally the `do`-desugaring. -/
private def tclBody (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) (i : Nat)
    (__s : Option (Int × Nat) × Unit) :
    Id (ForInStep (Option (Int × Nat) × Unit)) :=
  testcanlab.match_1
    (fun _ => Id (ForInStep (Option (Int × Nat) × Unit)))
    (VSet.rowCmp (leafRow ctx lab i) canong[i]!)
    (fun _ => pure (ForInStep.done (some (-1, i), ())))
    (fun _ => pure (ForInStep.done (some (1, i), ())))
    (fun _ => pure (ForInStep.yield (none, ())))

private theorem testcanlab_eq_scan (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) :
    testcanlab ctx canong lab =
      Break.runK.match_1 (fun _ => Int × Nat)
        (forIn (List.range n) (none, ())
          (tclBody ctx canong lab) :
            Id (Option (Int × Nat) × Unit)).fst
        (fun r => r) (fun _ => (0, n)) := by
  have h0 : testcanlab ctx canong lab =
      Break.runK.match_1 (fun _ => Int × Nat)
        (forIn [0:n] (none, ()) (tclBody ctx canong lab) :
          Id (Option (Int × Nat) × Unit)).fst
        (fun r => r) (fun _ => (0, n)) := rfl
  rw [h0, forIn_range_eq]

private theorem tclBody_gate (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat)
    (i : Nat) :
    HitGate (tclBody ctx canong lab i) (tclHit ctx canong lab i) := by
  cases hcmp : VSet.rowCmp (leafRow ctx lab i) canong[i]! with
  | lt =>
    refine ⟨fun h => ?_, fun v hv => ?_⟩
    · rw [tclHit, hcmp] at h
      simp at h
    · rw [tclHit, hcmp] at hv
      cases hv
      rw [tclBody, hcmp]
  | gt =>
    refine ⟨fun h => ?_, fun v hv => ?_⟩
    · rw [tclHit, hcmp] at h
      simp at h
    · rw [tclHit, hcmp] at hv
      cases hv
      rw [tclBody, hcmp]
  | eq =>
    refine ⟨fun _ => ?_, fun v hv => ?_⟩
    · rw [tclBody, hcmp]
    · rw [tclHit, hcmp] at hv
      simp at hv

private theorem testcanlab_eq_firstHit (ctx : Ctx n)
    (canong : Array (VSet n)) (lab : Array Nat) :
    testcanlab ctx canong lab =
      (firstHit (tclHit ctx canong lab)
        (List.range n)).getD (0, n) := by
  rw [testcanlab_eq_scan,
    forIn_scan_hits (List.range n) (tclBody ctx canong lab)
      (tclHit ctx canong lab) (tclBody_gate ctx canong lab)]
  cases firstHit (tclHit ctx canong lab) (List.range n) <;> rfl

/-- One induction along `range' s len`: either every row agrees (no
hit, `listCmp` ties) or there is a first difference at `j` with the
prefix agreeing and the hit and `listCmp` matching its trichotomy. -/
private theorem firstHit_trichotomy (ctx : Ctx n)
    (canong : Array (VSet n)) (lab : Array Nat) :
    ∀ (len s : Nat),
      (firstHit (tclHit ctx canong lab) (List.range' s len) = none ∧
        listCmp VSet.rowCmp ((List.range' s len).map (leafRow ctx lab))
          ((List.range' s len).map (canong[·]!)) = .eq ∧
        ∀ i, s ≤ i → i < s + len →
          leafRow ctx lab i = canong[i]!) ∨
      (∃ j c, s ≤ j ∧ j < s + len ∧
        (∀ i, s ≤ i → i < j → leafRow ctx lab i = canong[i]!) ∧
        VSet.rowCmp (leafRow ctx lab j) canong[j]! = c ∧ c ≠ .eq ∧
        firstHit (tclHit ctx canong lab) (List.range' s len) =
          some (ordInt c, j) ∧
        listCmp VSet.rowCmp ((List.range' s len).map (leafRow ctx lab))
          ((List.range' s len).map (canong[·]!)) = c) := by
  intro len
  induction len with
  | zero =>
    intro s
    exact Or.inl ⟨rfl, rfl, fun i h1 h2 => absurd h2 (by omega)⟩
  | succ m ih =>
    intro s
    rw [List.range'_succ]
    cases hcmp : VSet.rowCmp (leafRow ctx lab s) canong[s]! with
    | eq =>
      have hhead : leafRow ctx lab s = canong[s]! :=
        VSet.rowCmp_eq_iff.mp hcmp
      rcases ih (s + 1) with ⟨hfh, hlc, hall⟩ |
        ⟨j, c, hj1, hj2, hpre, hc, hne, hfh, hlc⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · simp only [firstHit, tclHit, hcmp]
          exact hfh
        · simp only [List.map_cons, listCmp, hcmp]
          exact hlc
        · intro i h1 h2
          rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact hhead
          · exact hall i (by omega) (by omega)
      · refine Or.inr ⟨j, c, by omega, by omega, ?_, hc, hne, ?_, ?_⟩
        · intro i h1 h2
          rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact hhead
          · exact hpre i (by omega) h2
        · simp only [firstHit, tclHit, hcmp]
          exact hfh
        · simp only [List.map_cons, listCmp, hcmp]
          exact hlc
    | lt =>
      refine Or.inr ⟨s, .lt, by omega, by omega,
        fun i h1 h2 => absurd h2 (by omega), hcmp, by simp, ?_, ?_⟩
      · simp only [firstHit, tclHit, hcmp, ordInt]
      · simp only [List.map_cons, listCmp, hcmp]
    | gt =>
      refine Or.inr ⟨s, .gt, by omega, by omega,
        fun i h1 h2 => absurd h2 (by omega), hcmp, by simp, ?_, ?_⟩
      · simp only [firstHit, tclHit, hcmp, ordInt]
      · simp only [List.map_cons, listCmp, hcmp]

/-- `testcanlab` returns the trichotomy of the lexicographic `VSet.rowCmp`
comparison of the leaf rows against the stored rows. -/
theorem testcanlab_fst (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) :
    (testcanlab ctx canong lab).1 =
      ordInt (listCmp VSet.rowCmp (leafRows ctx lab)
        ((List.range n).map (canong[·]!))) := by
  rw [testcanlab_eq_firstHit, leafRows_eq_map, List.range_eq_range']
  rcases firstHit_trichotomy ctx canong lab n 0 with
    ⟨hfh, hlc, _⟩ | ⟨j, c, _, _, _, _, _, hfh, hlc⟩
  · rw [hfh, hlc]
    rfl
  · rw [hfh, hlc]
    rfl

/-- The second component of `testcanlab` is a leading-agreement
count: every earlier leaf row agrees with the store. -/
theorem testcanlab_prefix (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) :
    ∀ i < (testcanlab ctx canong lab).2,
      leafRow ctx lab i = canong[i]! := by
  rw [testcanlab_eq_firstHit, List.range_eq_range']
  rcases firstHit_trichotomy ctx canong lab n 0 with
    ⟨hfh, _, hall⟩ | ⟨j, c, _, _, hpre, _, _, hfh, _⟩
  · rw [hfh]
    show ∀ i, i < n → leafRow ctx lab i = canong[i]!
    exact fun i hi => hall i (by omega) (by omega)
  · rw [hfh]
    show ∀ i, i < j → leafRow ctx lab i = canong[i]!
    exact fun i hi => hpre i (by omega) hi

/-- The leading-agreement count never exceeds `n`. -/
theorem testcanlab_snd_le (ctx : Ctx n) (canong : Array (VSet n)) (lab : Array Nat) :
    (testcanlab ctx canong lab).2 ≤ n := by
  rw [testcanlab_eq_firstHit, List.range_eq_range']
  rcases firstHit_trichotomy ctx canong lab n 0 with
    ⟨hfh, _, _⟩ | ⟨j, c, _, hj2, _, _, _, hfh, _⟩
  · rw [hfh]
    show n ≤ n
    exact Nat.le_refl _
  · rw [hfh]
    show j ≤ n
    omega

/-! **The packaged per-leaf clause** -/

/-- The per-leaf clause for the simulation induction: at a code-tied
leaf, `processnode` updates the store and compares. Under the store
invariant, the comparison outcome is the model row comparison of the
two leaf keys, and the updated store satisfies the invariant both at
`n` against the incumbent and at the returned prefix length against
the fresh leaf — re-establishing `CanongInv` whichever way the leaf
resolves. -/
theorem leafEvent_faithful {ctx : Ctx n} {canong : Array (VSet n)} {canonlab lab : Array Nat}
    {samerows : Nat}
    (hinv : CanongInv ctx canong canonlab samerows) :
    (testcanlab ctx (updatecan ctx canong canonlab samerows) lab).1 =
        ordInt (listCmp VSet.rowCmp (leafRows ctx lab)
          (leafRows ctx canonlab)) ∧
      CanongInv ctx (updatecan ctx canong canonlab samerows)
        canonlab n ∧
      CanongInv ctx (updatecan ctx canong canonlab samerows) lab
        (testcanlab ctx (updatecan ctx canong canonlab samerows)
          lab).2 := by
  have hup := updatecan_inv hinv
  refine ⟨?_, hup, ?_⟩
  · rw [testcanlab_fst, rows_of_canongInv hup]
  · exact ⟨hup.1, fun i hi =>
      (testcanlab_prefix ctx _ lab i hi).symm⟩

/-- On equal code lists the key comparison is the row comparison. -/
theorem keyCmp_codes_eq {cs : List Nat} {r1 r2 : List (VSet n)} :
    keyCmp ⟨cs, r1⟩ ⟨cs, r2⟩ = listCmp VSet.rowCmp r1 r2 := by
  rw [keyCmp,
    (listCmp_eq_iff (fun a b => Nat.compare_eq_eq) cs cs).mpr rfl]

end Hex.GraphIso.Nauty
