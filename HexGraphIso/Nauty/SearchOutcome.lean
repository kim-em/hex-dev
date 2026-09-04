/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.LoopCoverage
public import HexGraphIso.Nauty.QuartetStmt
public import HexGraphIso.Nauty.AutosLedger

public section

/-!
Outcome types for the verified search refinement.

The return integer alone does not distinguish a completed sweep, a
generator unwind, a comparison prune, and exhausted loop fuel.  In
particular, an unwind to `level - 1` has the same integer as ordinary
node completion.  The indexed types below keep those cases separate and
also keep logical specification fuel distinct from the two runtime fuels.

A generator or comparison unwind carries the ancestor child it has already
shown to be bounded by the incumbent.  Intermediate calls merely transport
that anchor.  At its indexed target loop, the anchor becomes ordinary child
coverage and the sweep continues.
-/

namespace Hex.GraphIso.Nauty

/-- A checked generator maps one labelling pointwise onto another. -/
@[expose] def LabelCarrier (ctx : Ctx) (ref cur : Array Nat)
    (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ ctx.n = true ∧
    ∀ i, i < ctx.n → γ[ref[i]!]! = cur[i]!

/-- Vertices strictly after the loop cursor. -/
@[expose] def After (cursor : Option Nat) (v : Nat) : Prop :=
  match cursor with
  | none => True
  | some u => u < v

/-- The prefixed specification key of offset `o` in a refined target
cell. -/
@[expose] def sweepKey (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells o : Nat) : Key :=
  prefixKey cs
    (childKey ctx tcLevel specFuel level rsLab rsPtn tc numcells o)

/-- Offset `o` has been absorbed by the incumbent in `out`. -/
@[expose] def ChildDone (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (out : SearchSt) (o : Nat) : Prop :=
  ∃ b, stInc ctx out = some b ∧
    keyLe (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
      numcells o) b

/-- Offset `o` is still eligible after the loop cursor. -/
@[expose] def ChildLive (rsLab : Array Nat) (tc len tcell : Nat)
    (cursor : Option Nat) (o : Nat) : Prop :=
  o < len ∧ elem tcell rsLab[tc + o]! = true ∧
    After cursor rsLab[tc + o]!

/-- The evolving invariant of a mutable target-cell sweep.

`cover` follows removed children transitively to the current live suffix.
`past` records the ordering fact needed when a pruning automorphism carries
a live vertex backwards: every retained vertex at or before the cursor has
already been absorbed. -/
structure SweepCover (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (out : SearchSt) : Prop where
  cover : ChildCover
    (sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells)
    (fun o => rsLab[tc + o]!)
    (fun o => o < len)
    (ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out)
    (ChildLive rsLab tc len tcell cursor)
  past : ∀ o, o < len → elem tcell rsLab[tc + o]! = true →
    ¬ After cursor rsLab[tc + o]! →
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out o

/-- Before the first iteration, the whole target-cell window is live. -/
theorem sweepCover_init (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells : Nat)
    (out : SearchSt) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (windowSet rsLab tc len) none out := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl, Nat.le_refl _⟩
    rw [elem_windowSet, segN]
    exact List.mem_map.mpr ⟨o, List.mem_range.mpr ho, rfl⟩
  · intro o ho hm hpast
    exact absurd trivial hpast

/-- Coverage crosses an arbitrary loop step once old covered children stay
covered and every old survivor is either covered or replaced by a
key-equivalent new survivor. -/
theorem SweepCover.step {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor cursor' : Option Nat}
    {out out' : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            out' j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor' j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hd : ∀ o,
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out o →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o)
    (hpast : ∀ o, o < len → elem tcell' rsLab[tc + o]! = true →
      ¬ After cursor' rsLab[tc + o]! →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor' out' := by
  exact ⟨ChildCover.step h.cover hs hd, hpast⟩

/-- Previously covered children remain covered when the incumbent grows. -/
theorem ChildDone.mono {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc numcells o : Nat}
    {out out' : SearchSt}
    (h : ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out o)
    (hinc : ∀ b, stInc ctx out = some b →
      ∃ b', stInc ctx out' = some b' ∧ keyLe b b') :
    ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
      out' o := by
  rcases h with ⟨b, hb, hkb⟩
  obtain ⟨b', hb', hbb'⟩ := hinc b hb
  exact ⟨b', hb', keyLe_trans hkb hbb'⟩

/-- A filter preserves sweep coverage when every old live child is either
absorbed or carried to a key-equivalent new survivor, and filtering adds no
vertices.  A carried survivor before the cursor is discharged through
`past`; it need not remain in the live suffix. -/
theorem SweepCover.filter {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      (∀ j, sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
          numcells j =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells o →
          ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
            out j) ∨
        ∃ j, ChildLive rsLab tc len tcell' cursor j ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor out := by
  refine ⟨ChildCover.step h.cover hs (fun _ hx => hx), ?_⟩
  intro o ho hm hpast
  exact h.past o ho (hsub _ hm) hpast

/-- Cursor eligibility is decidable without asking typeclass search to
reduce the opaque `After` definition. -/
theorem after_or_not (cursor : Option Nat) (v : Nat) :
    After cursor v ∨ ¬ After cursor v := by
  rcases cursor with _ | u
  · exact Or.inl trivial
  · rcases Nat.lt_or_ge u v with h | h
    · exact Or.inl h
    · exact Or.inr (by
        dsimp only [After]
        omega)

/-- A filter's natural preservation rule: every old live child is carried
to a key-equivalent member of the filtered set.  The member may lie before
the cursor; `past` converts that case to completed coverage. -/
theorem SweepCover.filterCarried {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      ∃ j, j < len ∧ elem tcell' rsLab[tc + j]! = true ∧
        sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
            numcells j ∧
        rsLab[tc + j]! ≤ rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor out := by
  apply h.filter _ hsub
  intro o ho
  obtain ⟨j, hj, hm, hkey, hrank⟩ := hs o ho
  rcases after_or_not cursor rsLab[tc + j]! with ha | ha
  · exact Or.inr ⟨j, ⟨hj, hm, ha⟩, hkey, hrank⟩
  · left
    have hdone := h.past j hj (hsub _ hm) ha
    intro z hz
    rcases hdone with ⟨b, hb, hle⟩
    refine ⟨b, hb, ?_⟩
    rw [hz, hkey]
    exact hle

/-- The form used by executable prune filters.  A current live child either
survives unchanged or is carried to a strictly smaller child of the full
target cell.  Ranked coverage follows the latter through any earlier
filters until it reaches an already-covered child or a new survivor. -/
theorem SweepCover.filterDesc {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hs : ∀ o, ChildLive rsLab tc len tcell cursor o →
      elem tcell' rsLab[tc + o]! = true ∨
        ∃ j, j < len ∧
          sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc numcells o =
            sweepKey ctx tcLevel specFuel level cs rsLab rsPtn tc
              numcells j ∧
          rsLab[tc + j]! < rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor out := by
  constructor
  · apply ChildCover.filterDesc h.cover
    · intro x y hkey hdone
      rcases hdone with ⟨b, hb, hle⟩
      refine ⟨b, hb, ?_⟩
      rw [hkey]
      exact hle
    · intro o ho
      rcases hs o ho with hm | ⟨j, hj, hkey, hrank⟩
      · exact Or.inl ⟨ho.1, hm, ho.2.2⟩
      · exact Or.inr ⟨j, hj, hkey, hrank⟩
  · intro o ho hm hpast
    exact h.past o ho (hsub _ hm) hpast

/-- Cell-stabilizing downward automorphism carriers discharge the abstract
descending-filter rule. -/
theorem SweepCover.filterAutom {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat}
    {tcell tcell' : Nat} {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hdrop : ∀ o, ChildLive rsLab tc len tcell cursor o →
      elem tcell' rsLab[tc + o]! = false →
      ∃ γ, checkAutom ctx.g γ ctx.n = true ∧
        CellStab rsPtn level rsLab γ ∧
        γ[rsLab[tc + o]!]! < rsLab[tc + o]!)
    (hsub : ∀ v, elem tcell' v = true → elem tcell v = true) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell' cursor out := by
  apply h.filterDesc _ hsub
  intro o ho
  rcases hm : elem tcell' rsLab[tc + o]! with _ | _
  · obtain ⟨γ, hγ, hstab, hlt⟩ := hdrop o ho hm
    have hW : elem (windowSet rsLab tc len) γ[rsLab[tc + o]!]! = true :=
      windowSet_carry hstab hic (by rw [hs]; exact hrange)
        (elem_windowSet.mpr (List.mem_map.mpr
          ⟨o, List.mem_range.mpr ho.1, rfl⟩))
    obtain ⟨j, hj, hcarry⟩ := List.mem_map.mp (elem_windowSet.mp hW)
    have hjlt : j < len := List.mem_range.mp hj
    have hkey : childKey ctx tcLevel specFuel level rsLab rsPtn tc
        numcells j = childKey ctx tcLevel specFuel level rsLab rsPtn tc
          numcells o :=
      childKey_of_carried (n := ctx.n) (ctx := ctx) rfl hgsz hγ
        tcLevel specFuel level hstab hs hok hsp hend hvals hic hrange
        hjlt ho.1 hlf hcarry.symm
    exact Or.inr ⟨j, hjlt, by
      unfold sweepKey
      rw [hkey], by simpa [hcarry] using hlt⟩
  · exact Or.inl rfl

/-- `longprune` preserves the evolving sweep under the autos ledger. -/
theorem SweepCover.longprune {ctx : Ctx}
    {tcLevel specFuel level fixedpts : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (haut : ∀ p ∈ out.autos.toList,
      (fixedpts &&& p.1 == fixedpts) = true →
      PairOk ctx.g rsPtn rsLab level ctx.n p.1 p.2) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (longprune tcell fixedpts out.autos) cursor out := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact longprune_drop (hok _ (by omega)) ho.2.1 hm haut
  · exact fun _ hm => longprune_subset hm

/-- `shortprune` preserves the evolving sweep under the last-pair ledger. -/
theorem SweepCover.shortprune {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hgsz : ctx.g.size = ctx.n) (hs : rsLab.size = ctx.n)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨ rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g rsPtn rsLab level ctx.n fix mcr) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      (shortprune tcell out) cursor out := by
  apply h.filterAutom hgsz hs hok hsp hend hvals hic hrange hlf
  · intro o ho hm
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    exact shortprune_drop (hok _ (by omega)) ho.2.1 hm hlast
  · exact fun _ hm => shortprune_subset hm

/-- At loop completion the evolving coverage invariant says that every
offset in the original target cell has been absorbed. -/
theorem SweepCover.finish {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells tcell : Nat} {cursor : Option Nat}
    {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hempty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells out o :=
  ChildCover.finish h.cover hempty

/-- A `none` cursor result means that no set member remains after the
cursor. -/
theorem no_child_after {s : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = none) :
    ∀ v, elem s v = true → After cursor v → False := by
  intro v hv ha
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · dsimp only at hnext ha
    split at hnext
    · next hz =>
      rw [hz, elem, Nat.zero_testBit] at hv
      cases hv
    · cases hnext
  · dsimp only at hnext ha
    change p < v at ha
    split at hnext
    · next hz =>
      have hbit : (((s >>> (p + 1)) <<< (p + 1)).testBit v) = true := by
        rw [Nat.testBit_shiftLeft]
        rw [show decide (p + 1 ≤ v) = true by simp; omega]
        rw [Nat.testBit_shiftRight]
        rw [show p + 1 + (v - (p + 1)) = v by omega]
        exact hv
      rw [hz, Nat.zero_testBit] at hbit
      cases hbit
    · cases hnext

/-- A successful `nextElem` lies strictly after its cursor. -/
theorem nextElem_after {s v : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = some v) : After cursor v := by
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · trivial
  · change p < v
    dsimp only at hnext
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      have hbit := testBit_lowBit _ hn
      rw [Nat.testBit_shiftLeft] at hbit
      have hle : p + 1 ≤ lowBit ((s >>> (p + 1)) <<< (p + 1)) :=
        of_decide_eq_true ((Bool.and_eq_true _ _).mp hbit).1
      omega

/-- `nextElem` returns the least set member strictly after its cursor. -/
theorem nextElem_le {s v w : Nat} {cursor : Option Nat}
    (hnext : nextElem s cursor = some v)
    (hw : elem s w = true) (ha : After cursor w) : v ≤ w := by
  rw [nextElem.eq_def] at hnext
  rcases cursor with _ | p
  · dsimp only at hnext
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      apply Nat.le_of_not_gt
      intro hle
      have hz := testBit_lt_lowBit s w hle
      change s.testBit w = true at hw
      rw [hz] at hw
      cases hw
  · dsimp only at hnext
    change p < w at ha
    split at hnext
    · cases hnext
    · next hn =>
      injection hnext with hv
      subst v
      have hmasked :
          (((s >>> (p + 1)) <<< (p + 1)).testBit w) = true := by
        rw [Nat.testBit_shiftLeft]
        rw [show decide (p + 1 ≤ w) = true by simp; omega]
        rw [Nat.testBit_shiftRight]
        rw [show p + 1 + (w - (p + 1)) = w by omega]
        exact hw
      apply Nat.le_of_not_gt
      intro hle
      have hz := testBit_lt_lowBit ((s >>> (p + 1)) <<< (p + 1)) w
        hle
      rw [hz] at hmasked
      cases hmasked

/-- Advancing to the least remaining vertex preserves sweep coverage once
that vertex's child is absorbed.  The `hcur` premise identifies every
offset carrying the chosen vertex; callers normally discharge it from
labelling injectivity. -/
theorem SweepCover.advance {ctx : Ctx} {tcLevel specFuel level : Nat}
    {cs : List Nat} {rsLab rsPtn : Array Nat} {tc len numcells tv : Nat}
    {tcell : Nat} {cursor : Option Nat} {out out' : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hnext : nextElem tcell cursor = some tv)
    (hcur : ∀ o, o < len → rsLab[tc + o]! = tv →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o)
    (hd : ∀ o,
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells out o →
      ChildDone ctx tcLevel specFuel level cs rsLab rsPtn tc numcells
        out' o) :
    SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
      tcell (some tv) out' := by
  refine SweepCover.step h ?_ hd ?_
  · intro o ho
    change o < len ∧ elem tcell rsLab[tc + o]! = true ∧
      After cursor rsLab[tc + o]! at ho
    rcases ho with ⟨ho, hm, ha⟩
    have hle := nextElem_le hnext hm ha
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · left
      have hdone := hcur o ho heq.symm
      intro j hj
      rcases hdone with ⟨b, hb, hkb⟩
      refine ⟨b, hb, ?_⟩
      rw [hj]
      exact hkb
    · exact Or.inr ⟨o, ⟨ho, hm, hlt⟩, rfl, Nat.le_refl _⟩
  · intro o ho hm hpast
    change ¬ tv < rsLab[tc + o]! at hpast
    rcases cursor with _ | u
    · have hle := nextElem_le hnext hm trivial
      exact hcur o ho (Nat.le_antisymm (Nat.le_of_not_gt hpast) hle)
    · rcases Nat.lt_or_ge u rsLab[tc + o]! with ha | ha
      · have hle := nextElem_le hnext hm ha
        exact hcur o ho (Nat.le_antisymm (Nat.le_of_not_gt hpast) hle)
      · exact hd o (h.past o ho hm (by
          dsimp only [After]
          omega))

/-- The executable loop terminator discharges the live-set premise of
`SweepCover.finish`. -/
theorem SweepCover.finish_of_nextElem {ctx : Ctx}
    {tcLevel specFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells tcell : Nat}
    {cursor : Option Nat} {out : SearchSt}
    (h : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor out)
    (hnext : nextElem tcell cursor = none) :
    ∀ o, o < len → ChildDone ctx tcLevel specFuel level cs rsLab rsPtn
      tc numcells out o := by
  apply h.finish
  intro o ho
  exact no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A child at an ancestor has already been absorbed.  The arrays and
offset are stored explicitly because neither `gcaFirst` nor `gcaCanon`
retains this path history. -/
structure Anchor (ctx : Ctx) (tcLevel target : Nat)
    (out : SearchSt) where
  specFuel : Nat
  codes : List Nat
  rsLab : Array Nat
  rsPtn : Array Nat
  tc : Nat
  numcells : Nat
  offset : Nat
  done : ChildDone ctx tcLevel specFuel target codes rsLab rsPtn tc
    numcells out offset

/-- Why an early return is sound.  Code one and code two retain their
different reference labellings; comparison pruning has no generator. -/
inductive Unwind (ctx : Ctx) (tcLevel target : Nat)
    (out : SearchSt) : Prop where
  | first (anchor : Anchor ctx tcLevel target out)
      (carrier : LabelCarrier ctx out.firstlab out.lab out.genTrace)
  | canon (anchor : Anchor ctx tcLevel target out)
      (carrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
  | frozen (anchor : Anchor ctx tcLevel target out)

/-- Every installed output key came from the incoming incumbent or this
node's specification subtree. -/
structure NodeSound (ctx : Ctx) (tcLevel specFuel level : Nat)
    (cs : List Nat) (st out : SearchSt) (numcells : Nat) : Prop where
  upper : ∀ b, stInc ctx out = some b →
    keyLe b (incMax (stInc ctx st)
      (nodeKey ctx tcLevel specFuel level cs st numcells))

/-- The result of a node call, with logical and runtime fuel separated.

`complete` and `unwind` may have the same return integer.  The latter is
therefore a constructor, not an inequality side condition. -/
inductive NodeResult (ctx : Ctx) (tcLevel specFuel runFuel level : Nat)
    (cs : List Nat) (st out : SearchSt) (numcells : Nat)
    (r : Int) : Prop where
  | complete (sound : NodeSound ctx tcLevel specFuel level cs st out
      numcells)
      (returned : r = Int.ofNat level - 1)
      (installed : out.canonlevel ≠ 0)
      (full : stInc ctx out = some (incMax (stInc ctx st)
        (nodeKey ctx tcLevel specFuel level cs st numcells)))
  | unwind (sound : NodeSound ctx tcLevel specFuel level cs st out
      numcells)
      (target : Nat) (returned : r = Int.ofNat target)
      (below : target < level) (payload : Unwind ctx tcLevel target out)
  | exhausted (empty : runFuel = 0) (returned : r = 0) (unchanged : out = st)

/-- The result of a child-loop call.  Exhaustion is distinct from a
completed empty remainder, so a general theorem cannot accidentally treat
the `cfuel = 0` arm as coverage of every child. -/
inductive LoopResult (ctx : Ctx) (tcLevel specFuel runFuel loopFuel level : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (tc len numcells tcell : Nat)
    (cursor : Option Nat) (st out : SearchSt) (r : Option Int) : Prop where
  | complete
      (returned : r = none)
      (cover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
        numcells tcell cursor out)
      (empty : ∀ o, ¬ ChildLive rsLab tc len tcell cursor o)
  | unwind (target : Nat) (returned : r = some (Int.ofNat target))
      (below : target < level) (payload : Unwind ctx tcLevel target out)
  | exhausted (empty : loopFuel = 0) (returned : r = none)
      (unchanged : out = st)

end Hex.GraphIso.Nauty
