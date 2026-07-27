/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Separation

public section

/-!
# Cells cut out by strictly isolated carrier roots

An array of `n` strictly ordered carrier roots cuts the real line into `n`
root cells and `n + 1` open cells.  Open cut `0` is the left tail, cut `n`
is the right tail, and an interior cut is the gap between its predecessor and
successor roots.  For `n = 0`, the sole open cell is all of `ℝ`.

The executable layer stores only indices and exact dyadic sample points.  A
noncomputable `RootModel` packages the semantic roots justified by the replay
and isolation checkers.
-/

namespace Hex.RCF

open HexRealRootsMathlib

/-- A root cell or one of the open cuts around `n` ordered roots. -/
inductive Cell (n : Nat) where
  /-- Open cell at a cut between roots, including both tails. -/
  | open (cut : Fin (n + 1))
  /-- Singleton cell at an isolated root. -/
  | root (i : Fin n)
  deriving DecidableEq, Repr

namespace Cell

/-- Alternating position of a cell in the left-to-right decomposition. -/
@[expose]
def rank : Cell n → Nat
  | .open cut => 2 * cut.val
  | .root i => 2 * i.val + 1

/-- Every rank is a valid index into a `2 * n + 1` cell vector. -/
theorem rank_lt (c : Cell n) : c.rank < 2 * n + 1 := by
  cases c with
  | «open» cut => simp [rank]; omega
  | root i => simp [rank]

/-- Deterministic left-to-right enumeration of all `2 * n + 1` cells. -/
@[expose]
def all (n : Nat) : Array (Cell n) :=
  (((List.finRange n).flatMap fun i =>
      [Cell.open i.castSucc, Cell.root i]) ++
    [Cell.open (Fin.last n)]).toArray

@[simp] theorem size_all (n : Nat) : (all n).size = 2 * n + 1 := by
  simp [all]
  omega

/-- Every size-correct cell occurs in the executable enumeration. -/
theorem mem_all (c : Cell n) : c ∈ all n := by
  cases c with
  | root i =>
      simp [all]
  | «open» cut =>
      by_cases hlast : cut.val = n
      · have hcut : cut = Fin.last n := Fin.ext (by simpa [Fin.last] using hlast)
        subst cut
        simp [all]
      · let i : Fin n := ⟨cut.val, by omega⟩
        have hcut : i.castSucc = cut := Fin.ext rfl
        simp [all]
        exact Or.inl ⟨i, hcut.symm⟩

end Cell

/-- The semantic roots named by a checked isolation array. -/
structure RootModel (f : ZPoly) (cert : IsolationCert) where
  /-- Root in each certified interval. -/
  root : Fin cert.intervals.size → ℝ
  /-- Every named point is a carrier root. -/
  isRoot : ∀ i, (toPolyℝ f).IsRoot (root i)
  /-- Every named point lies in its certified half-open interval. -/
  inInterval : ∀ i, Literal.InInterval cert.intervals[i] (root i)
  /-- Array order is strict real-root order. -/
  strictMono : StrictMono root
  /-- Every carrier root occurs at exactly one named index. -/
  complete : ∀ x, (toPolyℝ f).IsRoot x → ∃! i, root i = x

namespace IsolationCert

/-- The chosen unique root in one accepted generalized isolation. -/
noncomputable def rootAt {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size) : ℝ :=
  Classical.choose (exists_unique_root_of_check hreplay hcert i)

theorem rootAt_spec {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size) :
    (toPolyℝ f).IsRoot (cert.rootAt hreplay hcert i) ∧
      Literal.InInterval cert.intervals[i] (cert.rootAt hreplay hcert i) :=
  (Classical.choose_spec (exists_unique_root_of_check hreplay hcert i)).1

theorem rootAt_unique {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size)
    {x : ℝ} (hx : (toPolyℝ f).IsRoot x)
    (hmem : Literal.InInterval cert.intervals[i] x) :
    x = cert.rootAt hreplay hcert i :=
  (Classical.choose_spec (exists_unique_root_of_check hreplay hcert i)).2 x
    ⟨hx, hmem⟩

/-- Strict validation exposes its strict-gap component. -/
theorem gaps_of_checkStrict {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.checkStrict replay = true) : cert.checkGaps = true := by
  simp only [checkStrict, Bool.and_eq_true] at h
  exact h.2

/-- Package all semantic consequences of an accepted strict isolation array. -/
noncomputable def rootModel {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true) : RootModel f cert where
  root := cert.rootAt hreplay (check_of_checkStrict hstrict)
  isRoot i := (rootAt_spec cert hreplay (check_of_checkStrict hstrict) i).1
  inInterval i := (rootAt_spec cert hreplay (check_of_checkStrict hstrict) i).2
  strictMono := by
    intro i j hij
    exact roots_lt_of_check (gaps_of_checkStrict hstrict) hij
      (rootAt_spec cert hreplay (check_of_checkStrict hstrict) i).2
      (rootAt_spec cert hreplay (check_of_checkStrict hstrict) j).2
  complete := by
    intro x hx
    obtain ⟨i, hi, huniq⟩ := isolates_of_check hreplay
      (check_of_checkStrict hstrict) x hx
    refine ⟨i, ?_, ?_⟩
    · exact (rootAt_unique cert hreplay (check_of_checkStrict hstrict) i hx hi).symm
    · intro j hj
      apply huniq j
      rw [← hj]
      exact (rootAt_spec cert hreplay (check_of_checkStrict hstrict) j).2

/-- Exact dyadic sample for an open cut. -/
@[expose]
def openPoint (cert : IsolationCert) :
    Fin (cert.intervals.size + 1) → Dyadic
  | cut =>
      if hzero : cert.intervals.size = 0 then 0
      else if hleft : cut.val = 0 then
        (cert.intervals[0]'(by omega)).lower + Dyadic.ofInt (-1)
      else if hright : cut.val = cert.intervals.size then
        (cert.intervals[cert.intervals.size - 1]'(by omega)).upper + Dyadic.ofInt 1
      else
        ((cert.intervals[cut.val - 1]'(by omega)).upper +
          (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)

/-- Open cells carry exact dyadic samples; root cells are represented by their
certified isolation instead. -/
@[expose]
def sample? (cert : IsolationCert) : Cell cert.intervals.size → Option Dyadic
  | .open cut => some (cert.openPoint cut)
  | .root _ => none

@[simp] theorem sample?_open (cert : IsolationCert)
    (cut : Fin (cert.intervals.size + 1)) :
    cert.sample? (.open cut) = some (cert.openPoint cut) := rfl

end IsolationCert

namespace Cell

/-- Semantic membership in a cell of a checked root model. -/
@[expose]
def Sem {f : ZPoly} {cert : IsolationCert} (M : RootModel f cert) :
    Cell cert.intervals.size → ℝ → Prop
  | .root i, x => x = M.root i
  | .open cut, x =>
      if hzero : cert.intervals.size = 0 then True
      else if hleft : cut.val = 0 then
        x < M.root ⟨0, by omega⟩
      else if hright : cut.val = cert.intervals.size then
        M.root ⟨cert.intervals.size - 1, by omega⟩ < x
      else
        M.root ⟨cut.val - 1, by omega⟩ < x ∧
          x < M.root ⟨cut.val, by omega⟩

/-- Every checked open-cell sample lies in its advertised semantic cell. -/
theorem openPoint_mem {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (cut : Fin (cert.intervals.size + 1)) :
    Sem (cert.rootModel hreplay hstrict) (.open cut)
      (Dyadic.toReal (cert.openPoint cut)) := by
  classical
  by_cases hzero : cert.intervals.size = 0
  · simp [Sem, hzero]
  by_cases hleft : cut.val = 0
  · have hmem := (cert.rootModel hreplay hstrict).inInterval
      ⟨0, by omega⟩
    simp only [Literal.InInterval] at hmem
    have hcell : ∀ x : ℝ,
        Sem (cert.rootModel hreplay hstrict) (.open cut) x ↔
          x < (cert.rootModel hreplay hstrict).root ⟨0, by omega⟩ := by
      intro x
      simp [Sem, hzero, hleft]
    rw [hcell]
    have hsamp : cert.openPoint cut =
        (cert.intervals[0]'(by omega)).lower + Dyadic.ofInt (-1) := by
      simp [IsolationCert.openPoint, hzero, hleft]
    have hsampLt : cert.openPoint cut <
        (cert.intervals[0]'(by omega)).lower := by
      rw [hsamp, ← Dyadic.toRat_lt_toRat_iff, Dyadic.toRat_add,
        show Dyadic.ofInt (-1) = ((-1 : Int) : Dyadic) from rfl,
        Dyadic.toRat_intCast]
      norm_num
    exact lt_trans (toReal_lt_toReal hsampLt) hmem.1
  by_cases hright : cut.val = cert.intervals.size
  · have hmem := (cert.rootModel hreplay hstrict).inInterval
      ⟨cert.intervals.size - 1, by omega⟩
    simp only [Literal.InInterval] at hmem
    have hcell : ∀ x : ℝ,
        Sem (cert.rootModel hreplay hstrict) (.open cut) x ↔
          (cert.rootModel hreplay hstrict).root
            ⟨cert.intervals.size - 1, by omega⟩ < x := by
      intro x
      simp [Sem, hzero, hright]
    rw [hcell]
    have hsamp : cert.openPoint cut =
        (cert.intervals[cert.intervals.size - 1]'(by omega)).upper +
          Dyadic.ofInt 1 := by
      simp [IsolationCert.openPoint, hzero, hright]
    have hsampLt :
        (cert.intervals[cert.intervals.size - 1]'(by omega)).upper <
          cert.openPoint cut := by
      rw [hsamp, ← Dyadic.toRat_lt_toRat_iff, Dyadic.toRat_add,
        show Dyadic.ofInt 1 = ((1 : Int) : Dyadic) from rfl,
        Dyadic.toRat_intCast]
      norm_num
    exact lt_of_le_of_lt hmem.2 (toReal_lt_toReal hsampLt)
  · have hgap : (cert.intervals[cut.val - 1]'(by omega)).upper <
        (cert.intervals[cut.val]'(by omega)).lower := by
      have hg := IsolationCert.gap_of_check
        (IsolationCert.gaps_of_checkStrict hstrict) (cut.val - 1) (by omega)
      have heq : cut.val - 1 + 1 = cut.val := by omega
      simpa only [heq] using hg
    let gap : DyadicInterval :=
      ⟨(cert.intervals[cut.val - 1]'(by omega)).upper,
        (cert.intervals[cut.val]'(by omega)).lower,
        hgap⟩
    have hprev := (cert.rootModel hreplay hstrict).inInterval
      ⟨cut.val - 1, by omega⟩
    have hnext := (cert.rootModel hreplay hstrict).inInterval
      ⟨cut.val, by omega⟩
    have hlm := toReal_lt_toReal (lower_lt_midpoint gap)
    have hmu := toReal_lt_toReal (midpoint_lt_upper gap)
    simp only [Literal.InInterval] at hprev hnext
    have hsem : (cert.rootModel hreplay hstrict).root
          ⟨cut.val - 1, by omega⟩ < Dyadic.toReal gap.midpoint ∧
        Dyadic.toReal gap.midpoint <
          (cert.rootModel hreplay hstrict).root ⟨cut.val, by omega⟩ :=
      ⟨lt_of_le_of_lt hprev.2 hlm, lt_trans hmu hnext.1⟩
    have hraw : Dyadic.toReal
          (((cert.intervals[cut.val - 1]'(by omega)).upper +
            (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)) =
        (Dyadic.toReal (cert.intervals[cut.val - 1]'(by omega)).upper +
          Dyadic.toReal (cert.intervals[cut.val]'(by omega)).lower) / 2 := by
      rw [toReal_shiftRight, toReal_add]
      norm_num
      ring
    have hmid : Dyadic.toReal
          (((cert.intervals[cut.val - 1]'(by omega)).upper +
            (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)) =
        Dyadic.toReal gap.midpoint := by
      rw [hraw, toReal_midpoint]
    rw [← hmid] at hsem
    simpa [Sem, IsolationCert.openPoint, hzero, hleft, hright] using hsem

/-- Every real point belongs to at least one semantic cell. -/
theorem exists_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) :
    ∃ c : Cell cert.intervals.size, Sem M c x := by
  classical
  by_cases hzero : cert.intervals.size = 0
  · refine ⟨.open ⟨0, by omega⟩, ?_⟩
    simp [Sem, hzero]
  let first : Fin cert.intervals.size := ⟨0, by omega⟩
  by_cases hleft : x < M.root first
  · refine ⟨.open ⟨0, by omega⟩, ?_⟩
    simpa [Sem, hzero, first] using hleft
  by_cases hsome : ∃ i : Fin cert.intervals.size, x ≤ M.root i
  · let i := Fin.find (fun j => x ≤ M.root j) hsome
    have hxi : x ≤ M.root i := Fin.find_spec hsome
    by_cases heq : x = M.root i
    · exact ⟨.root i, by simpa [Sem] using heq⟩
    · have hi0 : i.val ≠ 0 := by
        intro hi
        have hieq : i = first := Fin.ext hi
        have hrx : M.root first ≤ x := not_lt.mp hleft
        apply heq
        rw [hieq] at hxi ⊢
        exact le_antisymm hxi hrx
      let prev : Fin cert.intervals.size := ⟨i.val - 1, by omega⟩
      have hprev : M.root prev < x := by
        apply lt_of_not_ge
        apply Fin.find_min hsome
        show prev.val < i.val
        simp only [prev]
        omega
      have hnext : x < M.root i := lt_of_le_of_ne hxi heq
      refine ⟨.open ⟨i.val, by omega⟩, ?_⟩
      simpa [Sem, hzero, hi0, show i.val ≠ cert.intervals.size by omega,
        prev] using And.intro hprev hnext
  · let last : Fin cert.intervals.size :=
      ⟨cert.intervals.size - 1, by omega⟩
    have hlast : M.root last < x := by
      exact lt_of_not_ge (fun hx => hsome ⟨last, hx⟩)
    refine ⟨.open (Fin.last cert.intervals.size), ?_⟩
    simpa [Sem, hzero, last] using hlast

private theorem open_lt_upper {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cut : Fin (cert.intervals.size + 1)) (x : ℝ)
    (hcut : cut.val < cert.intervals.size) (hx : Sem M (.open cut) x) :
    x < M.root ⟨cut.val, hcut⟩ := by
  have hzero : cert.intervals.size ≠ 0 := by omega
  by_cases hleft : cut.val = 0
  · simpa [Sem, hzero, hleft] using hx
  · have hright : cut.val ≠ cert.intervals.size := by omega
    simp [Sem, hzero, hleft, hright] at hx
    exact hx.2

private theorem lower_lt_open {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cut : Fin (cert.intervals.size + 1)) (x : ℝ)
    (hcut : 0 < cut.val) (hx : Sem M (.open cut) x) :
    M.root ⟨cut.val - 1, by omega⟩ < x := by
  have hzero : cert.intervals.size ≠ 0 := by omega
  have hleft : cut.val ≠ 0 := by omega
  by_cases hright : cut.val = cert.intervals.size
  · simpa [Sem, hzero, hleft, hright] using hx
  · simp [Sem, hzero, hleft, hright] at hx
    exact hx.1

/-- `rank` is an injective encoding of the alternating cell order. -/
theorem rank_injective : Function.Injective (@rank n) := by
  intro c d h
  cases c with
  | «open» i =>
      cases d with
      | «open» j =>
          simp only [rank] at h
          congr
          apply Fin.ext
          omega
      | root j =>
          simp only [rank] at h
          omega
  | root i =>
      cases d with
      | «open» j =>
          simp only [rank] at h
          omega
      | root j =>
          simp only [rank] at h
          congr
          apply Fin.ext
          omega

/-- Cells earlier in the alternating enumeration lie strictly to the left. -/
theorem lt_of_rank_lt {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) {c d : Cell cert.intervals.size} {x y : ℝ}
    (hcd : rank c < rank d) (hx : Sem M c x) (hy : Sem M d y) : x < y := by
  cases c with
  | root i =>
      cases d with
      | root j =>
          simp only [rank] at hcd
          simp only [Sem] at hx hy
          rw [hx, hy]
          exact M.strictMono (by omega)
      | «open» cut =>
          simp only [rank] at hcd
          simp only [Sem] at hx
          rw [hx]
          have hlower := lower_lt_open M cut y (by omega) hy
          have hmono : M.root i ≤ M.root ⟨cut.val - 1, by omega⟩ :=
            M.strictMono.monotone (by show i.val ≤ cut.val - 1; omega)
          exact lt_of_le_of_lt hmono hlower
  | «open» cut =>
      cases d with
      | root j =>
          simp only [rank] at hcd
          simp only [Sem] at hy
          rw [hy]
          have hupper := open_lt_upper M cut x (by omega) hx
          have hmono : M.root ⟨cut.val, by omega⟩ ≤ M.root j :=
            M.strictMono.monotone (by show cut.val ≤ j.val; omega)
          exact lt_of_lt_of_le hupper hmono
      | «open» next =>
          simp only [rank] at hcd
          have hupper := open_lt_upper M cut x (by omega) hx
          have hlower := lower_lt_open M next y (by omega) hy
          have hmono : M.root ⟨cut.val, by omega⟩ ≤
              M.root ⟨next.val - 1, by omega⟩ :=
            M.strictMono.monotone (by show cut.val ≤ next.val - 1; omega)
          exact lt_trans hupper (lt_of_le_of_lt hmono hlower)

/-- Semantic cell membership is unique. -/
theorem unique_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) {c d : Cell cert.intervals.size}
    (hc : Sem M c x) (hd : Sem M d x) : c = d := by
  by_contra hne
  have hrank : rank c ≠ rank d := fun h => hne (rank_injective h)
  rcases lt_or_gt_of_ne hrank with hlt | hgt
  · exact (lt_irrefl x) (lt_of_rank_lt M hlt hc hd)
  · exact (lt_irrefl x) (lt_of_rank_lt M hgt hd hc)

/-- The semantic cells form a genuine partition of the real line. -/
theorem existsUnique_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) :
    ∃! c : Cell cert.intervals.size, Sem M c x := by
  obtain ⟨c, hc⟩ := exists_mem M x
  exact ⟨c, hc, fun d hd => unique_mem M x hd hc⟩

/-- Every semantic cell contains a real point. -/
theorem exists_point {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (c : Cell cert.intervals.size) :
    ∃ x : ℝ, Sem M c x := by
  cases c with
  | root i => exact ⟨M.root i, by simp [Sem]⟩
  | «open» cut =>
      by_cases hzero : cert.intervals.size = 0
      · exact ⟨0, by simp [Sem, hzero]⟩
      by_cases hleft : cut.val = 0
      · refine ⟨M.root ⟨0, by omega⟩ - 1, ?_⟩
        simp [Sem, hzero, hleft]
      by_cases hright : cut.val = cert.intervals.size
      · refine ⟨M.root ⟨cert.intervals.size - 1, by omega⟩ + 1, ?_⟩
        simp [Sem, hzero, hright]
      · have hroots : M.root ⟨cut.val - 1, by omega⟩ <
            M.root ⟨cut.val, by omega⟩ := by
          apply M.strictMono
          show cut.val - 1 < cut.val
          omega
        obtain ⟨x, hx⟩ := exists_between hroots
        exact ⟨x, by simpa [Sem, hzero, hleft, hright] using hx⟩

/-- Every open semantic cell is an interval, hence preconnected. -/
theorem isPreconnected_open {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cut : Fin (cert.intervals.size + 1)) :
    IsPreconnected {x : ℝ | Sem M (.open cut) x} := by
  by_cases hzero : cert.intervals.size = 0
  · simpa [Sem, hzero] using (isPreconnected_univ :
      IsPreconnected (Set.univ : Set ℝ))
  by_cases hleft : cut.val = 0
  · have heq : {x : ℝ | Sem M (.open cut) x} =
        Set.Iio (M.root ⟨0, by omega⟩) := by
      ext x
      simp [Sem, hzero, hleft, Set.mem_Iio]
    rw [heq]
    exact isPreconnected_Iio
  by_cases hright : cut.val = cert.intervals.size
  · have heq : {x : ℝ | Sem M (.open cut) x} =
        Set.Ioi (M.root ⟨cert.intervals.size - 1, by omega⟩) := by
      ext x
      simp [Sem, hzero, hright, Set.mem_Ioi]
    rw [heq]
    exact isPreconnected_Ioi
  · have heq : {x : ℝ | Sem M (.open cut) x} =
        Set.Ioo (M.root ⟨cut.val - 1, by omega⟩)
          (M.root ⟨cut.val, by omega⟩) := by
      ext x
      simp [Sem, hzero, hleft, hright, Set.mem_Ioo]
    rw [heq]
    exact isPreconnected_Ioo

/-- An open carrier cell contains no carrier root. -/
theorem open_not_root {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) {cut : Fin (cert.intervals.size + 1)} {x : ℝ}
    (hx : Sem M (.open cut) x) : ¬(toPolyℝ f).IsRoot x := by
  intro hroot
  obtain ⟨i, hi, -⟩ := M.complete x hroot
  have hrootCell : Sem M (.root i) x := by
    simpa [Sem] using hi.symm
  have : Cell.open cut = Cell.root i := unique_mem M x hx hrootCell
  cases this

end Cell

/-- Claimed carrier-root comparisons against the lower and upper endpoints of
a bounded domain. -/
structure IocCmps (n : Nat) where
  /-- Each root's order relative to the excluded lower endpoint. -/
  lower : Vector Separation.RootCmp n
  /-- Each root's order relative to the included upper endpoint. -/
  upper : Vector Separation.RootCmp n
  deriving Repr

namespace IocCmps

/-- Recompute every claimed endpoint comparison. This validates comparison
data only; the bounded-domain layer separately checks `a < b`. -/
@[expose]
def check (f : ZPoly) (replay : SturmReplay) (cert : IsolationCert)
    (a b : Dyadic) (cmps : IocCmps cert.intervals.size) : Bool :=
  (List.range cert.intervals.size).all fun i =>
    if hi : i < cert.intervals.size then
      Separation.checkCmp f replay cert.intervals[i] a cmps.lower[i] &&
        Separation.checkCmp f replay cert.intervals[i] b cmps.upper[i]
    else false

/-- A checked comparison vector has its claimed meaning against the chosen
semantic roots. -/
theorem holds_of_check {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (hcmps : check f replay cert a b cmps = true)
    (i : Fin cert.intervals.size) :
    cmps.lower[i].Holds ((cert.rootModel hreplay hstrict).root i)
        (Dyadic.toReal a) ∧
      cmps.upper[i].Holds ((cert.rootModel hreplay hstrict).root i)
        (Dyadic.toReal b) := by
  have hmem : i.val ∈ List.range cert.intervals.size := List.mem_range.mpr i.isLt
  have hstep := (List.all_eq_true.mp hcmps) i.val hmem
  simp only [i.isLt, dite_true, Bool.and_eq_true] at hstep
  have cmpHolds (endpoint : Dyadic) (claim : Separation.RootCmp)
      (hclaim : Separation.checkCmp f replay cert.intervals[i] endpoint claim = true) :
      claim.Holds ((cert.rootModel hreplay hstrict).root i)
        (Dyadic.toReal endpoint) := by
    obtain ⟨root, hroot, -⟩ := Separation.checkCmp_sound hreplay
      (IsolationCert.check_of_checkStrict hstrict) i endpoint claim hclaim
    have hrootAt := cert.rootAt_unique hreplay
      (IsolationCert.check_of_checkStrict hstrict) i hroot.1 hroot.2.1
    have hmodelAt := cert.rootAt_unique hreplay
      (IsolationCert.check_of_checkStrict hstrict) i
      ((cert.rootModel hreplay hstrict).isRoot i)
      ((cert.rootModel hreplay hstrict).inInterval i)
    rw [hrootAt, ← hmodelAt] at hroot
    exact hroot.2.2
  exact ⟨cmpHolds a cmps.lower[i] hstep.1,
    cmpHolds b cmps.upper[i] hstep.2⟩

end IocCmps

namespace Cell

/-- Executable bounded-domain relevance test for a cell. The surrounding
certificate first checks `a < b`; this core assumes that nonempty-domain
hypothesis. -/
@[expose]
def meetsIoc (cmps : IocCmps n) : Cell n → Bool
  | .root i => cmps.lower[i] == .gt && cmps.upper[i] != .gt
  | .open cut =>
      if hzero : n = 0 then true
      else if hleft : cut.val = 0 then
        cmps.lower[0] == .gt
      else if hright : cut.val = n then
        cmps.upper[n - 1] == .lt
      else
        cmps.upper[cut.val - 1] == .lt && cmps.lower[cut.val] == .gt

/-- Guard the nonempty-domain relevance table against equal or reversed
endpoints. -/
@[expose]
def meetsIocOn (a b : Dyadic) (cmps : IocCmps n) (c : Cell n) : Bool :=
  decide (a < b) && meetsIoc cmps c

private theorem eq_gt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp == .gt) = true ↔ endpoint < root := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

private theorem ne_gt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp != .gt) = true ↔ root ≤ endpoint := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

private theorem eq_lt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp == .lt) = true ↔ root < endpoint := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

/-- The executable relevance table is exactly semantic intersection with a
nonempty half-open interval. -/
theorem meetsIoc_iff {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hab : Dyadic.toReal a < Dyadic.toReal b)
    (hlower : ∀ i : Fin cert.intervals.size,
      Separation.RootCmp.Holds cmps.lower[i] (M.root i) (Dyadic.toReal a))
    (hupper : ∀ i : Fin cert.intervals.size,
      Separation.RootCmp.Holds cmps.upper[i] (M.root i) (Dyadic.toReal b))
    (c : Cell cert.intervals.size) :
    meetsIoc cmps c = true ↔
      ∃ x : ℝ, Sem M c x ∧
        x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b) := by
  let A := Dyadic.toReal a
  let B := Dyadic.toReal b
  change meetsIoc cmps c = true ↔
    ∃ x : ℝ, Sem M c x ∧ x ∈ Set.Ioc A B
  change A < B at hab
  cases c with
  | root i =>
      have hl := hlower i
      have hu := hupper i
      change Separation.RootCmp.Holds cmps.lower[i] (M.root i) A at hl
      change Separation.RootCmp.Holds cmps.upper[i] (M.root i) B at hu
      change ((cmps.lower[i] == .gt) && (cmps.upper[i] != .gt)) = true ↔ _
      rw [Bool.and_eq_true, eq_gt_iff hl, ne_gt_iff hu]
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨M.root i, by simp [Sem], ha, hb⟩
      · rintro ⟨x, hx, ha, hb⟩
        have hxeq : x = M.root i := by simpa [Sem] using hx
        subst x
        exact ⟨ha, hb⟩
  | «open» cut =>
      by_cases hzero : cert.intervals.size = 0
      · simp only [meetsIoc]
        rw [dif_pos hzero]
        constructor
        · intro _
          exact ⟨B, by simp [Sem, hzero], hab, le_rfl⟩
        · intro _
          rfl
      by_cases hleft : cut.val = 0
      · let first : Fin cert.intervals.size := ⟨0, by omega⟩
        have hl := hlower first
        change Separation.RootCmp.Holds cmps.lower[first] (M.root first) A at hl
        have hsem : ∀ x : ℝ, Sem M (.open cut) x ↔ x < M.root first := by
          intro x
          simp [Sem, hzero, hleft, first]
        have hbound : (cmps.lower[0] == .gt) = true ↔ A < M.root first := by
          simpa [first] using eq_gt_iff hl
        simp only [meetsIoc]
        rw [dif_neg hzero, dif_pos hleft, hbound]
        constructor
        · intro har
          obtain ⟨x, hax, hx⟩ := exists_between (lt_min hab har)
          exact ⟨x, (hsem x).2 (lt_min_iff.mp hx).2,
            hax, (lt_min_iff.mp hx).1.le⟩
        · rintro ⟨x, hx, hax, -⟩
          exact lt_trans hax ((hsem x).1 hx)
      by_cases hright : cut.val = cert.intervals.size
      · let last : Fin cert.intervals.size :=
          ⟨cert.intervals.size - 1, by omega⟩
        have hu := hupper last
        change Separation.RootCmp.Holds cmps.upper[last] (M.root last) B at hu
        have hsem : ∀ x : ℝ, Sem M (.open cut) x ↔ M.root last < x := by
          intro x
          simp [Sem, hzero, hright, last]
        have hbound : (cmps.upper[cert.intervals.size - 1] == .lt) = true ↔
            M.root last < B := by
          simpa [last] using eq_lt_iff hu
        simp only [meetsIoc]
        rw [dif_neg hzero, dif_neg hleft, dif_pos hright, hbound]
        constructor
        · intro hrb
          obtain ⟨x, hx, hxb⟩ := exists_between (max_lt hab hrb)
          exact ⟨x, (hsem x).2 (max_lt_iff.mp hx).2,
            (max_lt_iff.mp hx).1, hxb.le⟩
        · rintro ⟨x, hx, -, hxb⟩
          exact lt_of_lt_of_le ((hsem x).1 hx) hxb
      · let prev : Fin cert.intervals.size := ⟨cut.val - 1, by omega⟩
        let next : Fin cert.intervals.size := ⟨cut.val, by omega⟩
        have hu := hupper prev
        have hl := hlower next
        change Separation.RootCmp.Holds cmps.upper[prev] (M.root prev) B at hu
        change Separation.RootCmp.Holds cmps.lower[next] (M.root next) A at hl
        have hroots : M.root prev < M.root next := by
          apply M.strictMono
          show cut.val - 1 < cut.val
          omega
        have hsem : ∀ x : ℝ, Sem M (.open cut) x ↔
            M.root prev < x ∧ x < M.root next := by
          intro x
          simp [Sem, hzero, hleft, hright, prev, next]
        have hubound : (cmps.upper[cut.val - 1] == .lt) = true ↔
            M.root prev < B := by
          simpa [prev] using eq_lt_iff hu
        have hlbound : (cmps.lower[cut.val] == .gt) = true ↔
            A < M.root next := by
          simpa [next] using eq_gt_iff hl
        simp only [meetsIoc]
        rw [dif_neg hzero, dif_neg hleft, dif_neg hright, Bool.and_eq_true,
          hubound, hlbound]
        constructor
        · rintro ⟨hrb, har⟩
          have hbetween : max A (M.root prev) < min B (M.root next) :=
            lt_min (max_lt hab hrb) (max_lt har hroots)
          obtain ⟨x, hx, hy⟩ := exists_between hbetween
          have hxmax := max_lt_iff.mp hx
          have hymin := lt_min_iff.mp hy
          exact ⟨x, (hsem x).2 ⟨hxmax.2, hymin.2⟩,
            hxmax.1, hymin.1.le⟩
        · rintro ⟨x, hx, hax, hxb⟩
          have hcell := (hsem x).1 hx
          exact ⟨lt_of_lt_of_le hcell.1 hxb, lt_trans hax hcell.2⟩

/-- Checked comparison vectors decide bounded-domain cell relevance exactly. -/
theorem meetsIoc_iff_of_check {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (hcmps : IocCmps.check f replay cert a b cmps = true)
    (hab : Dyadic.toReal a < Dyadic.toReal b)
    (c : Cell cert.intervals.size) :
    meetsIoc cmps c = true ↔
      ∃ x : ℝ, Sem (cert.rootModel hreplay hstrict) c x ∧
        x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b) := by
  apply meetsIoc_iff (cert.rootModel hreplay hstrict) cmps a b hab
  · intro i
    exact (cmps.holds_of_check a b hreplay hstrict hcmps i).1
  · intro i
    exact (cmps.holds_of_check a b hreplay hstrict hcmps i).2

/-- The guarded relevance test is exact for all endpoint orders. -/
theorem meetsIocOn_iff_of_check {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (hcmps : IocCmps.check f replay cert a b cmps = true)
    (c : Cell cert.intervals.size) :
    meetsIocOn a b cmps c = true ↔
      ∃ x : ℝ, Sem (cert.rootModel hreplay hstrict) c x ∧
        x ∈ Set.Ioc (Dyadic.toReal a) (Dyadic.toReal b) := by
  by_cases hab : a < b
  · simp only [meetsIocOn, hab, decide_true]
    exact meetsIoc_iff_of_check cmps a b hreplay hstrict hcmps
      (toReal_lt_toReal hab) c
  · constructor
    · simp [meetsIocOn, hab]
    · rintro ⟨x, -, hax, hxb⟩
      have hreal : ¬Dyadic.toReal a < Dyadic.toReal b := by
        simpa [toReal_lt_toReal_iff] using hab
      exact (hreal (lt_of_lt_of_le hax hxb)).elim

end Cell

end Hex.RCF
