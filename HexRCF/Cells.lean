/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Regions
public import HexRCF.Separation

public section

/-!
# Semantics of cells cut out by strictly isolated carrier roots

The Mathlib-free cell data, exact samples, endpoint-comparison checks, and
bounded-domain relevance table live in `HexRCF.CellsCheck`. A noncomputable
`RootModel` packages the semantic roots justified by the replay and isolation
checkers, and the theorems here interpret every executable cell over `ℝ`.
-/

namespace Hex.RCF

open HexRealRootsMathlib

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
  Classical.choose (existsUnique_root hreplay hcert i)

/-- The chosen point is a root of the polynomial in the specified interval. -/
theorem rootAt_spec {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size) :
    (toPolyℝ f).IsRoot (cert.rootAt hreplay hcert i) ∧
      Literal.InInterval cert.intervals[i] (cert.rootAt hreplay hcert i) :=
  (Classical.choose_spec (existsUnique_root hreplay hcert i)).1

/-- Every root in the specified interval equals the chosen root. -/
theorem rootAt_unique {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size)
    {x : ℝ} (hx : (toPolyℝ f).IsRoot x)
    (hmem : Literal.InInterval cert.intervals[i] x) :
    x = cert.rootAt hreplay hcert i :=
  (Classical.choose_spec (existsUnique_root hreplay hcert i)).2 x
    ⟨hx, hmem⟩

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

/-- The rational root model uses the coefficient-independent cell interpretation. -/
theorem sem_eq_region {f : ZPoly} {cert : IsolationCert} (M : RootModel f cert) :
    Sem M = Region M.root := by
  funext c x
  cases c <;> rfl

/-- Every checked open-cell sample lies in its advertised semantic cell. -/
theorem openPoint_mem {f : ZPoly} {replay : SturmReplay}
    (cert : IsolationCert) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (cut : Fin (cert.intervals.size + 1)) :
    Sem (cert.rootModel hreplay hstrict) (.open cut)
      (HexRealRootsMathlib.Dyadic.toReal (cert.openPoint cut)) := by
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
          ⟨cut.val - 1, by omega⟩ < HexRealRootsMathlib.Dyadic.toReal gap.midpoint ∧
        HexRealRootsMathlib.Dyadic.toReal gap.midpoint <
          (cert.rootModel hreplay hstrict).root ⟨cut.val, by omega⟩ :=
      ⟨lt_of_le_of_lt hprev.2 hlm, lt_trans hmu hnext.1⟩
    have hraw : HexRealRootsMathlib.Dyadic.toReal
          (((cert.intervals[cut.val - 1]'(by omega)).upper +
            (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)) =
        (HexRealRootsMathlib.Dyadic.toReal (cert.intervals[cut.val - 1]'(by omega)).upper +
          HexRealRootsMathlib.Dyadic.toReal (cert.intervals[cut.val]'(by omega)).lower) / 2 := by
      rw [toReal_shiftRight, toReal_add]
      norm_num
      ring
    have hmid : HexRealRootsMathlib.Dyadic.toReal
          (((cert.intervals[cut.val - 1]'(by omega)).upper +
            (cert.intervals[cut.val]'(by omega)).lower) >>> (1 : Int)) =
        HexRealRootsMathlib.Dyadic.toReal gap.midpoint := by
      rw [hraw, toReal_midpoint]
    rw [← hmid] at hsem
    simpa [Sem, IsolationCert.openPoint, hzero, hleft, hright] using hsem

/-- Every real point belongs to at least one semantic cell. -/
theorem exists_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) :
    ∃ c : Cell cert.intervals.size, Sem M c x := by
  simpa only [sem_eq_region] using Region.exists_mem M.root x

/-- Cells earlier in the alternating enumeration lie strictly to the left. -/
theorem lt_of_rank_lt {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) {c d : Cell cert.intervals.size} {x y : ℝ}
    (hcd : rank c < rank d) (hx : Sem M c x) (hy : Sem M d y) : x < y := by
  rw [sem_eq_region] at hx hy
  exact Region.lt_of_rank_lt M.root M.strictMono hcd hx hy

/-- Semantic cell membership is unique. -/
theorem unique_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) {c d : Cell cert.intervals.size}
    (hc : Sem M c x) (hd : Sem M d x) : c = d := by
  rw [sem_eq_region] at hc hd
  exact Region.unique_mem M.root M.strictMono x hc hd

/-- The semantic cells form a genuine partition of the real line. -/
theorem existsUnique_mem {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (x : ℝ) :
    ∃! c : Cell cert.intervals.size, Sem M c x := by
  simpa only [sem_eq_region] using Region.existsUnique_mem M.root M.strictMono x

/-- Every semantic cell contains a real point. -/
theorem exists_point {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (c : Cell cert.intervals.size) :
    ∃ x : ℝ, Sem M c x := by
  simpa only [sem_eq_region] using Region.exists_point M.root M.strictMono c

/-- Every open semantic cell is an interval, hence preconnected. -/
theorem isPreconnected_open {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cut : Fin (cert.intervals.size + 1)) :
    IsPreconnected {x : ℝ | Sem M (.open cut) x} := by
  simpa only [sem_eq_region] using Region.isPreconnected_open M.root cut

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

namespace RootModel

/-- The closed-on-the-right span from the open cell immediately left of root
`i` to that root. -/
def leftSpan {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (i : Fin cert.intervals.size) : Set ℝ :=
  if hi : i.val = 0 then Set.Iic (M.root i)
  else Set.Ioc (M.root ⟨i.val - 1, by omega⟩) (M.root i)

/-- A root and the open cell immediately to its left form an interval. -/
theorem isPreconnected_leftSpan {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (i : Fin cert.intervals.size) :
    IsPreconnected (M.leftSpan i) := by
  by_cases hi : i.val = 0
  · simpa [leftSpan, hi] using isPreconnected_Iic
  · simpa [leftSpan, hi] using isPreconnected_Ioc

/-- The open cell immediately left of root `i` lies in its left span. -/
theorem leftOpen_mem_leftSpan {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (i : Fin cert.intervals.size) {x : ℝ}
    (hx : Cell.Sem M (.open i.castSucc) x) : x ∈ M.leftSpan i := by
  have hsize : cert.intervals.size ≠ 0 := by
    have := i.isLt
    omega
  by_cases hi : i.val = 0
  · simp only [leftSpan, hi, dite_true, Set.mem_Iic]
    have hx0 : x < M.root ⟨0, by omega⟩ := by
      simpa [Cell.Sem, hsize, hi] using hx
    have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hieq]
    exact hx0.le
  · have hright : i.val ≠ cert.intervals.size := by omega
    have hx' : M.root ⟨i.val - 1, by omega⟩ < x ∧ x < M.root i := by
      simpa [Cell.Sem, hsize, hi, hright] using hx
    simpa [leftSpan, hi] using And.intro hx'.1 hx'.2.le

/-- Root `i` is the right endpoint of its left span. -/
theorem root_mem_leftSpan {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (i : Fin cert.intervals.size) :
    M.root i ∈ M.leftSpan i := by
  by_cases hi : i.val = 0
  · simp [leftSpan, hi]
  · simp only [leftSpan, hi, dite_false, Set.mem_Ioc]
    exact ⟨M.strictMono (Fin.mk_lt_mk.mpr (by omega)), le_rfl⟩

/-- A carrier root in the left span of root `i` is root `i` itself. -/
theorem root_unique_leftSpan
    {carrier : ZPoly} {cert : IsolationCert}
    (M : RootModel carrier cert) (i : Fin cert.intervals.size) {x : ℝ}
    (hxroot : (toPolyℝ carrier).IsRoot x) (hx : x ∈ M.leftSpan i) :
    x = M.root i := by
  obtain ⟨j, hj, _⟩ := M.complete x hxroot
  rw [← hj] at hx ⊢
  congr 1
  apply Fin.ext
  by_cases hi : i.val = 0
  · simp only [leftSpan, hi, dite_true, Set.mem_Iic] at hx
    by_contra hne
    have hij : i < j := by omega
    exact (not_lt_of_ge hx) (M.strictMono hij)
  · simp only [leftSpan, hi, dite_false, Set.mem_Ioc] at hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with hji | hij
    · let prev : Fin cert.intervals.size := ⟨i.val - 1, by omega⟩
      have hjprevIndex : j ≤ prev := by
        apply Fin.mk_le_mk.mpr
        omega
      have hjprev : M.root j ≤ M.root ⟨i.val - 1, by omega⟩ :=
        M.strictMono.monotone hjprevIndex
      exact (not_lt_of_ge hjprev) hx.1
    · exact (not_lt_of_ge hx.2) (M.strictMono (Fin.mk_lt_mk.mpr hij))

end RootModel

namespace IocCmps

/-- A checked comparison vector has its claimed meaning against the chosen
semantic roots. -/
theorem holds_of_check {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hreplay : replay.check f = true)
    (hstrict : cert.checkStrict replay = true)
    (hcmps : check f replay cert a b cmps = true)
    (i : Fin cert.intervals.size) :
    cmps.lower[i].Holds ((cert.rootModel hreplay hstrict).root i)
        (HexRealRootsMathlib.Dyadic.toReal a) ∧
      cmps.upper[i].Holds ((cert.rootModel hreplay hstrict).root i)
        (HexRealRootsMathlib.Dyadic.toReal b) := by
  have hmem : i.val ∈ List.range cert.intervals.size := List.mem_range.mpr i.isLt
  have hstep := (List.all_eq_true.mp hcmps) i.val hmem
  simp only [i.isLt, dite_true, Bool.and_eq_true] at hstep
  have cmpHolds (endpoint : Dyadic) (claim : Separation.RootCmp)
      (hclaim : Separation.checkCmp f replay cert.intervals[i] endpoint claim = true) :
      claim.Holds ((cert.rootModel hreplay hstrict).root i)
        (HexRealRootsMathlib.Dyadic.toReal endpoint) := by
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

/-- A valid root comparison equals `gt` exactly when the endpoint is below the root. -/
private theorem eq_gt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp == .gt) = true ↔ endpoint < root := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

/-- A valid root comparison differs from `gt` exactly when the root is at most the endpoint. -/
private theorem ne_gt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp != .gt) = true ↔ root ≤ endpoint := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

/-- A valid root comparison equals `lt` exactly when the root is below the endpoint. -/
private theorem eq_lt_iff {cmp : Separation.RootCmp} {root endpoint : ℝ}
    (h : cmp.Holds root endpoint) :
    (cmp == .lt) = true ↔ root < endpoint := by
  cases cmp <;> simp [Separation.RootCmp.Holds] at h ⊢ <;> linarith

/-- The executable relevance table is exactly semantic intersection with a
nonempty half-open interval. -/
theorem meetsIoc_iff {f : ZPoly} {cert : IsolationCert}
    (M : RootModel f cert) (cmps : IocCmps cert.intervals.size)
    (a b : Dyadic) (hab : HexRealRootsMathlib.Dyadic.toReal a < HexRealRootsMathlib.Dyadic.toReal b)
    (hlower : ∀ i : Fin cert.intervals.size,
      Separation.RootCmp.Holds cmps.lower[i] (M.root i) (HexRealRootsMathlib.Dyadic.toReal a))
    (hupper : ∀ i : Fin cert.intervals.size,
      Separation.RootCmp.Holds cmps.upper[i] (M.root i) (HexRealRootsMathlib.Dyadic.toReal b))
    (c : Cell cert.intervals.size) :
    meetsIoc cmps c = true ↔
      ∃ x : ℝ, Sem M c x ∧
        x ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a) (HexRealRootsMathlib.Dyadic.toReal b) := by
  let A := HexRealRootsMathlib.Dyadic.toReal a
  let B := HexRealRootsMathlib.Dyadic.toReal b
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
        rw [dite_eq_left hzero]
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
        rw [dite_eq_right hzero, dite_eq_left hleft, hbound]
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
        rw [dite_eq_right hzero, dite_eq_right hleft, dite_eq_left hright, hbound]
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
        rw [dite_eq_right hzero, dite_eq_right hleft, dite_eq_right hright, Bool.and_eq_true,
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
    (hab : HexRealRootsMathlib.Dyadic.toReal a < HexRealRootsMathlib.Dyadic.toReal b)
    (c : Cell cert.intervals.size) :
    meetsIoc cmps c = true ↔
      ∃ x : ℝ, Sem (cert.rootModel hreplay hstrict) c x ∧
        x ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a) (HexRealRootsMathlib.Dyadic.toReal b) := by
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
        x ∈ Set.Ioc (HexRealRootsMathlib.Dyadic.toReal a) (HexRealRootsMathlib.Dyadic.toReal b) := by
  by_cases hab : a < b
  · simp only [meetsIocOn, hab, decide_true]
    exact meetsIoc_iff_of_check cmps a b hreplay hstrict hcmps
      (toReal_lt_toReal hab) c
  · constructor
    · simp [meetsIocOn, hab]
    · rintro ⟨x, -, hax, hxb⟩
      have hreal : ¬HexRealRootsMathlib.Dyadic.toReal a < HexRealRootsMathlib.Dyadic.toReal b := by
        simpa [toReal_lt_toReal_iff] using hab
      exact (hreal (lt_of_lt_of_le hax hxb)).elim

end Cell

end Hex.RCF
