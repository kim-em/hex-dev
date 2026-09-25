/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationCheck
public import HexRCF.Cells
public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed

public section

/-! Mathematical root and sign meaning of the finite isolation replay. These
semantic theorems consume the single shared root-sum bridge owned by #10389;
the Boolean checker and its literal acceptance do not. -/

namespace Hex.RCF.RealCoefficients.IsolationReplay

open HexRealRootsMathlib HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable (f : E → ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : ℝ))
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (point : Dyadic → E) (hpoint : ∀ d, f (point d) = HexRealRootsMathlib.Dyadic.toReal d)

include h1 ha hs hm hnat hsign in
/-- The total query counts all distinct real roots of a nonzero head. -/
theorem total_spec (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) :
    interpret f hz head ≠ 0 ∧
      (Tarski.rootsIn (interpret f hz head) .negInf .posInf).card = cert.isolations.intervals.size := by
  classical
  simp only [check, Bool.and_eq_true] at h
  have spec := HexSturmMathlib.check_sound f hz h1 ha hs hm hnat sign hsign
    context head 1 .negInf .posInf cert.isolations.intervals.size cert.total h.1.2
  refine ⟨spec.1.1, ?_⟩
  have hc := spec.2
  rw [interpret_one f hz h1, Tarski.rootSum_one] at hc
  exact_mod_cast hc.symm

include h1 ha hs hm hnat hsign hpoint in
/-- Each accepted interval contains exactly one distinct real root. Endpoints
are open, as required by the shared query checker. -/
theorem interval_card (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) (i : Fin cert.isolations.intervals.size) :
    (Tarski.rootsIn (interpret f hz head)
      (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower))
      (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper))).card = 1 := by
  classical
  have spec := HexSturmMathlib.check_sound f hz h1 ha hs hm hnat sign hsign
    context head 1 _ _ 1 cert.counts[i] (cert.count_checked sign point context head h i)
  have hc := spec.2
  rw [interpret_one f hz h1, Tarski.rootSum_one] at hc
  simp only [Endpoint.map, hpoint] at hc
  exact_mod_cast hc.symm

include h1 ha hs hm hnat hsign hpoint in
/-- A checked interval selects one actual real root, rather than merely a
formal root count. -/
theorem existsUnique_root (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) (i : Fin cert.isolations.intervals.size) :
    ∃! x : ℝ, (interpret f hz head).IsRoot x ∧
      HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < x ∧
      x < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper := by
  classical
  have hp := (cert.total_spec f hz h1 ha hs hm hnat sign hsign point context head h).1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
    (cert.interval_card f hz h1 ha hs hm hnat sign hsign point hpoint context head h i)
  have hmem : ∀ y, (interpret f hz head).IsRoot y ∧
      HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < y ∧
      y < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper ↔ y = x := by
    intro y
    have hm := Tarski.mem_rootsIn_iff (interpret f hz head) hp
      (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower))
      (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper)) y
    rw [hx] at hm
    simpa only [Finset.mem_singleton, Polynomial.IsRoot, Tarski.inInterval_finite] using hm.symm
  exact ⟨x, (hmem x).mpr rfl, fun y hy => (hmem y).mp hy⟩

include h1 ha hs hm hnat hsign hpoint in
/-- Accepted counts and gaps give a complete, strictly ordered list of real
roots. Completeness comes from the checked total count, including when there
are no roots, rather than from an assumption about the proposed intervals. -/
theorem check_roots (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) :
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, (interpret f hz head).IsRoot (root i) ∧
        HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, (interpret f hz head).IsRoot x ↔ ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  classical
  have total := cert.total_spec f hz h1 ha hs hm hnat sign hsign point context head h
  have each := cert.existsUnique_root f hz h1 ha hs hm hnat sign hsign point hpoint context head h
  choose root hroot _ using each
  have gaps : cert.isolations.checkGaps = true := by
    simp only [check, Bool.and_eq_true] at h
    exact h.1.1
  have hmono : StrictMono root := by
    intro i j hij
    exact IsolationCert.roots_lt_of_check gaps hij
      ⟨(hroot i).2.1, (hroot i).2.2.le⟩ ⟨(hroot j).2.1, (hroot j).2.2.le⟩
  let roots := Tarski.rootsIn (interpret f hz head) .negInf .posInf
  have hmem (x : ℝ) : x ∈ roots ↔ (interpret f hz head).IsRoot x := by
    simp only [roots, Tarski.mem_rootsIn_iff _ total.1, Tarski.inInterval_univ, and_true]
    rfl
  have image : Finset.image root Finset.univ = roots := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hmem _).mpr (hroot i).1
    · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
        Fintype.card_fin]
      exact total.2.le
  refine ⟨root, hroot, hmono, ?_, ?_⟩
  · intro x
    rw [← hmem, ← image]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
  · intro cut
    exact Cell.openPoint_mem_region cert.isolations root gaps
      (fun i => ⟨(hroot i).2.1, (hroot i).2.2.le⟩) cut

omit [One E] [Sub E] [NatCast E] [DecidableEq Ctx] in
include ha hm hsign hpoint in
/-- A sign computed at a checked open-cell sample remains the sign throughout
that cell when every root of the query polynomial is a root of the carrier. -/
theorem open_sign (head q : DensePoly E) (cert : IsolationReplay E Ctx)
    (root : Fin cert.isolations.intervals.size → ℝ) (hmono : StrictMono root)
    (hcomplete : ∀ z, (interpret f hz head).IsRoot z ↔ ∃ i, root i = z)
    (cut : Fin (cert.isolations.intervals.size + 1))
    (hsample : Cell.Region root (.open cut)
      (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut)))
    (hroots : interpret f hz q = 0 ∨
      ∀ z, (interpret f hz q).IsRoot z → (interpret f hz head).IsRoot z)
    (x : ℝ) (hx : Cell.Region root (.open cut) x) :
    sign (q.eval (point (cert.isolations.openPoint cut))) =
      (SignType.sign ((interpret f hz q).eval x) : Int) := by
  have hsubset : interpret f hz q = 0 ∨
      ∀ z, (interpret f hz q).IsRoot z → ∃ i, root i = z :=
    hroots.imp_right (fun h z hzq => (hcomplete z).mp (h z hzq))
  have hs := Cell.Region.sign_eq root hmono (interpret f hz q)
    hsubset (.open cut) hsample hx
  rw [hsign, ← eval_interpret f hz ha hm q, hpoint]
  exact congrArg (fun s : SignType => (s : Int)) hs

include h1 ha hs hm hnat hsign hpoint in
/-- On an accepted count-one interval, an arbitrary checked Tarski query is
exactly the sign at its selected root, including a zero query value. -/
theorem check_sign (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) (i : Fin cert.isolations.intervals.size)
    (q : DensePoly E) (value : Int) (evidence : TarskiCertificate E E Ctx)
    (checked : Sturm.check sign context head q
      (.finite (point cert.isolations.intervals[i].lower))
      (.finite (point cert.isolations.intervals[i].upper)) value evidence = true)
    (x : ℝ) (hx : (interpret f hz head).IsRoot x)
    (hl : HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < x)
    (hu : x < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper) :
    value = (SignType.sign ((interpret f hz q).eval x) : Int) := by
  classical
  have hp := (cert.total_spec f hz h1 ha hs hm hnat sign hsign point context head h).1
  have hc := cert.interval_card f hz h1 ha hs hm hnat sign hsign point hpoint context head h i
  have hmem := (Tarski.mem_rootsIn_iff (interpret f hz head) hp
    (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower))
    (.finite (HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper)) x).mpr
      ⟨hx, (Tarski.inInterval_finite _ _ _).mpr ⟨hl, hu⟩⟩
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc
  have hxr : x = r := by simpa only [hr, Finset.mem_singleton] using hmem
  have hs := (HexSturmMathlib.check_sound f hz h1 ha hs hm hnat sign hsign
    context head q _ _ value evidence checked).2
  simp only [Endpoint.map, hpoint] at hs
  rw [Tarski.rootSum_singleton _ _ _ _ r hr, ← hxr] at hs
  exact hs

end Hex.RCF.RealCoefficients.IsolationReplay
