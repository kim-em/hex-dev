/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.CommonRootCheck
public import HexRCF.Cells

public section

/-!
# Real-root semantics of certified common roots

The Mathlib-free package and checker live in `HexRCF.CommonRootCheck`. The
theorems in this file prove that an accepted package has exactly the common
real roots of the atom and square-free carrier, and connect its cached replay
query to semantic root cells.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

namespace CommonRootCert

/-- A checked common-root polynomial has exactly the common real roots of the
atom and carrier. -/
theorem isRoot_iff {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) (x : ℝ) :
    (toPolyℝ cert.gcd).IsRoot x ↔
      (toPolyℝ atom).IsRoot x ∧ (toPolyℝ carrier).IsRoot x := by
  obtain ⟨hscale, hatom, hcarrier, hbezout, _hreplay⟩ := check_sound h
  have hscaleℝ : ((cert.scale : Int) : ℝ) ≠ 0 := by exact_mod_cast hscale
  have hatomℝ := congrArg toPolyℝ hatom
  have hcarrierℝ := congrArg toPolyℝ hcarrier
  have hbezoutℝ := congrArg toPolyℝ hbezout
  rw [toPolyℝ_mul] at hatomℝ hcarrierℝ
  rw [toPolyℝ_add, toPolyℝ_mul, toPolyℝ_mul, toPolyℝ_scale] at hbezoutℝ
  constructor
  · intro hgcd
    constructor
    · rw [Polynomial.IsRoot, hatomℝ, Polynomial.eval_mul]
      rw [show (toPolyℝ cert.gcd).eval x = 0 from hgcd, zero_mul]
    · rw [Polynomial.IsRoot, hcarrierℝ, Polynomial.eval_mul]
      rw [show (toPolyℝ cert.gcd).eval x = 0 from hgcd, zero_mul]
  · rintro ⟨hatomRoot, hcarrierRoot⟩
    simp only [Polynomial.IsRoot] at hatomRoot hcarrierRoot ⊢
    have heval := congrArg (Polynomial.eval x) hbezoutℝ
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at heval
    simp only [hatomRoot, hcarrierRoot, mul_zero, zero_add] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left hscaleℝ

/-- A checked constant common-root branch has no real roots. -/
theorem noRoot_of_constant {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) (hreplay : cert.replay = none)
    (x : ℝ) : ¬(toPolyℝ cert.gcd).IsRoot x := by
  have hvalid := (check_sound h).2.2.2.2
  simp only [ReplayValid, hreplay] at hvalid
  have hg0 : cert.gcd ≠ 0 := gcd_ne_zero h
  have hcast0 : toPolyℝ cert.gcd ≠ 0 :=
    fun hzero => hg0 (toPolyℝ_eq_zero_iff.mp hzero)
  have hdegree : (toPolyℝ cert.gcd).natDegree = 0 := by
    rw [natDegree_toPolyℝ,
      DensePoly.degree?_eq_some_of_pos_size cert.gcd (by omega), hvalid]
    rfl
  have hunit : IsUnit (toPolyℝ cert.gcd) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_eq_natDegree hcast0, hdegree]
    rfl
  intro hroot
  obtain ⟨u, hu, hunitEq⟩ := Polynomial.isUnit_iff.mp hunit
  rw [← hunitEq, Polynomial.IsRoot, Polynomial.eval_C] at hroot
  exact hu.ne_zero hroot

/-- A cached nonconstant replay counts one common root in a carrier isolation
exactly when the atom vanishes at its supplied carrier root. -/
theorem count_eq_one_iff {carrier : ZPoly} {carrierReplay : SturmReplay}
    (hcarrier : carrierReplay.check carrier = true)
    {isolations : IsolationCert} (hcert : isolations.check carrierReplay = true)
    {atom : ZPoly} {common : CommonRootCert} {gcdReplay : SturmReplay}
    (hcommon : common.check atom carrier = true)
    (hgcdReplay : common.replay = some gcdReplay)
    (i : Fin isolations.intervals.size) {root : ℝ}
    (hroot : (toPolyℝ carrier).IsRoot root)
    (hmem : Literal.InInterval isolations.intervals[i] root) :
    gcdReplay.count isolations.intervals[i] = 1 ↔
      (toPolyℝ atom).IsRoot root := by
  classical
  let I := isolations.intervals[i]
  have hgReplay : gcdReplay.check common.gcd = true :=
    common.replay_of_check hcommon hgcdReplay
  have hP0 : toPolyℝ carrier ≠ 0 := by
    intro hzero
    exact SturmReplay.head_ne_zero hcarrier (toPolyℝ_eq_zero_iff.mp hzero)
  have hgDiv : toPolyℝ common.gcd ∣ toPolyℝ carrier := by
    obtain ⟨_scale, _atom, hfactor, _bezout, _replay⟩ := check_sound hcommon
    refine ⟨toPolyℝ common.carrierFactor, ?_⟩
    simpa only [toPolyℝ_mul] using congrArg toPolyℝ hfactor
  have hrootsLe :
      Literal.rootsIn (toPolyℝ common.gcd) I ≤
        Literal.rootsIn (toPolyℝ carrier) I := by
    exact Multiset.filter_le_filter _
      (Polynomial.roots.le_of_dvd hP0 hgDiv)
  have hcarrierCard :
      (Literal.rootsIn (toPolyℝ carrier) I).card = 1 := by
    have hcount := IsolationCert.count_one_of_check
      (IsolationCert.counts_of_check hcert) i
    have hcard := SturmReplay.count_eq_card_roots hcarrier I
    rw [hcount] at hcard
    exact_mod_cast hcard.symm
  constructor
  · intro hcount
    have hcard : (Literal.rootsIn (toPolyℝ common.gcd) I).card = 1 := by
      have hcard := SturmReplay.count_eq_card_roots hgReplay I
      rw [hcount] at hcard
      exact_mod_cast hcard.symm
    have hpos : 0 < (Literal.rootsIn (toPolyℝ common.gcd) I).card := by
      omega
    obtain ⟨y, hrootMem⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    simp only [Literal.rootsIn, Multiset.mem_filter] at hrootMem
    have hgRoot : (toPolyℝ common.gcd).IsRoot y :=
      (Polynomial.mem_roots'.mp hrootMem.1).2
    have hboth := (common.isRoot_iff hcommon y).mp hgRoot
    have hrootEq : y = root :=
      (IsolationCert.exists_unique_root_of_check hcarrier hcert i).unique
        ⟨hboth.2, hrootMem.2⟩ ⟨hroot, hmem⟩
    simpa only [hrootEq] using hboth.1
  · intro hatomRoot
    have hgRoot : (toPolyℝ common.gcd).IsRoot root :=
      (common.isRoot_iff hcommon _).mpr ⟨hatomRoot, hroot⟩
    have hg0 : toPolyℝ common.gcd ≠ 0 := by
      intro hzero
      exact SturmReplay.head_ne_zero hgReplay (toPolyℝ_eq_zero_iff.mp hzero)
    have hgMem : root ∈ Literal.rootsIn (toPolyℝ common.gcd) I := by
      simp only [Literal.rootsIn, Multiset.mem_filter]
      exact ⟨Polynomial.mem_roots'.mpr ⟨hg0, hgRoot⟩, hmem⟩
    have hpos : 0 < (Literal.rootsIn (toPolyℝ common.gcd) I).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨_, hgMem⟩
    have hle : (Literal.rootsIn (toPolyℝ common.gcd) I).card ≤ 1 := by
      rw [← hcarrierCard]
      exact Multiset.card_le_card hrootsLe
    have hcard : (Literal.rootsIn (toPolyℝ common.gcd) I).card = 1 := by omega
    have hcount := SturmReplay.count_eq_card_roots hgReplay I
    simpa only [hcard, Nat.cast_one] using hcount

/-- The executable cached-root query is exact at a supplied carrier root in a
checked isolation, including the constant-gcd branch. -/
theorem hasRoot_iff {carrier : ZPoly} {carrierReplay : SturmReplay}
    (hcarrier : carrierReplay.check carrier = true)
    {isolations : IsolationCert}
    (hcert : isolations.check carrierReplay = true)
    {atom : ZPoly} {common : CommonRootCert}
    (hcommon : common.check atom carrier = true)
    (i : Fin isolations.intervals.size) {root : ℝ}
    (hroot : (toPolyℝ carrier).IsRoot root)
    (hmem : Literal.InInterval isolations.intervals[i] root) :
    common.hasRoot isolations.intervals[i] = true ↔
      (toPolyℝ atom).IsRoot root := by
  cases hreplay : common.replay with
  | none =>
      constructor
      · simp [hasRoot, hreplay]
      · intro hatom
        have hgcd := (common.isRoot_iff hcommon _).mpr ⟨hatom, hroot⟩
        exact (common.noRoot_of_constant hcommon hreplay _ hgcd).elim
  | some replay =>
      simp only [hasRoot, hreplay, decide_eq_true_eq]
      exact common.count_eq_one_iff hcarrier hcert hcommon hreplay i hroot hmem

/-- Specialize `hasRoot_iff` to the canonical root model of a strict
isolation certificate. -/
theorem hasRoot_model_iff {carrier : ZPoly} {carrierReplay : SturmReplay}
    (hcarrier : carrierReplay.check carrier = true)
    {isolations : IsolationCert}
    (hstrict : isolations.checkStrict carrierReplay = true)
    {atom : ZPoly} {common : CommonRootCert}
    (hcommon : common.check atom carrier = true)
    (i : Fin isolations.intervals.size) :
    common.hasRoot isolations.intervals[i] = true ↔
      (toPolyℝ atom).IsRoot
        ((isolations.rootModel hcarrier hstrict).root i) :=
  common.hasRoot_iff hcarrier (IsolationCert.check_of_checkStrict hstrict)
    hcommon i ((isolations.rootModel hcarrier hstrict).isRoot i)
    ((isolations.rootModel hcarrier hstrict).inInterval i)

end CommonRootCert

end Hex.RCF
