/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Cells

public section

/-!
# Certified common roots for RCF sign matrices

A common-root package is checked once for each distinct nonconstant atom
polynomial.  Its multiplication identities prove that a supplied polynomial
has exactly the common real roots of the atom and the square-free carrier.  A
nonconstant common-root polynomial also carries one generalized Sturm replay,
which is then shared by every carrier root cell.
-/

namespace Hex.RCF

open HexRealRootsMathlib Polynomial

/-- Multiplication-checkable witnesses for the common roots of an atom and a
carrier polynomial.  The atom and carrier themselves are external checker
inputs, so certificate data cannot silently substitute different polynomials.
-/
structure CommonRootCert where
  /-- Proposed common-root polynomial. -/
  gcd : ZPoly
  /-- Quotient witnessing that the common-root polynomial divides the atom. -/
  atomFactor : ZPoly
  /-- Quotient witnessing that the common-root polynomial divides the carrier. -/
  carrierFactor : ZPoly
  /-- Atom coefficient in the scaled Bezout identity. -/
  atomCoeff : ZPoly
  /-- Carrier coefficient in the scaled Bezout identity. -/
  carrierCoeff : ZPoly
  /-- Nonzero integer scale in the Bezout identity. -/
  scale : Int
  /-- Cached replay for a nonconstant common-root polynomial.  A nonzero
  constant common-root polynomial uses `none`. -/
  replay : Option SturmReplay

namespace CommonRootCert

/-- Validate the constant/nonconstant replay branch. -/
@[expose]
def checkReplay (cert : CommonRootCert) : Bool :=
  match cert.replay with
  | none => decide (cert.gcd.size = 1)
  | some replay =>
      -- The replay checker already implies this degree bound.  Keeping the
      -- guard makes the constant/nonconstant trust boundary explicit.
      decide (0 < cert.gcd.degree?.getD 0) && replay.check cert.gcd

/-- Proposition-level replay facts recovered from `checkReplay`. -/
@[expose]
def ReplayValid (cert : CommonRootCert) : Prop :=
  match cert.replay with
  | none => cert.gcd.size = 1
  | some replay =>
      0 < cert.gcd.degree?.getD 0 ∧ replay.check cert.gcd = true

/-- Check the divisibility and scaled Bezout identities against the external
atom and carrier polynomials. -/
@[expose]
def check (atom carrier : ZPoly) (cert : CommonRootCert) : Bool :=
  decide (cert.scale ≠ 0) &&
  DensePoly.beqCoeffs atom (cert.gcd * cert.atomFactor) &&
  DensePoly.beqCoeffs carrier (cert.gcd * cert.carrierFactor) &&
  DensePoly.beqCoeffs
    (cert.atomCoeff * atom + cert.carrierCoeff * carrier)
    (DensePoly.scale cert.scale cert.gcd) &&
  cert.checkReplay

/-- Proposition-level facts recovered from the common-root checker. -/
@[expose]
def Valid (atom carrier : ZPoly) (cert : CommonRootCert) : Prop :=
  cert.scale ≠ 0 ∧
  atom = cert.gcd * cert.atomFactor ∧
  carrier = cert.gcd * cert.carrierFactor ∧
  cert.atomCoeff * atom + cert.carrierCoeff * carrier =
    DensePoly.scale cert.scale cert.gcd ∧
  cert.ReplayValid

/-- Soundness of the constant/nonconstant replay branch. -/
theorem checkReplay_sound {cert : CommonRootCert}
    (h : cert.checkReplay = true) : cert.ReplayValid := by
  cases hreplay : cert.replay with
  | none => simpa [checkReplay, ReplayValid, hreplay] using h
  | some replay => simpa [checkReplay, ReplayValid, hreplay] using h

/-- Soundness of the executable common-root checker. -/
theorem check_sound {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) : cert.Valid atom carrier := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hscale, hatom⟩, hcarrier⟩, hbezout⟩, hreplay⟩ := h
  exact ⟨hscale, DensePoly.eq_of_beqCoeffs hatom,
    DensePoly.eq_of_beqCoeffs hcarrier,
    DensePoly.eq_of_beqCoeffs hbezout, checkReplay_sound hreplay⟩

/-- A checked common-root polynomial is nonzero in both certificate branches. -/
theorem gcd_ne_zero {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) : cert.gcd ≠ 0 := by
  have hvalid := (check_sound h).2.2.2.2
  cases hreplay : cert.replay with
  | none =>
      simp only [ReplayValid, hreplay] at hvalid
      intro hzero
      rw [hzero] at hvalid
      simp at hvalid
  | some replay =>
      simp only [ReplayValid, hreplay] at hvalid
      exact SturmReplay.head_ne_zero hvalid.2

/-- Recover the checked replay in the nonconstant certificate branch. -/
theorem replay_of_check {atom carrier : ZPoly} {cert : CommonRootCert}
    {replay : SturmReplay} (h : cert.check atom carrier = true)
    (hreplay : cert.replay = some replay) : replay.check cert.gcd = true := by
  have hvalid := (check_sound h).2.2.2.2
  simp only [ReplayValid, hreplay] at hvalid
  exact hvalid.2

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

/-- Decide whether the cached common-root polynomial has a root in an
interval.  The constant branch is root-free; the nonconstant branch reads its
shared generalized Sturm replay.  Its semantic guarantee applies when the
interval comes from a checked carrier isolation. -/
@[expose]
def hasRoot (cert : CommonRootCert) (I : DyadicInterval) : Bool :=
  match cert.replay with
  | none => false
  | some replay => decide (replay.count I = 1)

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
