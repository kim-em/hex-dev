/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Basic
public import HexSignDetMathlib.SelectedRoot
public import HexSturmMathlib.Domain
public import HexRealRootsMathlib.RealClosed

public section

namespace Hex.RealClosure

open HexPolyMathlib.Interpret

/-- The coefficient embedding used for rational selected-root interpretation. -/
@[expose] def ratCast : Rat → ℝ := fun q => (q : ℝ)
theorem ratZero (q : Rat) : ratCast q = 0 ↔ q = 0 := Rat.cast_eq_zero
theorem ratOne : ratCast (1 : Rat) = 1 := by simp [ratCast]
theorem ratAdd (a b : Rat) : ratCast (a + b) = ratCast a + ratCast b := by
  simp [ratCast]
theorem ratSub (a b : Rat) : ratCast (a - b) = ratCast a - ratCast b := by
  simp [ratCast]
theorem ratMul (a b : Rat) : ratCast (a * b) = ratCast a * ratCast b := by
  simp [ratCast]
theorem ratDiv (a b : Rat) : ratCast (a / b) = ratCast a / ratCast b := by
  simp [ratCast]
theorem ratNat (n : Nat) : ratCast (n : Rat) = (n : ℝ) := by
  simp [ratCast]

theorem ratSign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (ratCast q) : Int) := by
  by_cases hn : q < 0
  · have hn' : ratCast q < 0 := by simpa [ratCast] using hn
    simp [Sturm.orderSign, hn, sign_eq_neg_one_iff.mpr hn']
  · by_cases hz : q = 0
    · subst q
      simp [Sturm.orderSign, ratCast]
    · have hp : 0 < q := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hp' : 0 < ratCast q := by simpa [ratCast] using hp
      simp [Sturm.orderSign, hn, hz, sign_eq_one_iff.mpr hp']

/-- Interpret a rational dense polynomial over the real numbers. -/
@[expose] noncomputable def realPoly (p : DensePoly Rat) : Polynomial ℝ :=
  interpret ratCast ratZero p

theorem realPoly_mul (p q : DensePoly Rat) :
    realPoly (p * q) = realPoly p * realPoly q :=
  interpret_mul ratCast ratZero ratAdd ratMul p q

theorem realPoly_add (p q : DensePoly Rat) :
    realPoly (p + q) = realPoly p + realPoly q :=
  interpret_add ratCast ratZero ratAdd p q

/-- The real root denoted by a checked rational descriptor. -/
@[expose] noncomputable def Root.real {context : Nat} (d : Root context) : ℝ :=
  d.root ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign

/-- The selected root satisfies the checked head, interval and derivative signs. -/
theorem Root.real_spec {context : Nat} (d : Root context) :
    d.real ∈ HexRealRootsMathlib.Tarski.rootsIn (realPoly d.raw.head)
      (d.raw.lower.map ratCast) (d.raw.upper.map ratCast) ∧
    SignDet.signsAt ratCast ratZero d.raw.queries d.real = d.raw.signs := by
  exact d.root_spec ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign

/-- The descriptor's conditions identify the same selected real root. -/
theorem Root.real_unique {context : Nat} (d : Root context) (x : ℝ)
    (hx : x ∈ HexRealRootsMathlib.Tarski.rootsIn (realPoly d.raw.head)
      (d.raw.lower.map ratCast) (d.raw.upper.map ratCast))
    (hs : SignDet.signsAt ratCast ratZero d.raw.queries x = d.raw.signs) :
    x = d.real :=
  d.root_unique ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign x hx hs

/-- The checked rational definition is squarefree after interpretation. -/
theorem Root.real_squarefree {context : Nat} (d : Root context) :
    Squarefree (realPoly d.raw.head) := by
  obtain ⟨_, _, hc, _⟩ := SignDet.RawDescriptor.check_eq d.accepted
  exact (d.evidence.check_domain ratCast ratZero ratOne ratAdd ratSub ratMul ratNat
    Sturm.orderSign ratSign context d.raw.head d.raw.lower d.raw.upper d.raw.queries hc).2.1

/-- Revalidation in a new context version retains the selected real root. -/
theorem Rebinding.real_eq_source {context version : Nat} {source : Root context}
    (r : Rebinding source version) : r.target.real = source.real := by
  have hchecked : SignDet.Descriptor.validate Sturm.orderSign version
      { source.raw with context := version } = some r.target := r.checked
  have hraw : r.target.raw = { source.raw with context := version } :=
    SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp hchecked)
  let x := r.target.real
  have hs := r.target.root_spec ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign
  have hs' : x ∈ HexRealRootsMathlib.Tarski.rootsIn
      (interpret ratCast ratZero source.raw.head)
      (source.raw.lower.map ratCast) (source.raw.upper.map ratCast) ∧
      SignDet.signsAt ratCast ratZero source.raw.queries x = source.raw.signs := by
    simpa [x, Root.real, hraw, SignDet.RawDescriptor.queries] using hs
  have heq := source.root_unique ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign
    x hs'.1 hs'.2
  simpa [x, Root.real] using heq

namespace Expression

/-- Evaluate the stored polynomial at the descriptor's selected real root. -/
@[expose] noncomputable def denote {context : Nat} {d : Root context} (a : Expression d) : ℝ :=
  (realPoly a.polynomial).eval d.real

@[simp] theorem denote_ofPoly {context : Nat} {d : Root context} (p : DensePoly Rat) :
    (ofPoly p : Expression d).denote = (realPoly p).eval d.real := rfl

@[simp] theorem denote_head {context : Nat} {d : Root context} :
    (ofPoly d.raw.head : Expression d).denote = 0 := by
  have hne : realPoly d.raw.head ≠ 0 := d.head_ne_zero ratCast ratZero
  have hroot := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mp
    d.real_spec.1
  exact hroot.1

@[simp] theorem denote_zero {context : Nat} {d : Root context} :
    (zero (d := d)).denote = 0 := by
  simp [denote, zero, realPoly]

@[simp] theorem denote_one {context : Nat} {d : Root context} :
    (one (d := d)).denote = 1 := by
  simp [denote, one, realPoly, interpret_one ratCast ratZero ratOne]

@[simp] theorem denote_add {context : Nat} {d : Root context} (a b : Expression d) :
    (add a b).denote = a.denote + b.denote := by
  simp [denote, add, realPoly, interpret_add ratCast ratZero ratAdd]

@[simp] theorem denote_neg {context : Nat} {d : Root context} (a : Expression d) :
    (neg a).denote = -a.denote := by
  simp [denote, neg, realPoly, interpret_neg ratCast ratZero ratSub]

@[simp] theorem denote_sub {context : Nat} {d : Root context} (a b : Expression d) :
    (sub a b).denote = a.denote - b.denote := by
  simp [denote, sub, realPoly, interpret_sub ratCast ratZero ratSub]

@[simp] theorem denote_mul {context : Nat} {d : Root context} (a b : Expression d) :
    (mul a b).denote = a.denote * b.denote := by
  simp [denote, mul, realPoly, interpret_mul ratCast ratZero ratAdd ratMul]

/-- Accepted one-query evidence computes the sign of the selected real value. -/
theorem sign?_sound {context : Nat} {d : Root context} (a : Expression d) (value : Int)
    (h : a.sign? = .ok value) :
    value = (SignType.sign a.denote : Int) := by
  unfold sign? at h
  cases hs : d.buildSigns [a.polynomial] with
  | error err => simp [hs] at h
  | ok s =>
    have heq : s.value = value := by simpa [hs] using h
    simpa [denote, Root.real, realPoly, heq] using
      (s.value_at_root ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign)

/-- A checked zero sign reflects zero at the selected real root. -/
theorem sign?_zero {context : Nat} {d : Root context} (a : Expression d)
    (h : a.sign? = .ok 0) : a.denote = 0 := by
  have hs := a.sign?_sound 0 h
  have hs0 : (SignType.sign a.denote : Int) = 0 := hs.symm
  have hs0' : SignType.sign a.denote = 0 := by
    cases hsg : SignType.sign a.denote <;> simp [hsg] at hs0 ⊢
  exact sign_eq_zero_iff.mp hs0'

/-- The checked inverse result is an inverse of the value at the selected root. -/
theorem inverse?_sound {context : Nat} {d : Root context} (a b : Expression d)
    (h : a.inverse? = .ok (some b)) : a.denote * b.denote = 1 := by
  cases hs : a.sign? with
  | error err => simp [inverse?, hs] at h
  | ok sa =>
    by_cases hz : sa = 0
    · simp [inverse?, hs, hz] at h
    · cases hc : (sub (mul a a.inverseCandidate) one).sign? with
      | error err => simp [inverse?, hs, hz, hc] at h
      | ok sc =>
        by_cases hsc : sc = 0
        · have hb : a.inverseCandidate = b := by
            simpa [inverse?, hs, hz, hc, hsc] using h
          subst b
          have hzero : (sub (mul a a.inverseCandidate) one).denote = 0 :=
            sign?_zero _ (by simpa [hsc] using hc)
          have hprod : a.denote * a.inverseCandidate.denote - 1 = 0 := by
            simpa using hzero
          exact sub_eq_zero.mp hprod
        · simp [inverse?, hs, hz, hc, hsc] at h

/-- The scaled Bézout candidate is an inverse whenever the computed cofactor
vanishes at the selected root and extended gcd has a nonzero constant result. -/
theorem candidate_mul_eq_one {context : Nat} {d : Root context}
    (a : Expression d) (c : Rat)
    (hroot : (realPoly a.inverseFactor.2).eval d.real = 0)
    (hgcd : (DensePoly.xgcdLeft a.polynomial a.inverseFactor.2).gcd =
      DensePoly.C c) (hc : c ≠ 0) :
    a.denote * a.inverseCandidate.denote = 1 := by
  let h := a.inverseFactor.2
  let eg := DensePoly.xgcdLeft a.polynomial h
  have hbezout := interpret_bezout ratCast ratZero ratSub ratMul ratDiv
    ratAdd ratOne a.polynomial h
  have hleft := DensePoly.xgcdLeft_left_eq_xgcd a.polynomial h
  have hg := DensePoly.xgcdLeft_gcd_eq_xgcd a.polynomial h
  have hp : (realPoly eg.left).eval d.real * a.denote = (c : ℝ) := by
    have he := congrArg (fun p : Polynomial ℝ => p.eval d.real) hbezout
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at he
    rw [← hleft, ← hg] at he
    change (realPoly eg.left).eval d.real * a.denote +
      (realPoly (DensePoly.xgcd a.polynomial h).right).eval d.real *
        (realPoly h).eval d.real = (realPoly eg.gcd).eval d.real at he
    have hroot' : (realPoly h).eval d.real = 0 := hroot
    rw [hroot', mul_zero, add_zero] at he
    have hgcd' : eg.gcd = DensePoly.C c := hgcd
    rw [hgcd'] at he
    simpa [realPoly, interpret_C, ratCast] using he
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcandidate : a.inverseCandidate.denote =
      (c : ℝ)⁻¹ * (realPoly eg.left).eval d.real := by
    change (interpret ratCast ratZero
      (DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left)).eval d.real = _
    rw [interpret_scale ratCast ratZero ratMul]
    simp [realPoly, eg, h, hgcd, DensePoly.leadingCoeff_C, ratCast]
  rw [hcandidate]
  calc
    a.denote * ((c : ℝ)⁻¹ * (realPoly eg.left).eval d.real) =
        (c : ℝ)⁻¹ * ((realPoly eg.left).eval d.real * a.denote) := by ring
    _ = 1 := by rw [hp]; field_simp

/-- A checked split places the original selected root in its cofactor. -/
theorem cofactor_root {context version : Nat} {d : Root context}
    (a : Expression d) {lower upper : Endpoint Rat}
    (r : Refinement d a.inverseFactor.2 lower upper version) :
    (realPoly a.inverseFactor.2).eval d.real = 0 := by
  have hhead := r.encoding.check_eq.1.1
  have hspec := (Root.real_spec r.encoding.target).1
  have hne : realPoly r.encoding.target.raw.head ≠ 0 :=
    r.encoding.target.head_ne_zero ratCast ratZero
  have hzero := (HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ hne _ _ _).mp hspec |>.1
  rw [hhead] at hzero
  have hroot : Root.real r.encoding.target = d.real :=
    r.encoding.root_eq_source ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign
  rw [hroot] at hzero
  exact hzero

/-- A nonzero selected value forces the selected root into the computed
cofactor, independently of whether re-encoding has run. -/
theorem cofactor_root_of_nonzero {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    (realPoly a.inverseFactor.2).eval d.real = 0 := by
  let p := d.raw.head
  let q := a.polynomial
  let g := DensePoly.monicize (DensePoly.gcd p q)
  have hq : q ≠ 0 := by
    intro h
    apply ha
    simp [denote, q, h, realPoly]
  have hgraw : DensePoly.gcd p q ≠ 0 := DensePoly.gcd_ne_zero_right p q hq
  have hgdvdq : g ∣ q :=
    DensePoly.monicize_dvd_of_dvd hgraw (DensePoly.gcd_dvd_right p q)
  have hgdvdp : g ∣ p :=
    DensePoly.monicize_dvd_of_dvd hgraw (DensePoly.gcd_dvd_left p q)
  obtain ⟨r, hr⟩ := hgdvdq
  have hgval : (realPoly g).eval d.real ≠ 0 := by
    intro hgzero
    apply ha
    have hqeval := congrArg (fun t : DensePoly Rat => (realPoly t).eval d.real) hr
    rw [realPoly_mul, Polynomial.eval_mul, hgzero, zero_mul] at hqeval
    exact hqeval
  have hrem : (DensePoly.divMod p g).2 = 0 :=
    DensePoly.mod_eq_zero_of_dvd p g hgdvdp
  have hrec := DensePoly.divMod_spec p g
  have hpeq : (DensePoly.divMod p g).1 * g = p := by
    simpa [hrem] using hrec
  have hpeval := congrArg (fun t : DensePoly Rat => (realPoly t).eval d.real) hpeq
  rw [realPoly_mul, Polynomial.eval_mul] at hpeval
  have hpzero : (realPoly p).eval d.real = 0 := by
    simpa [p] using denote_head (d := d)
  rw [hpzero] at hpeval
  have hh : (realPoly (DensePoly.divMod p g).1).eval d.real = 0 :=
    (mul_eq_zero.mp hpeval).resolve_right hgval
  simpa [inverseFactor, p, q, g] using hh

/-- Squarefreeness and the computed gcd make the cofactor squarefree and
coprime to the operand after interpretation. -/
theorem cofactor_laws {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    Squarefree (realPoly a.inverseFactor.2) ∧
      IsRelPrime (realPoly a.inverseFactor.2) (realPoly a.polynomial) := by
  let p := d.raw.head
  let q := a.polynomial
  let g := DensePoly.monicize (DensePoly.gcd p q)
  let h := (DensePoly.divMod p g).1
  have hq : q ≠ 0 := by
    intro hz
    apply ha
    simp [denote, q, hz, realPoly]
  have hgraw : DensePoly.gcd p q ≠ 0 := DensePoly.gcd_ne_zero_right p q hq
  have hgdvdp : g ∣ p :=
    DensePoly.monicize_dvd_of_dvd hgraw (DensePoly.gcd_dvd_left p q)
  have hrem : (DensePoly.divMod p g).2 = 0 :=
    DensePoly.mod_eq_zero_of_dvd p g hgdvdp
  have hfactor : p = h * g := by
    have hs := DensePoly.divMod_spec p g
    simpa [h, hrem] using hs.symm
  have hreal : realPoly p = realPoly h * realPoly g := by
    rw [hfactor, realPoly_mul]
  have hsq : Squarefree (realPoly h * realPoly g) := by
    rw [← hreal]
    exact d.real_squarefree
  have hrel : IsRelPrime (realPoly h) (realPoly g) :=
    IsRelPrime.of_squarefree_mul hsq
  obtain ⟨s, t, hbez⟩ := DensePoly.bezout_monicize_gcd p q
  have hbezreal : realPoly g = realPoly s * realPoly p + realPoly t * realPoly q := by
    have hb := congrArg realPoly hbez
    simpa [g, realPoly_add, realPoly_mul] using hb.symm
  have hc : IsRelPrime (realPoly h) (realPoly q) := by
    intro z hz_h hz_q
    have hz_p : z ∣ realPoly p := by
      rw [hreal]
      exact dvd_mul_of_dvd_left hz_h _
    have hz_g : z ∣ realPoly g := by
      rw [hbezreal]
      exact dvd_add (dvd_mul_of_dvd_right hz_p _) (dvd_mul_of_dvd_right hz_q _)
    exact hrel hz_h hz_g
  exact ⟨hsq.of_mul_left, hc⟩

theorem cofactor_squarefree {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    Squarefree (realPoly a.inverseFactor.2) := (cofactor_laws a ha).1

theorem cofactor_coprime {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    IsRelPrime (realPoly a.inverseFactor.2) (realPoly a.polynomial) :=
  (cofactor_laws a ha).2

/-- The actual one-sided extended gcd of a nonzero selected value and its
cofactor is a nonzero constant. -/
theorem cofactor_xgcd_constant {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    ∃ c : Rat, c ≠ 0 ∧
      (DensePoly.xgcdLeft a.polynomial a.inverseFactor.2).gcd = DensePoly.C c := by
  let q := a.polynomial
  let h := a.inverseFactor.2
  let eg := DensePoly.xgcdLeft q h
  have hcoprime := cofactor_coprime a ha
  have hunit : IsUnit (EuclideanDomain.gcd (realPoly q) (realPoly h)) :=
    EuclideanDomain.gcd_isUnit_iff.mpr hcoprime.symm.isCoprime
  have hge : eg.gcd = DensePoly.gcd q h :=
    (DensePoly.xgcdLeft_gcd_eq_xgcd q h).trans
      (DensePoly.xgcd_gcd_eq_gcd q h)
  have hassoc : Associated (realPoly eg.gcd)
      (EuclideanDomain.gcd (realPoly q) (realPoly h)) := by
    simpa [realPoly, hge] using
      (interpret_gcd ratCast ratZero ratSub ratMul ratDiv q h)
  have hunit' : IsUnit (realPoly eg.gcd) := hassoc.isUnit_iff.mpr hunit
  have hne : eg.gcd ≠ 0 := by
    intro hz
    have hz' : realPoly eg.gcd = 0 := by simp [hz, realPoly]
    exact hunit'.ne_zero hz'
  have hdeg : eg.gcd.natDegree = 0 := by
    have hr := Polynomial.natDegree_eq_zero_of_isUnit hunit'
    simpa [realPoly, natDegree_interpret] using hr
  have hsize : eg.gcd.size = 1 := by
    have hpos : 0 < eg.gcd.size := Nat.pos_of_ne_zero (by
      intro hz
      exact hne ((DensePoly.size_eq_zero_iff eg.gcd).mp hz))
    have hd := DensePoly.natDegree_eq_size_sub_one eg.gcd
    omega
  refine ⟨eg.gcd.leadingCoeff, DensePoly.leadingCoeff_ne_zero hne, ?_⟩
  exact DensePoly.eq_C_leadingCoeff_of_size_one hsize

/-- With a checked cofactor split and constant extended gcd, the candidate
is an inverse at the original selected root. -/
theorem candidate_mul_eq_one_of_split {context version : Nat} {d : Root context}
    (a : Expression d) {lower upper : Endpoint Rat}
    (r : Refinement d a.inverseFactor.2 lower upper version) (c : Rat)
    (hgcd : (DensePoly.xgcdLeft a.polynomial a.inverseFactor.2).gcd =
      DensePoly.C c) (hc : c ≠ 0) :
    a.denote * a.inverseCandidate.denote = 1 :=
  candidate_mul_eq_one a c (cofactor_root a r) hgcd hc

/-- The actual scaled Bézout candidate inverts every nonzero selected value. -/
theorem candidate_mul_eq_one_of_nonzero {context : Nat} {d : Root context}
    (a : Expression d) (ha : a.denote ≠ 0) :
    a.denote * a.inverseCandidate.denote = 1 := by
  obtain ⟨c, hc, hgcd⟩ := cofactor_xgcd_constant a ha
  exact candidate_mul_eq_one a c (cofactor_root_of_nonzero a ha) hgcd hc

/-- A returned sign for the candidate product must be zero after a nonzero
operand sign. -/
theorem candidate_check_zero {context : Nat} {d : Root context}
    (a : Expression d) (sa sc : Int)
    (hs : a.sign? = .ok sa) (hne : sa ≠ 0)
    (hc : (sub (mul a a.inverseCandidate) one).sign? = .ok sc) : sc = 0 := by
  have hsound := a.sign?_sound sa hs
  have ha : a.denote ≠ 0 := by
    intro hz
    apply hne
    simpa [hz] using hsound
  have hprod := candidate_mul_eq_one_of_nonzero a ha
  have hdiff : (sub (mul a a.inverseCandidate) one).denote = 0 := by
    simp [hprod]
  have hsc := (sub (mul a a.inverseCandidate) one).sign?_sound sc hc
  simpa [hdiff] using hsc

/-- Once both producer calls return, nonzero inversion cannot fail its
candidate check. -/
theorem inverse?_of_signs {context : Nat} {d : Root context}
    (a : Expression d) (sa sc : Int)
    (hs : a.sign? = .ok sa) (hne : sa ≠ 0)
    (hc : (sub (mul a a.inverseCandidate) one).sign? = .ok sc) :
    a.inverse? = .ok (some a.inverseCandidate) := by
  have hsc := candidate_check_zero a sa sc hs hne hc
  simp [inverse?, hs, hne, hc, hsc]

/-- A successful `none` result means the operand is zero at the selected root. -/
theorem inverse?_none_denote {context : Nat} {d : Root context} (a : Expression d)
    (h : a.inverse? = .ok none) : a.denote = 0 := by
  cases hs : a.sign? with
  | error err => simp [inverse?, hs] at h
  | ok sa =>
    by_cases hz : sa = 0
    · exact sign?_zero a (by simpa [hz] using hs)
    · cases hc : (sub (mul a a.inverseCandidate) one).sign? with
      | error err => simp [inverse?, hs, hz, hc] at h
      | ok sc =>
        by_cases hsc : sc = 0
        · simp [inverse?, hs, hz, hc, hsc] at h
        · simp [inverse?, hs, hz, hc, hsc] at h

/-- Checked re-encoding changes the defining polynomial without changing the
real value of an expression. -/
theorem denote_transport {context : Nat} {d : Root context} {head : DensePoly Rat}
    {lower upper : Endpoint Rat} (r : SignDet.Reencoding d head lower upper)
    (a : Expression d) : (transport r a).denote = a.denote := by
  have hroot := r.root_eq_source ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign
  simpa [denote, transport, Root.real] using
    congrArg (fun x : ℝ => (realPoly a.polynomial).eval x) hroot

/-- Checked rebinding preserves every rational polynomial expression's value. -/
theorem denote_rebind {context version : Nat} {d : Root context}
    (r : Rebinding d version) (a : Expression d) :
    (rebind r a).denote = a.denote := by
  simpa [denote, rebind] using
    congrArg (fun x : ℝ => (realPoly a.polynomial).eval x)
      r.real_eq_source

/-- A checked factor split and context change preserve stored values. -/
theorem denote_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Expression d) :
    (refine r a).denote = a.denote := by
  exact (denote_rebind r.binding (transport r.encoding a)).trans
    (denote_transport r.encoding a)

/-- Checked splitting and rebinding preserve a selected inverse result. -/
theorem inverse_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a b : Expression d)
    (h : a.inverse? = .ok (some b)) :
    (refine r a).denote * (refine r b).denote = 1 := by
  rw [denote_refine, denote_refine]
  exact inverse?_sound a b h

/-- The computed inverse candidate remains an inverse after a checked
cofactor split and context change. -/
theorem candidate_refine {context version : Nat} {d : Root context}
    (a : Expression d) {lower upper : Endpoint Rat}
    (r : Refinement d a.inverseFactor.2 lower upper version)
    (ha : a.denote ≠ 0) :
    (refine r a).denote * (refine r a.inverseCandidate).denote = 1 := by
  rw [denote_refine, denote_refine]
  exact candidate_mul_eq_one_of_nonzero a ha

/-- Successful sign queries agree before and after checked refinement. -/
theorem sign_refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Expression d)
    (oldSign newSign : Int)
    (hOld : a.sign? = .ok oldSign)
    (hNew : (refine r a).sign? = .ok newSign) :
    oldSign = newSign := by
  rw [a.sign?_sound oldSign hOld,
    (refine r a).sign?_sound newSign hNew, denote_refine]

end Expression
end Hex.RealClosure

/- The inherited `sorryAx` is `HexRealRootsMathlib.Tarski.check_rootSum` (#10389). -/
/-- info: 'Hex.RealClosure.Expression.inverse?_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.inverse?_sound
/-- info: 'Hex.RealClosure.Expression.denote_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.denote_transport
/-- info: 'Hex.RealClosure.Expression.denote_rebind' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.denote_rebind
/-- info: 'Hex.RealClosure.Expression.candidate_mul_eq_one_of_split' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.candidate_mul_eq_one_of_split
/-- info: 'Hex.RealClosure.Expression.candidate_mul_eq_one_of_nonzero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.candidate_mul_eq_one_of_nonzero
