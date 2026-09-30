/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Algebraic
public import HexSignDetMathlib.QueryHandle
public import HexPolyMathlib.Interpret

public section

namespace Hex.RealClosure.Algebraic

open HexPolyMathlib HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))

/-- The root selected by the actual shared descriptor in the supplied ambient
real closed field. This interpretation is never a core constructor argument. -/
@[expose] noncomputable def Context.rootValue (context : Context E Ctx coeffSign parent) : K :=
  context.root.root f hz h1 ha hs hm hnat hsign

@[expose] noncomputable def Context.evalPoly (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : K :=
  (interpret f hz p).eval (context.rootValue f hz h1 ha hs hm hnat hsign)

variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hsign hn hi in
/-- Native construction retains a prepared query domain whenever the actual
coefficient operations have the supplied lawful interpretation. -/
theorem Context.handle_success (context : Context E Ctx coeffSign parent) :
    ∃ handle : SignDet.QueryHandle context.root, context.handle = some handle := by
  rw [context.handle_checked]
  exact context.root.prepareQueries_success f hz h1 ha hs hm hnat hsign hn hi

include hz h1 ha hs hm hnat hsign hn hi in
/-- The original selected-sign producer cannot return an error under the
predecessor interpretation. `Context.buildSigns_eq` transfers this result to
the retained-domain adapter used by scalar arithmetic. -/
theorem Context.buildSigns_ne_error (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (error : SignDet.BuildError) :
    context.root.buildSigns [p] ≠ .error error := by
  obtain ⟨signs, h⟩ := context.root.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi [p]
  rw [h]
  intro he
  cases he

theorem Context.evalPoly_const (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (hsize : p.size ≤ 1) :
    context.evalPoly f hz h1 ha hs hm hnat hsign p = f (p.coeff 0) := by
  have hp : p = DensePoly.C (p.coeff 0) := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_C]
    split
    · rename_i hi
      subst i
      rfl
    · exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
  calc
    _ = context.evalPoly f hz h1 ha hs hm hnat hsign (DensePoly.C (p.coeff 0)) :=
      congrArg (context.evalPoly f hz h1 ha hs hm hnat hsign) hp
    _ = f (p.coeff 0) := by simp only [evalPoly, interpret_C, Polynomial.eval_C]

include hn hi in
theorem Context.signPoly_spec (context : Context E Ctx coeffSign parent) (p : DensePoly E) :
    context.signPoly p =
      (SignType.sign (context.evalPoly f hz h1 ha hs hm hnat hsign p) : Int) := by
  by_cases hsize : p.size ≤ 1
  · rw [context.signPoly_const p hsize,
      context.evalPoly_const f hz h1 ha hs hm hnat hsign p hsize]
    exact hsign (p.coeff 0)
  · obtain ⟨signs, h⟩ := context.root.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi [p]
    rw [context.signPoly_of_success p signs h (by omega)]
    exact signs.value_at_root f hz h1 ha hs hm hnat hsign

theorem Context.evalPoly_head (context : Context E Ctx coeffSign parent) :
    context.evalPoly f hz h1 ha hs hm hnat hsign context.root.raw.head = 0 := by
  have hr := (context.root.root_spec f hz h1 ha hs hm hnat hsign).1
  exact ((Tarski.mem_rootsIn_iff _ (context.root.head_ne_zero f hz) _ _ _).mp hr).1

theorem Context.evalPoly_reduce (context : Context E Ctx coeffSign parent) (p : DensePoly E) :
    context.evalPoly f hz h1 ha hs hm hnat hsign (context.reduce p) =
      context.evalPoly f hz h1 ha hs hm hnat hsign p := by
  unfold Context.reduce
  split
  · rename_i hreduce
    have hmonic := context.monic_of_reduce hreduce
    unfold evalPoly
    have hr := congrArg Prod.snd
      (interpret_divModMonic f hz hs hm h1 p context.root.raw.head hmonic)
    dsimp only at hr
    rw [hr]
    have he := congrArg
      (fun q : Polynomial K => q.eval (context.rootValue f hz h1 ha hs hm hnat hsign))
      (EuclideanDomain.div_add_mod (interpret f hz p) (interpret f hz context.root.raw.head))
    have hzero := context.evalPoly_head f hz h1 ha hs hm hnat hsign
    change (interpret f hz context.root.raw.head).eval
      (context.rootValue f hz h1 ha hs hm hnat hsign) = 0 at hzero
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      hzero, zero_mul, zero_add] using he
  · rfl

theorem Context.evalPoly_zero (context : Context E Ctx coeffSign parent) :
    context.evalPoly f hz h1 ha hs hm hnat hsign 0 = 0 := by
  simp [evalPoly]

include h1 ha hs hm hnat hsign in
theorem Context.head_squarefree (context : Context E Ctx coeffSign parent) :
    Squarefree (interpret f hz context.root.raw.head) := by
  obtain ⟨_, _, hc, _⟩ := SignDet.RawDescriptor.check_eq context.root.accepted
  exact (context.root.evidence.check_domain f hz h1 ha hs hm hnat coeffSign hsign
    parent context.root.raw.head context.root.raw.lower context.root.raw.upper
      context.root.raw.queries hc).2.1

namespace Element

variable {context : Context E Ctx coeffSign parent}

/-- Evaluate the stored representative at the descriptor's selected root. -/
@[expose] noncomputable def denote (a : Element context) : K :=
  context.evalPoly f hz h1 ha hs hm hnat hsign a.polynomial

@[simp] theorem denote_zero : denote f hz h1 ha hs hm hnat hsign (0 : Element context) = 0 := by
  rw [denote, polynomial_zero]
  exact context.evalPoly_zero f hz h1 ha hs hm hnat hsign

include hn hi in
/-- The cached sign belongs to the actual selected value. -/
theorem sign_spec (a : Element context) :
    a.sign = (SignType.sign (a.denote f hz h1 ha hs hm hnat hsign) : Int) := by
  cases h : a.stored with
  | none =>
    simp only [sign, polynomial, denote, h]
    rw [context.evalPoly_zero f hz h1 ha hs hm hnat hsign]
    simp only [_root_.sign_zero, SignType.coe_zero]
  | some p =>
    simp only [sign, polynomial, denote, h]
    rw [← p.checked]
    exact context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi p.polynomial

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem int_sign_zero (x : K) : (SignType.sign x : Int) = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply sign_eq_zero_iff.mp
    cases hx : SignType.sign x <;> simp_all
  · intro h
    subst x
    simp only [_root_.sign_zero, SignType.coe_zero]

include hn hi in
/-- Zero is canonical even though nonzero representatives need not be. -/
theorem denote_eq_zero (a : Element context) :
    a.denote f hz h1 ha hs hm hnat hsign = 0 ↔ a = 0 := by
  rw [← int_sign_zero, ← a.sign_spec f hz h1 ha hs hm hnat hsign hn hi]
  exact a.sign_eq_zero

include hn hi in
/-- Packing performs a sign query and may retain a monic remainder; neither
branch changes the selected value. -/
theorem denote_ofPoly (p : DensePoly E) :
    (ofPoly (context := context) p).denote f hz h1 ha hs hm hnat hsign =
      context.evalPoly f hz h1 ha hs hm hnat hsign p := by
  unfold denote polynomial
  rw [stored_ofPoly]
  by_cases hzero : context.signPoly (context.reduce p) = 0
  · simp only [hzero, ↓reduceDIte]
    have hv : context.evalPoly f hz h1 ha hs hm hnat hsign (context.reduce p) = 0 := by
      apply (int_sign_zero _).mp
      rw [← context.signPoly_spec f hz h1 ha hs hm hnat hsign hn hi]
      exact hzero
    rw [context.evalPoly_zero f hz h1 ha hs hm hnat hsign,
      ← context.evalPoly_reduce f hz h1 ha hs hm hnat hsign p, hv]
  · simp only [hzero, ↓reduceDIte]
    exact context.evalPoly_reduce f hz h1 ha hs hm hnat hsign p

include hn hi in
theorem denote_add (a b : Element context) :
    (a + b).denote f hz h1 ha hs hm hnat hsign =
      a.denote f hz h1 ha hs hm hnat hsign + b.denote f hz h1 ha hs hm hnat hsign := by
  change (ofPoly (context := context) _).denote f hz h1 ha hs hm hnat hsign = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [denote, Context.evalPoly, interpret_add f hz ha, Polynomial.eval_add]

include hn hi in
theorem denote_sub (a b : Element context) :
    (a - b).denote f hz h1 ha hs hm hnat hsign =
      a.denote f hz h1 ha hs hm hnat hsign - b.denote f hz h1 ha hs hm hnat hsign := by
  change (ofPoly (context := context) _).denote f hz h1 ha hs hm hnat hsign = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [denote, Context.evalPoly, interpret_sub f hz hs, Polynomial.eval_sub]

include hn hi in
theorem denote_neg (a : Element context) :
    (-a).denote f hz h1 ha hs hm hnat hsign =
      -(a.denote f hz h1 ha hs hm hnat hsign) := by
  change (ofPoly (context := context) (0 - a.polynomial)).denote f hz h1 ha hs hm hnat hsign = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [denote, Context.evalPoly, interpret_sub f hz hs, interpret_zero,
    zero_sub, Polynomial.eval_neg]

include hn hi in
theorem denote_mul (a b : Element context) :
    (a * b).denote f hz h1 ha hs hm hnat hsign =
      a.denote f hz h1 ha hs hm hnat hsign * b.denote f hz h1 ha hs hm hnat hsign := by
  change (ofPoly (context := context) _).denote f hz h1 ha hs hm hnat hsign = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [denote, Context.evalPoly, interpret_mul f hz ha hm, Polynomial.eval_mul]

include hn hi in
theorem denote_one : (1 : Element context).denote f hz h1 ha hs hm hnat hsign = 1 := by
  change (ofPoly 1).denote _ _ _ _ _ _ _ _ = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [Context.evalPoly, interpret_one f hz h1, Polynomial.eval_one]

include hn hi in
theorem denote_nat (n : Nat) :
    (n : Element context).denote f hz h1 ha hs hm hnat hsign = (n : K) := by
  change (ofPoly (DensePoly.C (n : E))).denote _ _ _ _ _ _ _ _ = _
  rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [Context.evalPoly, interpret_C, Polynomial.eval_C, hnat]

include hn hi in
theorem equal_spec (a b : Element context) : a.equal b = true ↔
    a.denote f hz h1 ha hs hm hnat hsign = b.denote f hz h1 ha hs hm hnat hsign := by
  rw [equal, decide_eq_true_eq, sign_spec f hz h1 ha hs hm hnat hsign hn hi,
    int_sign_zero, denote_sub f hz h1 ha hs hm hnat hsign hn hi, sub_eq_zero]

include hn hi in
theorem denote_ofCoeff (c : E) :
    (ofCoeff (context := context) c).denote f hz h1 ha hs hm hnat hsign = f c := by
  rw [ofCoeff, denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
  simp only [Context.evalPoly, interpret_C, Polynomial.eval_C]

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem int_sign_neg (x : K) : (SignType.sign x : Int) < 0 ↔ x < 0 := by
  rw [← (sign_eq_neg_one_iff (a := x))]
  cases SignType.sign x <;> decide

include hn hi in
/-- Comparison uses the same selected values as arithmetic and semantic equality. -/
theorem compare_spec (a b : Element context) :
    a.compare b =
      if a.denote f hz h1 ha hs hm hnat hsign < b.denote f hz h1 ha hs hm hnat hsign then .lt
      else if a.denote f hz h1 ha hs hm hnat hsign = b.denote f hz h1 ha hs hm hnat hsign
        then .eq else .gt := by
  simp only [compare, sign_spec f hz h1 ha hs hm hnat hsign hn hi,
    denote_sub f hz h1 ha hs hm hnat hsign hn hi, int_sign_neg, int_sign_zero,
    sub_neg, sub_eq_zero]

variable (hd : ∀ a b, f (a / b) = f a / f b)

omit [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
include hs hm hi hd in
/-- The computed complementary factor transfers through a zero-reflecting
coefficient interpretation, without injectivity or field laws on storage. -/
theorem cofactor_map (a : Element context) :
    DensePoly.Interpret.map f hz a.inverseFactor.2 =
      (DensePoly.divMod (DensePoly.Interpret.map f hz context.root.raw.head)
        (DensePoly.monicize (DensePoly.gcd
          (DensePoly.Interpret.map f hz context.root.raw.head)
          (DensePoly.Interpret.map f hz a.polynomial)))).1 := by
  simp only [inverseFactor]
  have h := congrArg Prod.fst (DensePoly.Interpret.map_divMod f hz hs hm hd
    context.root.raw.head (DensePoly.monicize
      (DensePoly.gcd context.root.raw.head a.polynomial)))
  dsimp only at h
  rw [h, DensePoly.Interpret.map_monicize f hz hm hi,
    DensePoly.Interpret.map_gcd f hz hs hm hd]

set_option maxHeartbeats 800000 in
include hi hd in
/-- The actual gcd split keeps the selected root in the complementary factor,
which is squarefree and relatively prime to the nonzero operand. -/
theorem cofactor_spec (a : Element context)
    (hne : a.denote f hz h1 ha hs hm hnat hsign ≠ 0) :
    context.evalPoly f hz h1 ha hs hm hnat hsign a.inverseFactor.2 = 0 ∧
      Squarefree (interpret f hz a.inverseFactor.2) ∧
        IsRelPrime (interpret f hz a.inverseFactor.2) (interpret f hz a.polynomial) := by
  let p := DensePoly.Interpret.map f hz context.root.raw.head
  let q := DensePoly.Interpret.map f hz a.polynomial
  let g := DensePoly.monicize (DensePoly.gcd p q)
  let h := (DensePoly.divMod p g).1
  let x := context.rootValue f hz h1 ha hs hm hnat hsign
  have hpzero : (toPolynomial p).eval x = 0 := by
    have he := context.evalPoly_head f hz h1 ha hs hm hnat hsign
    simpa only [Context.evalPoly, interpret_map] using he
  have hden : a.denote f hz h1 ha hs hm hnat hsign = (toPolynomial q).eval x := by
    simp only [denote, Context.evalPoly, interpret_map]
    rfl
  rw [hden] at hne
  have hq : q ≠ 0 := by
    intro hzero
    apply hne
    rw [hzero, toPolynomial_zero, Polynomial.eval_zero]
  have hgraw : DensePoly.gcd p q ≠ 0 := DensePoly.gcd_ne_zero_right p q hq
  have hgdvdp : g ∣ p :=
    DensePoly.monicize_dvd_of_dvd hgraw (DensePoly.gcd_dvd_left p q)
  have hgdvdq : g ∣ q :=
    DensePoly.monicize_dvd_of_dvd hgraw (DensePoly.gcd_dvd_right p q)
  have hrem : (DensePoly.divMod p g).2 = 0 := DensePoly.mod_eq_zero_of_dvd p g hgdvdp
  have hfactor : p = h * g := by
    have hc := DensePoly.divMod_spec p g
    simpa only [h, hrem, DensePoly.add_zero_semiring] using hc.symm
  have hpoly : toPolynomial p = toPolynomial h * toPolynomial g := by
    rw [hfactor, toPolynomial_mul]
  have hgval : (toPolynomial g).eval x ≠ 0 := by
    intro hgzero
    obtain ⟨r, hr⟩ := hgdvdq
    apply hne
    rw [hr, toPolynomial_mul, Polynomial.eval_mul, hgzero, zero_mul]
  have hhzero : (toPolynomial h).eval x = 0 := by
    have he := congrArg (fun t : Polynomial K => t.eval x) hpoly
    rw [Polynomial.eval_mul, hpzero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hgval
  have hsq : Squarefree (toPolynomial h * toPolynomial g) := by
    rw [← hpoly]
    simpa only [interpret_map] using context.head_squarefree f hz h1 ha hs hm hnat hsign
  have hrel : IsRelPrime (toPolynomial h) (toPolynomial g) :=
    IsRelPrime.of_squarefree_mul hsq
  obtain ⟨s, t, hbez⟩ := DensePoly.bezout_monicize_gcd p q
  have hb : toPolynomial g = toPolynomial s * toPolynomial p +
      toPolynomial t * toPolynomial q := by
    have he := congrArg toPolynomial hbez
    simpa only [toPolynomial_add, toPolynomial_mul] using he.symm
  have hcoprime : IsRelPrime (toPolynomial h) (toPolynomial q) := by
    intro z hz_h hz_q
    have hz_p : z ∣ toPolynomial p := by
      rw [hpoly]
      exact dvd_mul_of_dvd_left hz_h _
    have hz_g : z ∣ toPolynomial g := by
      rw [hb]
      exact dvd_add (dvd_mul_of_dvd_right hz_p _) (dvd_mul_of_dvd_right hz_q _)
    exact hrel hz_h hz_g
  have hh : interpret f hz a.inverseFactor.2 = toPolynomial h := by
    rw [interpret_map, a.cofactor_map f hz hs hm hi hd]
  rw [Context.evalPoly, hh, interpret_map]
  exact ⟨hhzero, hsq.of_mul_left, hcoprime⟩

set_option maxHeartbeats 800000 in
include hi hd in
/-- The one-sided extended gcd returned for the complementary factor is an
actual nonzero constant polynomial over the stored predecessor coefficients. -/
theorem cofactor_constant (a : Element context)
    (hne : a.denote f hz h1 ha hs hm hnat hsign ≠ 0) :
    ∃ c : E, c ≠ 0 ∧
      (DensePoly.xgcdLeft a.polynomial a.inverseFactor.2).gcd = DensePoly.C c := by
  let q := a.polynomial
  let h := a.inverseFactor.2
  let eg := DensePoly.xgcdLeft q h
  have hcoprime := (a.cofactor_spec f hz h1 ha hs hm hnat hsign hi hd hne).2.2
  have hunit : IsUnit (EuclideanDomain.gcd (interpret f hz q) (interpret f hz h)) :=
    EuclideanDomain.gcd_isUnit_iff.mpr hcoprime.symm.isCoprime
  have hge : eg.gcd = DensePoly.gcd q h :=
    (DensePoly.xgcdLeft_gcd_eq_xgcd q h).trans (DensePoly.xgcd_gcd_eq_gcd q h)
  have hassoc : Associated (interpret f hz eg.gcd)
      (EuclideanDomain.gcd (interpret f hz q) (interpret f hz h)) := by
    rw [hge]
    exact interpret_gcd f hz hs hm hd q h
  have hunit' : IsUnit (interpret f hz eg.gcd) := hassoc.isUnit_iff.mpr hunit
  have heg : eg.gcd ≠ 0 := by
    intro hzero
    exact hunit'.ne_zero ((interpret_eq_zero f hz eg.gcd).mpr hzero)
  have hdeg : eg.gcd.natDegree = 0 := by
    have hr := Polynomial.natDegree_eq_zero_of_isUnit hunit'
    simpa only [natDegree_interpret] using hr
  have hsize : eg.gcd.size = 1 := by
    have hpos : 0 < eg.gcd.size := Nat.pos_of_ne_zero (by
      intro hzsize
      exact heg ((DensePoly.size_eq_zero_iff eg.gcd).mp hzsize))
    have hdsize := DensePoly.natDegree_eq_size_sub_one eg.gcd
    omega
  exact ⟨eg.gcd.leadingCoeff, DensePoly.leadingCoeff_ne_zero_of_pos_size eg.gcd (by omega),
    DensePoly.eq_C_leadingCoeff_of_size_one hsize⟩

set_option maxHeartbeats 800000 in
include hi hd in
/-- The exact scaled Bézout coefficient computed by inversion is the inverse
at the selected root; no successful split or constant gcd is assumed. -/
theorem candidate_spec (a : Element context)
    (hne : a.denote f hz h1 ha hs hm hnat hsign ≠ 0) :
    context.evalPoly f hz h1 ha hs hm hnat hsign a.inverseCandidate =
      (a.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by
  obtain ⟨c, hc, hgcd⟩ := a.cofactor_constant f hz h1 ha hs hm hnat hsign hi hd hne
  let h := a.inverseFactor.2
  let eg := DensePoly.xgcdLeft a.polynomial h
  let x := context.rootValue f hz h1 ha hs hm hnat hsign
  have hroot := (a.cofactor_spec f hz h1 ha hs hm hnat hsign hi hd hne).1
  have he := congrArg (fun p : Polynomial K => p.eval x)
    (interpret_bezout f hz hs hm hd ha h1 a.polynomial h)
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at he
  rw [← DensePoly.xgcdLeft_left_eq_xgcd a.polynomial h,
    ← DensePoly.xgcdLeft_gcd_eq_xgcd a.polynomial h] at he
  have hp : (interpret f hz eg.left).eval x * a.denote f hz h1 ha hs hm hnat hsign = f c := by
    change (interpret f hz eg.left).eval x * a.denote f hz h1 ha hs hm hnat hsign +
      (interpret f hz (DensePoly.xgcd a.polynomial h).right).eval x *
        context.evalPoly f hz h1 ha hs hm hnat hsign h = (interpret f hz eg.gcd).eval x at he
    rw [hroot, mul_zero, add_zero, hgcd, interpret_C, Polynomial.eval_C] at he
    exact he
  have hc' : f c ≠ 0 := fun hzero => hc ((hz c).mp hzero)
  have hcand : context.evalPoly f hz h1 ha hs hm hnat hsign a.inverseCandidate =
      (f c)⁻¹ * (interpret f hz eg.left).eval x := by
    change (interpret f hz (DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left)).eval x = _
    rw [interpret_scale f hz hm, Polynomial.eval_mul, Polynomial.eval_C,
      hi, hgcd, DensePoly.leadingCoeff_C]
  have hprod : a.denote f hz h1 ha hs hm hnat hsign *
      context.evalPoly f hz h1 ha hs hm hnat hsign a.inverseCandidate = 1 := by
    rw [hcand]
    calc
      _ = (f c)⁻¹ * ((interpret f hz eg.left).eval x *
          a.denote f hz h1 ha hs hm hnat hsign) := by ring
      _ = 1 := by rw [hp, inv_mul_cancel₀ hc']
  apply mul_left_cancel₀ hne
  rw [mul_inv_cancel₀ hne]
  exact hprod

include hn hi hd in
/-- Inversion is total, fixes canonical zero, and inverts every nonzero value. -/
theorem denote_inv (a : Element context) :
    (a⁻¹).denote f hz h1 ha hs hm hnat hsign =
      (a.denote f hz h1 ha hs hm hnat hsign)⁻¹ := by
  change (inv a).denote f hz h1 ha hs hm hnat hsign = _
  unfold inv
  cases h : a.stored with
  | none =>
    have ha0 : a = 0 := by apply ext; rw [stored_zero]; exact h
    rw [ha0, denote_zero, inv_zero]
  | some p =>
    rw [denote_ofPoly f hz h1 ha hs hm hnat hsign hn hi]
    apply candidate_spec f hz h1 ha hs hm hnat hsign hi hd a
    intro hzero
    have hsignzero : a.sign = 0 := by
      rw [a.sign_spec f hz h1 ha hs hm hnat hsign hn hi, hzero]
      simp only [_root_.sign_zero, SignType.coe_zero]
    exact p.nonzero (by simpa only [sign, h] using hsignzero)

include hn hi hd in
theorem denote_div (a b : Element context) :
    (a / b).denote f hz h1 ha hs hm hnat hsign =
      a.denote f hz h1 ha hs hm hnat hsign / b.denote f hz h1 ha hs hm hnat hsign := by
  change (a * b⁻¹).denote f hz h1 ha hs hm hnat hsign = _
  rw [denote_mul f hz h1 ha hs hm hnat hsign hn hi,
    denote_inv f hz h1 ha hs hm hnat hsign hn hi hd, div_eq_mul_inv]

end Element

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.buildSigns_ne_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.buildSigns_ne_error
/-- info: 'Hex.RealClosure.Algebraic.Element.denote_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.denote_eq_zero
/-- info: 'Hex.RealClosure.Algebraic.Element.denote_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.denote_inv
/-- info: 'Hex.RealClosure.Algebraic.Element.compare_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.compare_spec

/-- info: 'Hex.RealClosure.Algebraic.Context.handle_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.handle_success
