/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Chain
public import HexResultantMathlib.Sylvester

public section

/-!
Bivariate specialization laws for executable elimination.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

section DenseCommRing

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- The Mathlib ring structure induced by the executable dense-polynomial
operations. It remains proof-local: the public API deliberately does not
install a global `CommRing (DensePoly R)` instance. -/
@[implicit_reducible]
private noncomputable def denseCommRing [CommRing R] [DecidableEq R] :
    CommRing (DensePoly R) :=
  let s := (inferInstance : Lean.Grind.CommRing (DensePoly R))
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one,
        Lean.Grind.Semiring.natCast_succ] }

end DenseCommRing

/-- Evaluation carries an explicit-degree coefficient minor to the resultant
of the specialized inputs. This is the direct coefficient-map transfer; it
does not instantiate the executable resultant correspondence over
`DensePoly R`. -/
private theorem eval_coeffMinorAt_zero [CommRing R] [DecidableEq R]
    (df dg : Nat) (f g : DensePoly (DensePoly R)) (a : R)
    (hf : f.size ≤ df + 1) (hg : g.size ≤ dg + 1) :
    eval (Subresultant.coeffMinorAt df dg 0 0 f g) a =
      Polynomial.resultant (specialize f a) (specialize g a)
        (m := df) (n := dg) := by
  let _ : CommRing (DensePoly R) := denseCommRing
  let ε : DensePoly R →+* R :=
    (Polynomial.evalRingHom a).comp
      (HexPolyMathlib.equiv (R := R)).toRingHom
  have hε (p : DensePoly R) : ε p = eval p a := by
    change (HexPolyMathlib.toPolynomial p).eval a = eval p a
    exact (eval_toPolynomial p a).symm
  have hfMap :
      (HexPolyMathlib.toPolynomial f).map ε = specialize f a := by
    ext i
    rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
      coeff_specialize, hε]
  have hgMap :
      (HexPolyMathlib.toPolynomial g).map ε = specialize g a := by
    ext i
    rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
      coeff_specialize, hε]
  rw [← hε]
  have hminor :=
    Subresultant.coeffMinorAt_zero_eq_resultant df dg f g hf hg
  calc
    ε (Subresultant.coeffMinorAt df dg 0 0 f g) =
        ε (Polynomial.resultant (HexPolyMathlib.toPolynomial f)
          (HexPolyMathlib.toPolynomial g) df dg) := congrArg ε hminor
    _ = Polynomial.resultant (specialize f a) (specialize g a) df dg := by
      rw [← Polynomial.resultant_map_map, hfMap, hgMap]

/-- Specializing the coefficient variable after elimination agrees with the
formal-degree Mathlib resultant of the specialized inputs. -/
theorem eval_resultant [CommRing R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0) := by
  by_cases hf : f = 0
  · subst f
    have hz : (0 : DensePoly (DensePoly R)).isZero = true :=
      (isZero_eq_true_iff (0 : DensePoly (DensePoly R))).2 rfl
    have hzdeg : (0 : DensePoly (DensePoly R)).degree?.getD 0 = 0 := by
      simp
    by_cases hgsmall : g.size ≤ 1
    · have hgdeg : g.degree?.getD 0 = 0 := by
        by_cases hg : g = 0
        · subst g
          simp
        · have hgpos : 0 < g.size := by
            by_contra h
            apply hg
            exact (size_eq_zero_iff g).mp (by omega)
          rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
          omega
      unfold resultant
      rw [hz]
      simp only [↓reduceIte]
      rw [if_pos hgsmall, specialize_zero, hzdeg, hgdeg,
        eval_toPolynomial, HexPolyMathlib.toPolynomial_one]
      simp [Polynomial.resultant]
    · have hgdeg : 0 < g.degree?.getD 0 := by
        have hgpos : 0 < g.size := by omega
        rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
        omega
      unfold resultant
      rw [hz]
      simp only [↓reduceIte]
      rw [if_neg hgsmall, specialize_zero, hzdeg,
        eval_toPolynomial, HexPolyMathlib.toPolynomial_zero,
        Polynomial.eval_zero, Polynomial.resultant_zero_left]
      simp [hgdeg.ne']
  · by_cases hg : g = 0
    · subst g
      have hz : (0 : DensePoly (DensePoly R)).isZero = true :=
        (isZero_eq_true_iff (0 : DensePoly (DensePoly R))).2 rfl
      have hzdeg : (0 : DensePoly (DensePoly R)).degree?.getD 0 = 0 := by
        simp
      have hfpos : 0 < f.size := by
        by_contra h
        apply hf
        exact (size_eq_zero_iff f).mp (by omega)
      have hfz : f.isZero = false := (isZero_eq_false_iff f).2 hfpos
      by_cases hfsmall : f.size ≤ 1
      · have hfdeg : f.degree?.getD 0 = 0 := by
          rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
          omega
        unfold resultant
        rw [hfz, hz]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_pos hfsmall, specialize_zero, hzdeg, hfdeg,
          eval_toPolynomial, HexPolyMathlib.toPolynomial_one]
        simp [Polynomial.resultant]
      · have hfdeg : 0 < f.degree?.getD 0 := by
          rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
          omega
        unfold resultant
        rw [hfz, hz]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_neg hfsmall, specialize_zero, hzdeg,
          eval_toPolynomial, HexPolyMathlib.toPolynomial_zero,
          Polynomial.eval_zero, Polynomial.resultant_zero_right]
        simp [hfdeg.ne']
    · have hfpos : 0 < f.size := by
        by_contra h
        apply hf
        exact (size_eq_zero_iff f).mp (by omega)
      have hgpos : 0 < g.size := by
        by_contra h
        apply hg
        exact (size_eq_zero_iff g).mp (by omega)
      have hfz : f.isZero = false := (isZero_eq_false_iff f).2 hfpos
      have hgz : g.isZero = false := (isZero_eq_false_iff g).2 hgpos
      have hdf : f.degree?.getD 0 = Subresultant.formalDegree f := by
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
        rfl
      have hdg : g.degree?.getD 0 = Subresultant.formalDegree g := by
        rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
        rfl
      have hfBound : f.size ≤ Subresultant.formalDegree f + 1 := by
        unfold Subresultant.formalDegree
        omega
      have hgBound : g.size ≤ Subresultant.formalDegree g + 1 := by
        unfold Subresultant.formalDegree
        omega
      rw [hdf, hdg]
      unfold resultant
      simp only [hfz, hgz, Bool.false_eq_true, ↓reduceIte]
      by_cases hfg : f.size < g.size
      · rw [if_pos hfg]
        rw [resultantOrdered_eq_coeffMinor g f hg hf (by omega),
          negOnePow_eq_sign]
        have hswap := Subresultant.coeffMinor_swap 0 0 f g
        simp only [Nat.sub_zero, Subresultant.formalDegree] at hswap
        rw [← hswap]
        unfold Subresultant.coeffMinor
        exact eval_coeffMinorAt_zero _ _ f g a hfBound hgBound
      · rw [if_neg hfg]
        rw [resultantOrdered_eq_coeffMinor f g hf hg (by omega)]
        unfold Subresultant.coeffMinor
        exact eval_coeffMinorAt_zero _ _ f g a hfBound hgBound

/-- A nonvanishing specialized leading coefficient preserves the outer
degree under specialization. -/
private theorem natDegree_specialize [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R)
    (hf : eval f.leadingCoeff a ≠ 0) :
    (specialize f a).natDegree = f.degree?.getD 0 := by
  have hfpos : 0 < f.size := by
    by_contra h
    have hfzero : f = 0 := (size_eq_zero_iff f).mp (by omega)
    subst f
    rw [leadingCoeff_zero, eval_toPolynomial,
      HexPolyMathlib.toPolynomial_zero, Polynomial.eval_zero] at hf
    exact hf rfl
  rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_specialize]
    have hsize : f.size ≤ n := by omega
    rw [coeff_eq_zero_of_size_le f hsize]
    have heval : eval (Zero.zero : DensePoly R) a = (Zero.zero : R) := rfl
    rw [heval]
    exact ((Lean.Grind.Semiring.ofNat_eq_natCast (α := R) 0).trans
      Lean.Grind.Semiring.natCast_zero).symm
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_specialize]
    have hcoeff : f.coeff (f.size - 1) = f.leadingCoeff :=
      (leadingCoeff_eq_coeff_last f hfpos).symm
    rw [hcoeff]
    exact hf

/-- Specialization cannot increase the outer degree. -/
private theorem natDegree_specialize_le [CommRing R] [DecidableEq R]
    (f : DensePoly (DensePoly R)) (a : R) :
    (specialize f a).natDegree ≤ f.degree?.getD 0 := by
  by_cases hfsize : f.size = 0
  · have hf : f = 0 := (size_eq_zero_iff f).mp hfsize
    subst f
    simp
  · have hfpos : 0 < f.size := Nat.pos_of_ne_zero hfsize
    rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_specialize]
    have hsize : f.size ≤ n := by omega
    rw [coeff_eq_zero_of_size_le f hsize]
    have heval : eval (Zero.zero : DensePoly R) a = (Zero.zero : R) := rfl
    rw [heval]
    exact ((Lean.Grind.Semiring.ofNat_eq_natCast (α := R) 0).trans
      Lean.Grind.Semiring.natCast_zero).symm

/-- Over a domain, a common root makes the default-degree resultant vanish as
soon as at least one polynomial is nonzero. The proof maps injectively to the
fraction field and uses Mathlib's field criterion. -/
theorem resultant_eq_zero_of_common_eval
    [CommRing R] [IsDomain R]
    (F G : Polynomial R) (b : R)
    (hF : F.eval b = 0) (hG : G.eval b = 0)
    (hne : F ≠ 0 ∨ G ≠ 0) :
    Polynomial.resultant F G = 0 := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let FK := F.map φ
  let GK := G.map φ
  have hφ : Function.Injective φ :=
    FaithfulSMul.algebraMap_injective R K
  have hFKeval : FK.eval (φ b) = 0 := by
    simpa [FK, φ] using congrArg φ hF
  have hGKeval : GK.eval (φ b) = 0 := by
    simpa [GK, φ] using congrArg φ hG
  have hneMap : FK ≠ 0 ∨ GK ≠ 0 := by
    rcases hne with hFne | hGne
    · exact Or.inl ((Polynomial.map_ne_zero_iff hφ).2 hFne)
    · exact Or.inr ((Polynomial.map_ne_zero_iff hφ).2 hGne)
  have hnot : ¬IsCoprime FK GK := by
    intro hcop
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcop (φ b) with h | h
    · exact h (by simpa [Polynomial.aeval_def] using hFKeval)
    · exact h (by simpa [Polynomial.aeval_def] using hGKeval)
  have hmapres : Polynomial.resultant FK GK = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨hneMap, hnot⟩
  have hFKdeg : FK.natDegree = F.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ F
  have hGKdeg : GK.natDegree = G.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ G
  have hres : φ (Polynomial.resultant F G) = 0 := by
    rw [← Polynomial.resultant_map_map]
    simpa [FK, GK, hFKdeg, hGKdeg] using hmapres
  apply hφ
  simpa using hres

/-- The specialization law at default Mathlib degrees when neither outer
leading coefficient vanishes. -/
theorem eval_resultant_default
    [CommRing R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R)
    (hf : eval f.leadingCoeff a ≠ 0) (hg : eval g.leadingCoeff a ≠ 0) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a) := by
  rw [eval_resultant]
  rw [← natDegree_specialize f a hf, ← natDegree_specialize g a hg]

/-- A common bivariate zero forces the specialized eliminant to vanish when at
least one input genuinely has positive degree in the eliminated variable. The
condition excludes the formal-degree `(0, 0)` resultant, whose value is `1`. -/
theorem eval_resultant_eq_zero_of_common_root
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a b : R)
    (hpos : 1 < f.size ∨ 1 < g.size)
    (hfb : evalBivariate f a b = 0) (hgb : evalBivariate g a b = 0) :
    eval (resultant f g) a = 0 := by
  rw [eval_resultant]
  let F := specialize f a
  let G := specialize g a
  let m := f.degree?.getD 0
  let n := g.degree?.getD 0
  change Polynomial.resultant F G m n = 0
  have hFroot : F.eval b = 0 := by
    simpa only [F, evalBivariate] using hfb
  have hGroot : G.eval b = 0 := by
    simpa only [G, evalBivariate] using hgb
  have hm : F.natDegree ≤ m := by
    simpa only [F, m] using natDegree_specialize_le f a
  have hn : G.natDegree ≤ n := by
    simpa only [G, n] using natDegree_specialize_le g a
  have hmn : 0 < m ∨ 0 < n := by
    rcases hpos with hfpos | hgpos
    · left
      dsimp only [m]
      rw [degree?_eq_some_of_pos_size f (by omega), Option.getD_some]
      omega
    · right
      dsimp only [n]
      rw [degree?_eq_some_of_pos_size g (by omega), Option.getD_some]
      omega
  by_cases hboth : F = 0 ∧ G = 0
  · rcases hboth with ⟨hFzero, hGzero⟩
    rw [hFzero, hGzero, Polynomial.resultant_zero_zero]
    have hsum : m + n ≠ 0 := by omega
    exact zero_pow hsum
  · have hne : F ≠ 0 ∨ G ≠ 0 := by
      by_cases hFzero : F = 0
      · right
        intro hGzero
        exact hboth ⟨hFzero, hGzero⟩
      · exact Or.inl hFzero
    have hdefault :=
      resultant_eq_zero_of_common_eval F G b hFroot hGroot hne
    have hmEq : m = F.natDegree + (m - F.natDegree) := by omega
    have hnEq : n = G.natDegree + (n - G.natDegree) := by omega
    rw [hmEq, Polynomial.resultant_add_left_deg F G F.natDegree n
      (m - F.natDegree) le_rfl]
    rw [hnEq, Polynomial.resultant_add_right_deg F G F.natDegree
      G.natDegree (n - G.natDegree) le_rfl]
    rw [hdefault]
    ring

end Hex.DensePoly
