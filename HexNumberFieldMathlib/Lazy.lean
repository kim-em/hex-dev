/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Exact

public section

/-!
# Semantics of lazy and canonical arithmetic

Each checked lazy operation has a soundness theorem and a bounded-search
completeness theorem. These imply the corresponding theorem for the total
fallback wrapper, and exactification transfers it to canonical algebraic
numbers.
-/

namespace Hex

noncomputable section

@[implicit_reducible] local instance : CommRing ZPoly :=
  let s := (inferInstance : Lean.Grind.CommRing ZPoly)
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

local instance : IsDomain ZPoly :=
  MulEquiv.isDomain (Polynomial Int)
    (HexPolyMathlib.equiv (R := Int)).toMulEquiv

private noncomputable def evalZPoly (t : ℂ) : ZPoly →+* ℂ :=
  (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
    (HexPolyMathlib.equiv (R := Int)).toRingHom

private theorem ZPoly.map_liftOuter (p : ZPoly) (t : ℂ) :
    (HexPolyMathlib.toPolynomial p.liftOuter).map (evalZPoly t) =
      HexRootsMathlib.toPolyℂ p := by
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    ZPoly.coeff_liftOuter, HexRootsMathlib.coeff_toPolyℂ]
  change Polynomial.eval₂ (Int.castRingHom ℂ) t
      (HexPolyMathlib.toPolynomial (DensePoly.C (p.coeff n))) =
    (p.coeff n : ℂ)
  rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
  rfl

private theorem evalZPoly_X (t : ℂ) : evalZPoly t ZPoly.X = t := by
  simp [evalZPoly, ZPoly.X, HexPolyMathlib.equiv_apply,
    HexPolyMathlib.toPolynomial_monomial,
    Polynomial.monomial_one_one_eq_X]

private theorem resultant_eval_eq_zero_of_common_root
    (f g : DensePoly ZPoly) (t y : ℂ)
    (hpos : 1 < f.size ∨ 1 < g.size)
    (hf : ((HexPolyMathlib.toPolynomial f).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0)
    (hg : ((HexPolyMathlib.toPolynomial g).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0) :
    (HexRootsMathlib.toPolyℂ (DensePoly.resultant f g)).eval t = 0 := by
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  let F : Polynomial ℂ := (HexPolyMathlib.toPolynomial f).map ε
  let G : Polynomial ℂ := (HexPolyMathlib.toPolynomial g).map ε
  let m := f.degree?.getD 0
  let n := g.degree?.getD 0
  have hm : F.natDegree ≤ m := by
    calc
      F.natDegree ≤ (HexPolyMathlib.toPolynomial f).natDegree :=
        Polynomial.natDegree_map_le
      _ = m := by
        simp [m]
  have hn : G.natDegree ≤ n := by
    calc
      G.natDegree ≤ (HexPolyMathlib.toPolynomial g).natDegree :=
        Polynomial.natDegree_map_le
      _ = n := by
        simp [n]
  have hmn : 0 < m ∨ 0 < n := by
    rcases hpos with hfpos | hgpos
    · left
      dsimp only [m]
      rw [DensePoly.degree?_eq_some_of_pos_size f (by omega), Option.getD_some]
      omega
    · right
      dsimp only [n]
      rw [DensePoly.degree?_eq_some_of_pos_size g (by omega), Option.getD_some]
      omega
  have hresultant : Polynomial.resultant F G m n = 0 := by
    by_cases hboth : F = 0 ∧ G = 0
    · rcases hboth with ⟨hFzero, hGzero⟩
      rw [hFzero, hGzero, Polynomial.resultant_zero_zero]
      exact zero_pow (by omega)
    · have hne : F ≠ 0 ∨ G ≠ 0 := by
        by_cases hFzero : F = 0
        · right
          intro hGzero
          exact hboth ⟨hFzero, hGzero⟩
        · exact Or.inl hFzero
      have hdefault : Polynomial.resultant F G = 0 :=
        DensePoly.resultant_eq_zero_of_common_eval F G y
          (by simpa [F, ε] using hf) (by simpa [G, ε] using hg) hne
      have hmEq : m = F.natDegree + (m - F.natDegree) := by omega
      have hnEq : n = G.natDegree + (n - G.natDegree) := by omega
      rw [hmEq, Polynomial.resultant_add_left_deg F G F.natDegree n
        (m - F.natDegree) le_rfl]
      rw [hnEq, Polynomial.resultant_add_right_deg F G F.natDegree
        G.natDegree (n - G.natDegree) le_rfl]
      rw [hdefault]
      ring
  have hcorrespondence := congrArg ε
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have heval (q : ZPoly) :
      ε q = (HexRootsMathlib.toPolyℂ q).eval t := by
    simp [ε, HexRootsMathlib.toPolyℂ, Polynomial.eval_map]
  rw [← heval]
  rw [hcorrespondence]
  exact hresultant

private theorem ZPoly.addEliminant_isRoot (a b : AlgebraicRoot) :
    (HexRootsMathlib.toPolyℂ (ZPoly.addEliminant a.p b.p)).IsRoot
      (a.toComplex + b.toComplex) := by
  unfold ZPoly.addEliminant
  apply resultant_eval_eq_zero_of_common_root
      (y := a.toComplex)
  · left
    have hsize : 1 < a.p.size := by
      have hpos : 0 < a.p.size := by
        by_contra h
        have hzero : a.p = 0 :=
          (DensePoly.size_eq_zero_iff a.p).mp (by omega)
        have hdegree := a.pos_degree
        rw [hzero] at hdegree
        simp at hdegree
      have hdegree := a.pos_degree
      rw [DensePoly.degree?_eq_some_of_pos_size a.p hpos,
        Option.getD_some] at hdegree
      omega
    have hcoeff :
        a.p.liftOuter.coeff (a.p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun p : ZPoly => p.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size a.p (by omega) hconst
    have hlt : a.p.size - 1 < a.p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega
  · change ((HexPolyMathlib.toPolynomial a.p.liftOuter).map
      (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex = 0
    rw [ZPoly.map_liftOuter]
    exact AlgebraicRoot.toComplex_isRoot a
  · change (((HexPolyMathlib.toPolynomial
      (DensePoly.compose b.p.liftOuter
        (DensePoly.C ZPoly.X - DensePoly.monomial 1 1))).map
          (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex) = 0
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp,
      ZPoly.map_liftOuter]
    simp [HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, evalZPoly_X,
      Polynomial.eval_comp, AlgebraicRoot.toComplex_isRoot]

private theorem ZPoly.negRoots_isRoot_of_isRoot {p : ZPoly} {z : ℂ}
    (hp : p ≠ 0) (hz : (HexRootsMathlib.toPolyℂ p).IsRoot z) :
    (HexRootsMathlib.toPolyℂ p.negRoots).IsRoot (-z) := by
  let reflected : ZPoly := DensePoly.compose p (-ZPoly.X)
  have hreflected :
      HexRootsMathlib.toPolyℂ reflected =
        (HexRootsMathlib.toPolyℂ p).comp (-Polynomial.X) := by
    change
      (HexPolyMathlib.toPolynomial reflected).map (Int.castRingHom ℂ) =
        ((HexPolyMathlib.toPolynomial p).map (Int.castRingHom ℂ)).comp
          (-Polynomial.X)
    dsimp only [reflected]
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp]
    simp [ZPoly.X, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X]
  have hreflectedRoot :
      (HexRootsMathlib.toPolyℂ reflected).eval (-z) = 0 := by
    rw [hreflected, Polynomial.eval_comp]
    simpa [Polynomial.IsRoot] using hz
  have hpSize : p.size ≠ 0 := by
    intro hsize
    exact hp ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hpComplex : HexRootsMathlib.toPolyℂ p ≠ 0 :=
    HexRootsMathlib.toPolyℂ_ne_zero p hpSize
  have hreflectedComplex : HexRootsMathlib.toPolyℂ reflected ≠ 0 := by
    rw [hreflected]
    intro hzero
    have hdegree := congrArg Polynomial.degree hzero
    rw [Polynomial.degree_comp_neg_X, Polynomial.degree_zero] at hdegree
    exact hpComplex (Polynomial.degree_eq_bot.mp hdegree)
  have hreflectedNe : reflected ≠ 0 := by
    intro hzero
    apply hreflectedComplex
    rw [hzero]
    simp [HexRootsMathlib.toPolyℂ]
  have hcontent : ZPoly.content reflected ≠ 0 :=
    HexPolyZMathlib.content_ne_zero reflected hreflectedNe
  have hdecomp :
      HexRootsMathlib.toPolyℂ reflected =
        Polynomial.C (ZPoly.content reflected : ℂ) *
          HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected) := by
    simpa [HexRootsMathlib.toPolyℂ] using congrArg
      (fun q : Polynomial ℤ => q.map (Int.castRingHom ℂ))
      (HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart reflected)
  have hprimitiveRoot :
      (HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected)).eval (-z) = 0 := by
    have hproduct :
        (ZPoly.content reflected : ℂ) *
          (HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected)).eval (-z) = 0 := by
      rw [← Polynomial.eval_C_mul, ← hdecomp]
      exact hreflectedRoot
    exact (mul_eq_zero.mp hproduct).resolve_left (by exact_mod_cast hcontent)
  unfold ZPoly.negRoots ZPoly.normalizePrimitiveSign
  change (HexRootsMathlib.toPolyℂ
    (if (ZPoly.primitivePart reflected).leadingCoeff < 0 then
      DensePoly.scale (-1) (ZPoly.primitivePart reflected)
    else ZPoly.primitivePart reflected)).IsRoot (-z)
  split
  · simpa [Polynomial.IsRoot, HexRootsMathlib.toPolyℂ,
      HexPolyMathlib.toPolynomial_scale] using hprimitiveRoot
  · exact hprimitiveRoot

private theorem DyadicSquare.neg_mem_closedDisc {s : DyadicSquare} {z : ℂ}
    (hz : z ∈ HexRootsMathlib.DyadicSquare.closedDisc s) :
    -z ∈ HexRootsMathlib.DyadicSquare.closedDisc s.neg := by
  have hcenter : HexRootsMathlib.DyadicSquare.center s.neg =
      -HexRootsMathlib.DyadicSquare.center s := by
    apply Complex.ext <;>
      simp [DyadicSquare.neg, HexRootsMathlib.DyadicSquare.center,
        Hex.DyadicSquare.center, HexRootsMathlib.GaussDyadic.toComplex]
  have hradius : HexRootsMathlib.DyadicSquare.radius s.neg =
      HexRootsMathlib.DyadicSquare.radius s := by
    simp [HexRootsMathlib.DyadicSquare.radius_eq, DyadicSquare.neg]
  rw [HexRootsMathlib.DyadicSquare.closedDisc, Metric.mem_closedBall] at hz ⊢
  rw [hcenter, hradius]
  simpa only [dist_neg_neg] using hz

namespace AlgebraicRoot

/-- Reflection computes complex negation. -/
theorem neg_toComplex (a : AlgebraicRoot) :
    a.neg.toComplex = -a.toComplex := by
  have hroot :
      (HexRootsMathlib.toPolyℂ a.p.negRoots).IsRoot (-a.toComplex) :=
    ZPoly.negRoots_isRoot_of_isRoot
      (HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep)
      (AlgebraicRoot.toComplex_isRoot a)
  have hmem :
      -a.toComplex ∈
        HexRootsMathlib.DyadicSquare.closedDisc a.neg.rep.1.square := by
    exact DyadicSquare.neg_mem_closedDisc
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep)
  exact (HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
    a.neg.rep hroot hmem).symm

/-- A certified lazy sum denotes the sum of its inputs. -/
theorem add?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.add? b = some c) :
    c.toComplex = a.toComplex + b.toComplex := by
  sorry

/-- The bounded lazy addition search always finds its certificate. -/
theorem add?_isSome (a b : AlgebraicRoot) :
    (a.add? b).isSome := by
  sorry

/-- Total lazy addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicRoot) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  cases h : a.add? b with
  | none =>
      have hsome := add?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.add, h] using add?_sound a b h

/-- A certified lazy difference denotes the difference of its inputs. -/
theorem sub?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.sub? b = some c) :
    c.toComplex = a.toComplex - b.toComplex := by
  have hsum : c.toComplex = a.toComplex + b.neg.toComplex :=
    add?_sound a b.neg h
  rw [neg_toComplex] at hsum
  exact hsum

/-- The bounded lazy subtraction search always finds its certificate. -/
theorem sub?_isSome (a b : AlgebraicRoot) :
    (a.sub? b).isSome := by
  exact add?_isSome a b.neg

/-- Total lazy subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicRoot) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  cases h : a.sub? b with
  | none =>
      have hsome := sub?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.sub, h] using sub?_sound a b h

/-- A certified lazy product denotes the product of its inputs. -/
theorem mul?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.mul? b = some c) :
    c.toComplex = a.toComplex * b.toComplex := by
  sorry

/-- The bounded lazy multiplication search always finds its certificate. -/
theorem mul?_isSome (a b : AlgebraicRoot) :
    (a.mul? b).isSome := by
  sorry

/-- Total lazy multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicRoot) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  cases h : a.mul? b with
  | none =>
      have hsome := mul?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.mul, h] using mul?_sound a b h

/-- A certified lazy inverse denotes the reciprocal of its input, including
the executable convention `0⁻¹ = 0`. -/
theorem inv?_sound (a : AlgebraicRoot) {b : AlgebraicRoot}
    (h : a.inv? = some b) :
    b.toComplex = a.toComplex⁻¹ := by
  sorry

/-- The bounded lazy inverse search always finds its certificate. -/
theorem inv?_isSome (a : AlgebraicRoot) :
    a.inv?.isSome := by
  sorry

/-- Total lazy inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicRoot) :
    a.inv.toComplex = a.toComplex⁻¹ := by
  cases h : a.inv? with
  | none =>
      have hsome := inv?_isSome a
      simp [h] at hsome
  | some b =>
      simpa [AlgebraicRoot.inv, h] using inv?_sound a h

/-- A certified lazy quotient denotes the quotient of its inputs. -/
theorem div?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.div? b = some c) :
    c.toComplex = a.toComplex / b.toComplex := by
  cases hb : b.inv? with
  | none => simp [AlgebraicRoot.div?, hb] at h
  | some bInv =>
      have hmul : a.mul? bInv = some c := by
        simpa [AlgebraicRoot.div?, hb] using h
      rw [mul?_sound a bInv hmul, inv?_sound b hb]
      rfl

/-- The bounded lazy division search always finds its certificate. -/
theorem div?_isSome (a b : AlgebraicRoot) :
    (a.div? b).isSome := by
  cases hb : b.inv? with
  | none =>
      have hsome := inv?_isSome b
      simp [hb] at hsome
  | some bInv =>
      simpa [AlgebraicRoot.div?, hb] using mul?_isSome a bInv

/-- Total lazy division computes complex division. -/
theorem div_toComplex (a b : AlgebraicRoot) :
    (a.div b).toComplex = a.toComplex / b.toComplex := by
  cases h : a.div? b with
  | none =>
      have hsome := div?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.div, h] using div?_sound a b h

end AlgebraicRoot

namespace AlgebraicNumber

/-- Canonical addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicNumber) :
    (a + b).toComplex = a.toComplex + b.toComplex := by
  change (a.toRoot.add b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.add_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicNumber) :
    (a - b).toComplex = a.toComplex - b.toComplex := by
  change (a.toRoot.sub b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.sub_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicNumber) :
    (a * b).toComplex = a.toComplex * b.toComplex := by
  change (a.toRoot.mul b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.mul_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical negation computes complex negation. -/
theorem neg_toComplex (a : AlgebraicNumber) :
    (-a).toComplex = -a.toComplex := by
  change a.toRoot.neg.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.neg_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicNumber) :
    a⁻¹.toComplex = a.toComplex⁻¹ := by
  change a.toRoot.inv.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.inv_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical division computes complex division. -/
theorem div_toComplex (a b : AlgebraicNumber) :
    (a / b).toComplex = a.toComplex / b.toComplex := by
  change (a.toRoot.div b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.div_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

end AlgebraicNumber

end

end Hex
