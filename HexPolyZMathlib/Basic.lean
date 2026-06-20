import HexPolyMathlib.Basic
import HexHensel.Basic
import HexModArithMathlib
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.GCDMonoid.Nat
import HexPolyZ

/-!
Correspondence definitions between `Hex.ZPoly` and Mathlib's `Polynomial ℤ`.

This module specializes the generic dense-polynomial correspondence to integer
coefficients so downstream libraries can work directly with the `ZPoly`
abbreviation and the corresponding `Polynomial ℤ` equivalence.
-/

namespace HexPolyZMathlib

noncomputable section

/-- Interpret an executable integer polynomial as a Mathlib polynomial. -/
abbrev toPolynomial (p : Hex.ZPoly) : Polynomial ℤ :=
  HexPolyMathlib.toPolynomial p

/-- Rebuild an executable integer polynomial from a Mathlib polynomial. -/
abbrev ofPolynomial (p : Polynomial ℤ) : Hex.ZPoly :=
  HexPolyMathlib.ofPolynomial p

/-- Coefficients of the embedded Mathlib polynomial agree with the executable
coefficients. -/
@[simp, grind =]
theorem coeff_toPolynomial (p : Hex.ZPoly) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n :=
  HexPolyMathlib.coeff_toPolynomial p n

/-- `ofPolynomial` sends the zero polynomial to the zero `ZPoly`. -/
@[simp, grind =]
theorem ofPolynomial_zero :
    ofPolynomial (0 : Polynomial ℤ) = 0 :=
  HexPolyMathlib.ofPolynomial_zero

/-- `toPolynomial` sends the zero `ZPoly` to the zero polynomial. -/
@[simp, grind =]
theorem toPolynomial_zero :
    toPolynomial (0 : Hex.ZPoly) = 0 :=
  HexPolyMathlib.toPolynomial_zero

/-- `toPolynomial` sends the executable constant `C c` to Mathlib's `Polynomial.C c`. -/
@[simp, grind =]
theorem toPolynomial_C (c : ℤ) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c :=
  HexPolyMathlib.toPolynomial_C c

/-- `toPolynomial` is additive. -/
@[simp, grind =]
theorem toPolynomial_add (p q : Hex.ZPoly) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q :=
  HexPolyMathlib.toPolynomial_add p q

/-- `toPolynomial` is multiplicative. -/
@[simp, grind =]
theorem toPolynomial_mul (p q : Hex.ZPoly) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q :=
  HexPolyMathlib.toPolynomial_mul p q

/-- `toPolynomial` sends the executable `1` to Mathlib's `1`. -/
@[simp, grind =]
theorem toPolynomial_one :
    toPolynomial (1 : Hex.ZPoly) = 1 :=
  HexPolyMathlib.toPolynomial_one

/-- `toPolynomial` commutes with negation. -/
@[simp, grind =]
theorem toPolynomial_neg (p : Hex.ZPoly) :
    toPolynomial (-p) = -toPolynomial p :=
  HexPolyMathlib.toPolynomial_neg p

/-- `toPolynomial` commutes with subtraction. -/
@[simp, grind =]
theorem toPolynomial_sub (p q : Hex.ZPoly) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q :=
  HexPolyMathlib.toPolynomial_sub p q

/-- `toPolynomial` is a left inverse of `ofPolynomial`: embedding a rebuilt
polynomial recovers it. -/
@[simp, grind =]
theorem toPolynomial_ofPolynomial (p : Polynomial ℤ) :
    toPolynomial (ofPolynomial p) = p :=
  HexPolyMathlib.toPolynomial_ofPolynomial p

/-- `ofPolynomial` is a left inverse of `toPolynomial`: rebuilding an embedded
`ZPoly` recovers it. -/
@[simp, grind =]
theorem ofPolynomial_toPolynomial (p : Hex.ZPoly) :
    ofPolynomial (toPolynomial p) = p :=
  HexPolyMathlib.ofPolynomial_toPolynomial p

/-- The executable `ZPoly` representation is ring-equivalent to Mathlib
polynomials over `ℤ`. -/
abbrev equiv : Hex.ZPoly ≃+* Polynomial ℤ :=
  HexPolyMathlib.equiv

/-- The ring equivalence acts as `toPolynomial` in the forward direction. -/
@[simp, grind =]
theorem equiv_apply (p : Hex.ZPoly) :
    equiv p = toPolynomial p := by
  rfl

/-- The inverse ring equivalence acts as `ofPolynomial`. -/
@[simp, grind =]
theorem equiv_symm_apply (p : Polynomial ℤ) :
    equiv.symm p = ofPolynomial p := by
  rfl

/-- The Mathlib-free `ZPoly` unit predicate agrees with Mathlib units after
transport to `Polynomial ℤ`. -/
theorem isUnit_iff_toPolynomial_isUnit (f : Hex.ZPoly) :
    Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f) := by
  constructor
  · rintro (rfl | rfl)
    · simp
    · simp
  · intro h
    rcases Polynomial.isUnit_iff.mp h with ⟨r, hr, hpoly⟩
    have hf : f = Hex.DensePoly.C r := by
      exact equiv.injective (by
        simpa using hpoly.symm)
    rcases Int.isUnit_iff.mp hr with hr | hr
    · left
      simp [hf, hr]
    · right
      simp [hf, hr]

/--
The executable coefficientwise reduction `Hex.ZPoly.modP` agrees with
Mathlib's coefficient map from `ℤ[X]` to `(ZMod p)[X]`, after transporting
the executable `ZMod64 p` coefficients through the `ZMod64`/`ZMod` equivalence.
-/
theorem coeff_toZMod_modP_eq_coeff_map_intCast
    (p : Nat) [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) (n : Nat) :
    HexModArithMathlib.ZMod64.toZMod ((Hex.ZPoly.modP p f).coeff n) =
      ((toPolynomial f).map (Int.castRingHom (ZMod p))).coeff n := by
  rw [Polynomial.coeff_map, Hex.ZPoly.coeff_modP, coeff_toPolynomial]
  change
    HexModArithMathlib.ZMod64.toZMod
        (Hex.ZMod64.ofNat p (Hex.ZPoly.intModNat (f.coeff n) p)) =
      ((f.coeff n : ℤ) : ZMod p)
  apply ZMod.val_injective p
  rw [HexModArithMathlib.ZMod64.val_toZMod, Hex.ZMod64.toNat_ofNat]
  apply Int.ofNat.inj
  change ((Hex.ZPoly.intModNat (f.coeff n) p % p : Nat) : ℤ) =
    (((f.coeff n : ℤ) : ZMod p).val : ℤ)
  rw [Int.natCast_mod, ZMod.val_intCast]
  unfold Hex.ZPoly.intModNat
  have hp : (p : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Hex.ZMod64.Bounds.pPos (p := p)))
  have hcast :
      ((f.coeff n % Int.ofNat p).toNat : ℤ) =
        f.coeff n % Int.ofNat p :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hp)
  rw [hcast]
  change f.coeff n % (p : ℤ) % (p : ℤ) = f.coeff n % (p : ℤ)
  rw [Int.emod_emod]

/--
Extensional equality for any Mathlib polynomial over `ZMod p` whose
coefficients are supplied by the executable `Hex.ZPoly.modP` image.
Downstream finite-field polynomial transports can instantiate the coefficient
hypothesis with their own `FpPoly` coefficient lemma.
-/
theorem eq_map_intCast_of_coeff_eq_toZMod_modP
    (p : Nat) [Hex.ZMod64.Bounds p] (f : Hex.ZPoly)
    {q : Polynomial (ZMod p)}
    (hq :
      ∀ n, q.coeff n =
        HexModArithMathlib.ZMod64.toZMod ((Hex.ZPoly.modP p f).coeff n)) :
    q = (toPolynomial f).map (Int.castRingHom (ZMod p)) := by
  ext n
  rw [hq, coeff_toZMod_modP_eq_coeff_map_intCast]

/-- Reduction modulo `p` preserves natural degree when the leading coefficient
survives the map to `ZMod p`. -/
theorem natDegree_map_intCast_zmod_eq_of_leadingCoeff_ne_zero
    (p : Nat) (g : Hex.ZPoly)
    (hlc :
      (Int.castRingHom (ZMod p)) (toPolynomial g).leadingCoeff ≠ 0) :
    ((toPolynomial g).map (Int.castRingHom (ZMod p))).natDegree =
      (toPolynomial g).natDegree :=
  Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    (Int.castRingHom (ZMod p)) hlc

/--
Divisibility of executable integer polynomials transports to divisibility of
their Mathlib reductions modulo `p`.
-/
theorem dvd_modP_of_dvd
    (p : Nat) {g f : Hex.ZPoly} (hgf : g ∣ f) :
    (toPolynomial g).map (Int.castRingHom (ZMod p)) ∣
      (toPolynomial f).map (Int.castRingHom (ZMod p)) := by
  rcases hgf with ⟨q, rfl⟩
  refine ⟨(toPolynomial q).map (Int.castRingHom (ZMod p)), ?_⟩
  rw [toPolynomial_mul, Polynomial.map_mul]

/--
Core integer-to-`ZMod p` identity underlying `modP`: pushing an
integer through `intModNat`/`ZMod64.ofNat` and then to Mathlib's `ZMod p` via
`toZMod` agrees with the direct integer cast.
-/
theorem toZMod_ZMod64_ofNat_intModNat_eq_intCast
    (p : Nat) [Hex.ZMod64.Bounds p] (z : ℤ) :
    HexModArithMathlib.ZMod64.toZMod
        (Hex.ZMod64.ofNat p (Hex.ZPoly.intModNat z p)) =
      ((z : ℤ) : ZMod p) := by
  apply ZMod.val_injective p
  rw [HexModArithMathlib.ZMod64.val_toZMod, Hex.ZMod64.toNat_ofNat]
  apply Int.ofNat.inj
  change ((Hex.ZPoly.intModNat z p % p : Nat) : ℤ) =
    (((z : ℤ) : ZMod p).val : ℤ)
  rw [Int.natCast_mod, ZMod.val_intCast]
  unfold Hex.ZPoly.intModNat
  have hp : (p : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Hex.ZMod64.Bounds.pPos (p := p)))
  have hcast :
      ((z % Int.ofNat p).toNat : ℤ) =
        z % Int.ofNat p :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hp)
  rw [hcast]
  change z % (p : ℤ) % (p : ℤ) = z % (p : ℤ)
  rw [Int.emod_emod]

/-- The executable variable-dilation `X ↦ c · X` corresponds to Mathlib
composition with `C c * X`. -/
@[simp, grind =]
theorem toPolynomial_dilate (c : ℤ) (g : Hex.ZPoly) :
    toPolynomial (Hex.ZPoly.dilate c g) =
      (toPolynomial g).comp (Polynomial.C c * Polynomial.X) := by
  ext n
  rw [coeff_toPolynomial, Hex.ZPoly.coeff_dilate, Polynomial.comp_C_mul_X_coeff,
    coeff_toPolynomial, mul_comm]

/-- Variable dilation is multiplicative: substituting `X ↦ c · X` is a ring
homomorphism, so it distributes over products. -/
theorem dilate_mul (c : ℤ) (g h : Hex.ZPoly) :
    Hex.ZPoly.dilate c (g * h) =
      Hex.ZPoly.dilate c g * Hex.ZPoly.dilate c h := by
  apply equiv.injective
  simp only [equiv_apply, toPolynomial_dilate, toPolynomial_mul, Polynomial.mul_comp]

/-- For a nonzero dilation factor, variable dilation preserves natural degree:
`C c * X` has degree `1` with a unit leading coefficient over the integers. -/
theorem natDegree_toPolynomial_dilate (c : ℤ) (hc : c ≠ 0) (g : Hex.ZPoly) :
    (toPolynomial (Hex.ZPoly.dilate c g)).natDegree =
      (toPolynomial g).natDegree := by
  rw [toPolynomial_dilate, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X c hc, mul_one]

/-- Substitution `X ↦ u · X` by a unit `u` reflects divisibility: if the dilated
polynomials divide, so do the originals. The substitution is a ring automorphism
of `R[X]` with inverse `X ↦ u⁻¹ · X`, so applying that inverse hom to the
hypothesis (via `map_dvd`) recovers `a ∣ b`. This is the substitution engine the
lift-stage recovery chain uses to descend a divisibility through `X ↦ lc · X`,
where `lc` is a unit because the prime does not divide the leading coefficient. -/
theorem dvd_of_comp_unit_mul_X {R : Type*} [CommRing R] {u : R} (hu : IsUnit u)
    {a b : Polynomial R}
    (h : a.comp (Polynomial.C u * Polynomial.X) ∣
          b.comp (Polynomial.C u * Polynomial.X)) :
    a ∣ b := by
  obtain ⟨w, hw⟩ := hu
  set v : R := ↑w⁻¹ with hv
  have huv : u * v = 1 := by rw [hv, ← hw]; exact w.mul_inv
  have hcomp : (Polynomial.C u * Polynomial.X).comp (Polynomial.C v * Polynomial.X)
      = Polynomial.X := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
      ← Polynomial.C_mul, huv, Polynomial.C_1, one_mul]
  have key : ∀ p : Polynomial R,
      (p.comp (Polynomial.C u * Polynomial.X)).comp (Polynomial.C v * Polynomial.X)
        = p := by
    intro p
    rw [Polynomial.comp_assoc, hcomp, Polynomial.comp_X]
  have hdvd := map_dvd (Polynomial.compRingHom (Polynomial.C v * Polynomial.X)) h
  rwa [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply, key, key]
    at hdvd

/-- Divisibility is invariant under substitution `X ↦ u · X` by a unit: the
dilated polynomials divide iff the originals do. The forward direction is
`map_dvd` of the composition ring hom (no unit needed); the reverse is
`dvd_of_comp_unit_mul_X`. -/
theorem comp_unit_mul_X_dvd_iff {R : Type*} [CommRing R] {u : R} (hu : IsUnit u)
    {a b : Polynomial R} :
    a.comp (Polynomial.C u * Polynomial.X) ∣
        b.comp (Polynomial.C u * Polynomial.X) ↔ a ∣ b :=
  ⟨dvd_of_comp_unit_mul_X hu, fun h => by
    have hdvd := map_dvd (Polynomial.compRingHom (Polynomial.C u * Polynomial.X)) h
    rwa [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at hdvd⟩

/-! ### Gauss content/primitive-part correspondence

The executable `Hex.ZPoly.content`/`primitivePart` carry their own Gauss theory
(`content_mul`, `content_mul_primitivePart`, `primitivePart_primitive`). These
lemmas relate that theory to Mathlib's `Polynomial.content`/`primPart`, so the
recombination recovery proof can lean on Mathlib's Gauss lemma machinery. -/

/-- The Mathlib content of the embedded polynomial agrees with the executable
integer content. Both are the normalized (nonnegative) gcd of the coefficients,
so this is the Gauss bridge between the two content theories. -/
theorem toPolynomial_content (f : Hex.ZPoly) :
    (toPolynomial f).content = Hex.ZPoly.content f := by
  have hnonneg : 0 ≤ Hex.ZPoly.content f := by
    unfold Hex.ZPoly.content Hex.DensePoly.content
    exact Int.natCast_nonneg _
  refine dvd_antisymm_of_normalize_eq Polynomial.normalize_content
    (Int.normalize_of_nonneg hnonneg) ?_ ?_
  · rw [← Int.natAbs_dvd]
    refine Hex.ZPoly.dvd_content_of_nat_dvd_coeff f _ (fun n => ?_)
    rw [Int.natAbs_dvd, ← coeff_toPolynomial]
    exact Polynomial.content_dvd_coeff n
  · rw [Polynomial.dvd_content_iff_C_dvd, Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [coeff_toPolynomial]
    exact Hex.ZPoly.content_dvd_coeff f n

/-- Gauss content decomposition transported to Mathlib: the embedded polynomial
is its content times the embedded primitive part. -/
theorem toPolynomial_eq_C_content_mul_primitivePart (f : Hex.ZPoly) :
    toPolynomial f =
      Polynomial.C (Hex.ZPoly.content f) *
        toPolynomial (Hex.ZPoly.primitivePart f) := by
  conv_lhs => rw [← Hex.ZPoly.content_mul_primitivePart f]
  rw [← Hex.ZPoly.C_mul_eq_scale, toPolynomial_mul, toPolynomial_C]

/-- A primitive executable polynomial embeds to a Mathlib-primitive polynomial. -/
theorem isPrimitive_toPolynomial_of_primitive (f : Hex.ZPoly)
    (hf : Hex.ZPoly.Primitive f) : (toPolynomial f).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one, toPolynomial_content]
  exact hf

/-- A nonzero executable polynomial has nonzero content. -/
theorem content_ne_zero (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.ZPoly.content f ≠ 0 := by
  intro hz
  apply hf
  have hz' : (toPolynomial f).content = 0 := by rw [toPolynomial_content]; exact hz
  rw [Polynomial.content_eq_zero_iff] at hz'
  rw [← ofPolynomial_toPolynomial f, hz', ofPolynomial_zero]

/-- **Packaged recombination recovery.** Given the keystone product identity
`C (lc^(d-1)) * core = dilate lc g * dilate lc h` (the executable keystone
`dilate_transformedCore` combined with `dilate_mul`), with `lc ≠ 0` and a nonzero
`core`, the primitive part of `dilate lc g` divides `core`, is primitive, and has
the same degree as `g`. This is the inverse-factor correspondence the
recombination recovery proof consumes. -/
theorem dilate_recovery (core g h : Hex.ZPoly) (lc : ℤ) (d : ℕ)
    (hlc0 : lc ≠ 0) (hcore0 : core ≠ 0)
    (hkey : Hex.DensePoly.C (lc ^ (d - 1)) * core =
              Hex.ZPoly.dilate lc g * Hex.ZPoly.dilate lc h) :
    toPolynomial (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g)) ∣
        toPolynomial core ∧
      Hex.ZPoly.Primitive (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g)) ∧
      (toPolynomial (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g))).natDegree =
        (toPolynomial g).natDegree := by
  -- Transport the keystone identity into `Polynomial ℤ`.
  have hkeyP : Polynomial.C (lc ^ (d - 1)) * toPolynomial core =
      toPolynomial (Hex.ZPoly.dilate lc g) *
        toPolynomial (Hex.ZPoly.dilate lc h) := by
    have h := congrArg toPolynomial hkey
    rwa [toPolynomial_mul, toPolynomial_mul, toPolynomial_C] at h
  set G := toPolynomial (Hex.ZPoly.dilate lc g) with hG
  set K := toPolynomial core with hK
  set pg := Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g) with hpg
  -- Nonvanishing facts.
  have hk0 : lc ^ (d - 1) ≠ 0 := pow_ne_zero _ hlc0
  have hK0 : K ≠ 0 := by
    rw [hK]; intro hz
    exact hcore0 (by rw [← ofPolynomial_toPolynomial core, hz, ofPolynomial_zero])
  have hlhs0 : Polynomial.C (lc ^ (d - 1)) * K ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hk0) hK0
  have hG0 : G ≠ 0 := left_ne_zero_of_mul (hkeyP ▸ hlhs0)
  have hdg0 : Hex.ZPoly.dilate lc g ≠ 0 := by
    intro hz; exact hG0 (by rw [hG, hz, toPolynomial_zero])
  -- (b) primitivity.
  have hb : Hex.ZPoly.Primitive pg :=
    Hex.ZPoly.primitivePart_primitive _ (content_ne_zero _ hdg0)
  have hPgPrim : (toPolynomial pg).IsPrimitive :=
    isPrimitive_toPolynomial_of_primitive pg hb
  -- Decompose `G` through its content and primitive part.
  have hGdecomp : G = Polynomial.C (Hex.ZPoly.content (Hex.ZPoly.dilate lc g)) *
      toPolynomial pg := by
    rw [hG, hpg]; exact toPolynomial_eq_C_content_mul_primitivePart _
  -- (a) divisibility.
  have hPg_dvd_G : toPolynomial pg ∣ G := by
    rw [hGdecomp]; exact dvd_mul_left _ _
  have hG_dvd : G ∣ Polynomial.C (lc ^ (d - 1)) * K := by
    rw [hkeyP]; exact dvd_mul_right _ _
  have hPg_dvd_CkK : toPolynomial pg ∣ Polynomial.C (lc ^ (d - 1)) * K :=
    hPg_dvd_G.trans hG_dvd
  have ha : toPolynomial pg ∣ K := by
    rw [← hPgPrim.dvd_primPart_iff_dvd hK0]
    have hkpp := (hPgPrim.dvd_primPart_iff_dvd hlhs0).mpr hPg_dvd_CkK
    rw [Polynomial.primPart_mul hlhs0] at hkpp
    exact ((Polynomial.isUnit_primPart_C (lc ^ (d - 1))).dvd_mul_left).mp hkpp
  -- (c) degree.
  have hc : (toPolynomial pg).natDegree = (toPolynomial g).natDegree := by
    have hcontent0 : Hex.ZPoly.content (Hex.ZPoly.dilate lc g) ≠ 0 :=
      content_ne_zero _ hdg0
    have hGdeg : G.natDegree = (toPolynomial pg).natDegree := by
      rw [hGdecomp, Polynomial.natDegree_C_mul hcontent0]
    rw [← hGdeg, hG, natDegree_toPolynomial_dilate lc hlc0]
  exact ⟨ha, hb, hc⟩

end

end HexPolyZMathlib
