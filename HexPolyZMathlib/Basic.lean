import HexPolyMathlib.Basic
import HexHensel.Basic
import HexModArithMathlib
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ZMod.Basic
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

@[simp]
theorem coeff_toPolynomial (p : Hex.ZPoly) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n :=
  HexPolyMathlib.coeff_toPolynomial p n

@[simp]
theorem ofPolynomial_zero :
    ofPolynomial (0 : Polynomial ℤ) = 0 :=
  HexPolyMathlib.ofPolynomial_zero

@[simp]
theorem toPolynomial_zero :
    toPolynomial (0 : Hex.ZPoly) = 0 :=
  HexPolyMathlib.toPolynomial_zero

@[simp]
theorem toPolynomial_C (c : ℤ) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c :=
  HexPolyMathlib.toPolynomial_C c

@[simp]
theorem toPolynomial_add (p q : Hex.ZPoly) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q :=
  HexPolyMathlib.toPolynomial_add p q

@[simp]
theorem toPolynomial_mul (p q : Hex.ZPoly) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q :=
  HexPolyMathlib.toPolynomial_mul p q

@[simp]
theorem toPolynomial_ofPolynomial (p : Polynomial ℤ) :
    toPolynomial (ofPolynomial p) = p :=
  HexPolyMathlib.toPolynomial_ofPolynomial p

@[simp]
theorem ofPolynomial_toPolynomial (p : Hex.ZPoly) :
    ofPolynomial (toPolynomial p) = p :=
  HexPolyMathlib.ofPolynomial_toPolynomial p

/-- The executable `ZPoly` representation is ring-equivalent to Mathlib
polynomials over `ℤ`. -/
abbrev equiv : Hex.ZPoly ≃+* Polynomial ℤ :=
  HexPolyMathlib.equiv

@[simp]
theorem equiv_apply (p : Hex.ZPoly) :
    equiv p = toPolynomial p := by
  rfl

@[simp]
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

/--
Divisibility of executable integer polynomials reduces modulo `p` after
transporting both sides to Mathlib polynomials over `ZMod p`.
-/
theorem map_intCast_zmod_dvd_of_zpoly_dvd
    (p : Nat) {g f : Hex.ZPoly} (hgf : g ∣ f) :
    (toPolynomial g).map (Int.castRingHom (ZMod p)) ∣
      (toPolynomial f).map (Int.castRingHom (ZMod p)) := by
  rcases hgf with ⟨q, rfl⟩
  refine ⟨(toPolynomial q).map (Int.castRingHom (ZMod p)), ?_⟩
  rw [toPolynomial_mul, Polynomial.map_mul]

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
Issue-spec rename of `map_intCast_zmod_dvd_of_zpoly_dvd`: divisibility of
executable integer polynomials transports to divisibility of their Mathlib
reductions modulo `p`.
-/
theorem dvd_modP_of_dvd
    (p : Nat) {g f : Hex.ZPoly} (hgf : g ∣ f) :
    (toPolynomial g).map (Int.castRingHom (ZMod p)) ∣
      (toPolynomial f).map (Int.castRingHom (ZMod p)) :=
  map_intCast_zmod_dvd_of_zpoly_dvd p hgf

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

end

end HexPolyZMathlib
