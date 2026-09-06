/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.FactorGeneric
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dimension.Constructions

public section

/-!
# Law-bearing arithmetic for validated number towers

The generic coordinate proofs and recursive factor-checker correctness establish
injectivity before the public field structure is assembled.
-/

namespace Hex.NumberTower

/-- The fixed complex interpretation is injective. -/
theorem toComplex_injective (T : NumberTower) :
    Function.Injective T.toComplex :=
  toComplex_injective_of_denote T
    (denoteInjective_of_valid T.levels.toList T.valid)

/-- The canonical coefficient denotation of a certified tower is injective. -/
theorem coeffDenote_injective (T : NumberTower) :
    LevelSemantics.DenoteInjective T.levels.toList :=
  denoteInjective_of_valid T.levels.toList T.valid

/-- Executable zero denotes complex zero. -/
theorem map_zero (T : NumberTower) :
    T.toComplex (0 : Elem T) = 0 := by
  rw [zero_eq_ofRat]
  simpa using toComplex_ofRat T 0

/-- Executable one denotes complex one. -/
theorem map_one (T : NumberTower) :
    T.toComplex (1 : Elem T) = 1 := by
  rw [one_eq_ofRat]
  simpa using toComplex_ofRat T 1

/-- Coordinate addition computes complex addition. -/
theorem map_add (T : NumberTower) (a b : Elem T) :
    T.toComplex (a + b) = T.toComplex a + T.toComplex b := by
  rw [LevelSemantics.toComplex_eq_denote T (a + b),
    LevelSemantics.toComplex_eq_denote T a,
    LevelSemantics.toComplex_eq_denote T b, coeffs_add]
  simpa [dim] using
    LevelSemantics.denote_add T.levels.toList (coeffs a) (coeffs b)

/-- Coordinate negation computes complex negation. -/
theorem map_neg (T : NumberTower) (a : Elem T) :
    T.toComplex (-a) = -T.toComplex a := by
  have h := map_add T a (-a)
  rw [NumberTower.add_neg_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Coordinate subtraction computes complex subtraction. -/
theorem map_sub (T : NumberTower) (a b : Elem T) :
    T.toComplex (a - b) = T.toComplex a - T.toComplex b := by
  rw [NumberTower.sub_eq_add_neg, map_add, map_neg]
  rfl

/-- Recursive reduced multiplication computes complex multiplication. -/
theorem map_mul (T : NumberTower) (a b : Elem T) :
    T.toComplex (a * b) = T.toComplex a * T.toComplex b := by
  rw [LevelSemantics.toComplex_eq_denote T (a * b),
    LevelSemantics.toComplex_eq_denote T a,
    LevelSemantics.toComplex_eq_denote T b, coeffs_mul]
  exact LevelSemantics.denote_mul T.levels.toList T.valid (coeffs a) (coeffs b)

/-- Recursive extended-gcd inversion computes complex inversion, including
the executable convention `0⁻¹ = 0`. -/
theorem map_inv (T : NumberTower) (a : Elem T) :
    T.toComplex a⁻¹ = (T.toComplex a)⁻¹ := by
  rw [LevelSemantics.toComplex_eq_denote T a⁻¹,
    LevelSemantics.toComplex_eq_denote T a, coeffs_inv]
  exact LevelSemantics.denote_invCoords T.levels.toList T.valid
    (coeffDenote_injective T) (coeffs a)

/-- Tower division computes complex division. -/
theorem map_div (T : NumberTower) (a b : Elem T) :
    T.toComplex (a / b) = T.toComplex a / T.toComplex b := by
  change T.toComplex (a * b⁻¹) = _
  rw [map_mul, map_inv]
  rfl

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul (T : NumberTower) (q : Rat) (a : Elem T) :
    T.toComplex (q • a) = (q : ℂ) * T.toComplex a := by
  rw [LevelSemantics.toComplex_eq_denote T (q • a),
    LevelSemantics.toComplex_eq_denote T a, coeffs_smul,
    LevelSemantics.denote_smul]

/-- Natural powers preserve the selected complex interpretation. -/
theorem map_natPow (T : NumberTower) (a : Elem T) (n : Nat) :
    T.toComplex (natPow a n) = T.toComplex a ^ n := by
  induction n with
  | zero => simp [natPow, map_one]
  | succ n ih => rw [natPow, map_mul, ih, pow_succ]

/-- Integer powers preserve the selected complex interpretation. -/
theorem map_intPow (T : NumberTower) (a : Elem T) (n : Int) :
    T.toComplex (intPow a n) = T.toComplex a ^ n := by
  cases n with
  | ofNat n => exact map_natPow T a n
  | negSucc n =>
      rw [intPow, map_inv, map_natPow]
      rfl

/-- The law-bearing field whose operations are the existing executable tower
coordinate operations. The remaining casts and scalar actions use the
canonical rational embedding. -/
@[expose, reducible]
noncomputable def elemField (T : NumberTower) : Field (Elem T) := by
  letI : SMul Nat (Elem T) := ⟨fun n a => (n : Rat) • a⟩
  letI : SMul Int (Elem T) := ⟨fun n a => (n : Rat) • a⟩
  letI : SMul ℚ≥0 (Elem T) := ⟨fun q a => (q : Rat) • a⟩
  -- The executable `Pow`, `NatCast` and `IntCast` instances are retained: the
  -- field proves laws for those operations rather than replacing them.
  letI : NNRatCast (Elem T) := ⟨fun q => T.ofRat (q : Rat)⟩
  letI : RatCast (Elem T) := ⟨fun q => T.ofRat q⟩
  apply Function.Injective.field T.toComplex (toComplex_injective T)
  · exact map_zero T
  · exact map_one T
  · exact map_add T
  · exact map_mul T
  · exact map_neg T
  · exact map_sub T
  · exact map_inv T
  · exact map_div T
  · intro n a
    change T.toComplex ((n : Rat) • a) = n • T.toComplex a
    rw [map_smul, nsmul_eq_mul]
    rfl
  · intro n a
    change T.toComplex ((n : Rat) • a) = n • T.toComplex a
    rw [map_smul, zsmul_eq_mul]
    rfl
  · intro q a
    change T.toComplex ((q : Rat) • a) = q • T.toComplex a
    rw [map_smul, NNRat.smul_def]
    rfl
  · intro q a
    change T.toComplex (q • a) = q • T.toComplex a
    rw [map_smul, Rat.smul_def]
  · exact map_natPow T
  · exact map_intPow T
  · intro n
    exact toComplex_ofRat T (n : Rat)
  · intro n
    exact toComplex_ofRat T (n : Rat)
  · intro q
    exact toComplex_ofRat T (q : Rat)
  · exact toComplex_ofRat T

namespace TowerField

/-- Opt-in field instance for tower elements. It is scoped so importing the
Mathlib correspondence layer does not make executable downstream definitions
depend on a noncomputable semantic proof dictionary. -/
noncomputable scoped instance (T : NumberTower) : Field (Elem T) := elemField T

end TowerField

open scoped TowerField

/-- The selected complex interpretation as an injective ring homomorphism. -/
@[expose]
noncomputable def embedding (T : NumberTower) : Elem T →+* ℂ where
  toFun := T.toComplex
  map_zero' := map_zero T
  map_one' := map_one T
  map_add' := map_add T
  map_mul' := map_mul T

@[simp]
theorem embedding_apply (T : NumberTower) (a : Elem T) :
    T.embedding a = T.toComplex a := rfl

/-- The selected complex ring homomorphism is an embedding. -/
theorem embedding_injective (T : NumberTower) :
    Function.Injective T.embedding := toComplex_injective T

/-- The Boolean zero test recognizes exactly semantic zero. -/
theorem isZero_iff (T : NumberTower) (a : Elem T) :
    NumberTower.isZero a ↔ T.toComplex a = 0 := by
  rw [NumberTower.isZero_iff_eq_zero]
  constructor
  · rintro rfl
    exact map_zero T
  · intro h
    apply toComplex_injective T
    rw [h, map_zero]

/-- Mixed-radix coordinate equality is exactly semantic equality. -/
theorem eq_iff_toComplex (T : NumberTower) (a b : Elem T) :
    a = b ↔ T.toComplex a = T.toComplex b := by
  constructor
  · exact fun h => congrArg T.toComplex h
  · intro h
    exact @toComplex_injective T a b h

namespace TowerField

/-- Tower coordinate fields have characteristic zero, through the injective
complex embedding. -/
scoped instance (T : NumberTower) : CharZero (Elem T) where
  cast_injective m n h := Nat.cast_injective (R := ℂ) <| by
    rw [← map_natCast T.embedding, ← map_natCast T.embedding, h]

/-- Opt-in `Lean.Grind.Field` law package for the executable tower
operations, derived from the scoped field instance through the standard
Mathlib bridge. It is scoped together with the field instance so executable
downstream code does not silently depend on the semantic dictionary. -/
noncomputable scoped instance (T : NumberTower) : Lean.Grind.Field (Elem T) :=
  Field.toGrindField (K := Elem T)

end TowerField

/-- The field's rational cast is the executable rational embedding. -/
theorem ratCast_eq_ofRat (T : NumberTower) (q : Rat) :
    (q : Elem T) = T.ofRat q := rfl

/-- Multiplication by an embedded rational is the executable scalar action. -/
theorem ratCast_mul_eq_smul (T : NumberTower) (q : Rat) (a : Elem T) :
    (q : Elem T) * a = q • a := by
  apply toComplex_injective T
  rw [map_mul, ratCast_eq_ofRat, toComplex_ofRat, map_smul]

/-- The mixed-radix coordinate representation as a `ℚ`-linear equivalence
with the fixed-width function space. -/
@[expose]
noncomputable def coordEquiv (T : NumberTower) :
    Elem T ≃ₗ[ℚ] (Fin T.dim → ℚ) where
  toFun a i := (coeffs a).getD i.val 0
  invFun v := ofCoeffs T (Array.ofFn v)
  map_add' a b := by
    funext i
    simp [coeffs_add, Arithmetic.addCoords, Array.getD, i.isLt]
  map_smul' q a := by
    funext i
    rw [Algebra.smul_def, eq_ratCast, ratCast_mul_eq_smul]
    simp [coeffs_smul, Array.getD, i.isLt]
  left_inv a := by
    apply Elem.ext
    rw [coeffs_ofCoeffs, normalizeCoeffs_eq_self _ _ (by simp)]
    apply Array.ext
    · simp
    · intro i hi₁ hi₂
      simp [Array.getD]
  right_inv v := by
    funext i
    show (coeffs (ofCoeffs T (Array.ofFn v))).getD i.val 0 = v i
    rw [coeffs_ofCoeffs, normalizeCoeffs_eq_self _ _ (by simp)]
    simp [Array.getD, i.isLt]

/-- The element type of a validated tower, regarded as the certified
coordinate field. The field, characteristic-zero, and `ℚ`-algebra structures
are the scoped instances of the `TowerField` namespace. -/
abbrev toField (T : NumberTower) : Type := Elem T

/-- The executable mixed-radix dimension is the `ℚ`-vector-space dimension of
the coordinate field. -/
theorem dim_eq_finrank (T : NumberTower) :
    T.dim = Module.finrank ℚ T.toField := by
  rw [(coordEquiv T).finrank_eq, Module.finrank_fin_fun]

namespace Extension

/-- An extension embedding preserves the fixed absolute embedding. This is a
property of checked constructors, not of arbitrary
{name}`Hex.NumberTower.Extension` records. -/
@[expose]
def PreservesEmbedding {T : NumberTower} (E : Extension T) : Prop :=
  ∀ a, E.tower.toComplex (E.embed a) = T.toComplex a

/-- The distinguished generator denotes the extension's stored absolute
root. -/
@[expose]
def GeneratorValue {T : NumberTower} (E : Extension T) : Prop :=
  E.tower.toComplex E.gen = E.root.toComplex

variable {T : NumberTower} (E : Extension T)

/-- A checked extension embedding is injective. -/
theorem embed_injective (hE : E.PreservesEmbedding) :
    Function.Injective E.embed := fun a b h => by
  apply toComplex_injective T
  rw [← hE, ← hE, h]

/-- A checked extension embedding is additive. -/
theorem embed_add (hE : E.PreservesEmbedding) (a b : Elem T) :
    E.embed (a + b) = E.embed a + E.embed b := by
  apply toComplex_injective E.tower
  rw [hE, map_add E.tower, hE, hE, map_add T]

/-- A checked extension embedding is multiplicative. -/
theorem embed_mul (hE : E.PreservesEmbedding) (a b : Elem T) :
    E.embed (a * b) = E.embed a * E.embed b := by
  apply toComplex_injective E.tower
  rw [hE, map_mul E.tower, hE, hE, map_mul T]

/-- A checked extension embedding fixes the embedded rationals. -/
theorem embed_ofRat (hE : E.PreservesEmbedding) (q : Rat) :
    E.embed (T.ofRat q) = E.tower.ofRat q := by
  apply toComplex_injective E.tower
  rw [hE, toComplex_ofRat, toComplex_ofRat]

/-- A checked extension embedding preserves the executable rational scalar
action. -/
theorem embed_smul (hE : E.PreservesEmbedding) (q : Rat) (a : Elem T) :
    E.embed (q • a) = q • E.embed a := by
  apply toComplex_injective E.tower
  rw [hE, map_smul E.tower, map_smul T, hE]

/-- A checked extension embedding as a `ℚ`-algebra homomorphism between the
certified coordinate fields. Injectivity is `embedAlgHom_injective`. -/
@[expose]
noncomputable def embedAlgHom (hE : E.PreservesEmbedding) :
    T.toField →ₐ[ℚ] E.tower.toField where
  toFun := E.embed
  map_one' := by
    apply toComplex_injective E.tower
    rw [hE, map_one E.tower, map_one T]
  map_mul' := embed_mul E hE
  map_zero' := by
    apply toComplex_injective E.tower
    rw [hE, map_zero E.tower, map_zero T]
  map_add' := embed_add E hE
  commutes' q := by
    rw [eq_ratCast (algebraMap ℚ T.toField), eq_ratCast (algebraMap ℚ E.tower.toField),
      ratCast_eq_ofRat, ratCast_eq_ofRat]
    exact embed_ofRat E hE q

/-- The algebra homomorphism packaging acts by the executable embedding. -/
@[simp]
theorem embedAlgHom_apply (hE : E.PreservesEmbedding) (a : Elem T) :
    embedAlgHom E hE a = E.embed a := rfl

/-- The `ℚ`-algebra homomorphism packaging of a checked extension embedding
is injective. -/
theorem embedAlgHom_injective (hE : E.PreservesEmbedding) :
    Function.Injective (embedAlgHom E hE) :=
  embed_injective E hE

end Extension

end Hex.NumberTower
