/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Vector

public section

/-!
Mathlib algebraic structure on `Hex.Matrix`, transported along `matrixEquiv`.

`matrixEquiv` carries the executable dense-matrix operations to Mathlib's
function-based `Matrix`, so we equip `Hex.Matrix` with the Mathlib algebraic
tower (`AddCommMonoid`, `AddCommGroup`, `Module`, `Semiring`, `Ring`, `Algebra`)
whose operations are the executable ones, and upgrade `matrixEquiv` to the
corresponding additive, linear, ring, and algebra equivalences.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-! ### Preservation of the additive operations -/

@[simp, grind =] theorem matrixEquiv_zero [Zero R] :
    matrixEquiv (0 : Hex.Matrix R n m) = 0 := by
  ext i j
  rw [matrixEquiv_apply, Matrix.zero_apply]
  show (Hex.Matrix.zero n m : Hex.Matrix R n m)[i][j] = 0
  rw [Hex.Matrix.zero, Hex.Matrix.getElem_ofFn]

@[simp, grind =] theorem matrixEquiv_add [Add R] (A B : Hex.Matrix R n m) :
    matrixEquiv (A + B) = matrixEquiv A + matrixEquiv B := by
  ext i j
  simp

@[simp, grind =] theorem matrixEquiv_neg [Neg R] (A : Hex.Matrix R n m) :
    matrixEquiv (-A) = -matrixEquiv A := by
  ext i j
  simp

@[simp, grind =] theorem matrixEquiv_sub [Sub R] (A B : Hex.Matrix R n m) :
    matrixEquiv (A - B) = matrixEquiv A - matrixEquiv B := by
  ext i j
  simp

@[simp, grind =] theorem matrixEquiv_smul {S : Type*} [SMul S R] (c : S) (A : Hex.Matrix R n m) :
    matrixEquiv (c • A) = c • matrixEquiv A := by
  ext i j
  simp

/-- Regression guard: under a Mathlib scalar instance the canonical matrix zero
is the executable `ofFn`-based `Hex.Matrix.zero`, not the core `Vector`
`replicate` zero. The additive tower, `Semiring`, and `matrixEquiv_zero` all
share this zero; this `rfl` fails loudly if instance resolution ever drifts. -/
example [Zero R] : (0 : Hex.Matrix R n m) = Hex.Matrix.zero n m := rfl

/-- `1` on a square matrix is the identity matrix. The instance is here rather than
in `HexMatrix` because the `Semiring`/`Ring` structures transported below need it,
while `HexMatrix` states its own lemmas with `Matrix.identity`. -/
instance instOne [OfNat R 0] [OfNat R 1] : One (Hex.Matrix R n n) := ⟨Hex.Matrix.identity n⟩

/-- Regression guard: `1` on a square matrix is `Matrix.identity`. -/
example [Zero R] [One R] : (1 : Hex.Matrix R n n) = Hex.Matrix.identity n := rfl

/-! ### Additive instances and the additive equivalence -/

instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (Hex.Matrix R n m) :=
  matrixEquiv.injective.addCommMonoid _ matrixEquiv_zero matrixEquiv_add
    (fun _ _ => matrixEquiv_smul _ _)

instance instAddCommGroup [AddCommGroup R] : AddCommGroup (Hex.Matrix R n m) :=
  matrixEquiv.injective.addCommGroup _ matrixEquiv_zero matrixEquiv_add matrixEquiv_neg
    matrixEquiv_sub (fun _ _ => matrixEquiv_smul _ _) (fun _ _ => matrixEquiv_smul _ _)

/-- `matrixEquiv` as an additive equivalence. -/
@[expose]
def matrixAddEquiv [AddCommMonoid R] : Hex.Matrix R n m ≃+ Matrix (Fin n) (Fin m) R :=
  { matrixEquiv with map_add' := matrixEquiv_add }

@[simp] theorem matrixAddEquiv_apply [AddCommMonoid R] (M : Hex.Matrix R n m) :
    matrixAddEquiv M = matrixEquiv M := rfl

/-! ### Module structure and the linear equivalence -/

instance instModule [Semiring R] : Module R (Hex.Matrix R n m) :=
  Function.Injective.module R (M := Matrix (Fin n) (Fin m) R)
    (matrixAddEquiv (R := R) (n := n) (m := m)).toAddMonoidHom
    (fun _ _ h => matrixAddEquiv.injective h)
    (fun c x => matrixEquiv_smul c x)

/-- `matrixEquiv` as an `R`-linear equivalence. -/
@[expose]
def matrixLinearEquiv [Semiring R] : Hex.Matrix R n m ≃ₗ[R] Matrix (Fin n) (Fin m) R :=
  { matrixEquiv with
    map_add' := matrixEquiv_add
    map_smul' := fun c A => matrixEquiv_smul c A }

@[simp] theorem matrixLinearEquiv_apply [Semiring R] (M : Hex.Matrix R n m) :
    matrixLinearEquiv M = matrixEquiv M := rfl

/-! ### Multiplicative preservation -/

@[simp, grind =] theorem matrixEquiv_one [Zero R] [One R] :
    matrixEquiv (1 : Hex.Matrix R n n) = 1 := by
  ext i j
  rw [matrixEquiv_apply]
  show (Hex.Matrix.identity n)[i][j] = _
  rw [Hex.Matrix.getElem_identity, Matrix.one_apply]

@[simp, grind =] theorem matrixEquiv_mul [Semiring R] (A B : Hex.Matrix R n n) :
    matrixEquiv (A * B) = matrixEquiv A * matrixEquiv B := by
  ext i j
  rw [matrixEquiv_apply, Matrix.mul_apply]
  show (Hex.Matrix.mul A B)[i][j] = ∑ k, matrixEquiv A i k * matrixEquiv B k j
  rw [Hex.Matrix.mul, Hex.Matrix.getElem_ofFn, dotProduct_eq]
  unfold dotProduct
  refine Finset.sum_congr rfl (fun k _ => ?_)
  grind

/-! ### Auxiliary operations, pulled back through `matrixEquiv`

These `NatCast`, `IntCast`, and `Pow` instances exist only to populate the
corresponding fields of the `Semiring`/`Ring` structures. They are *proof-facing*:
defined by transport through `matrixEquiv`, not in executable form. Executable
code never goes through them — it uses the `HexMatrix` operations directly (the
square-matrix `*`, the `ofFn` identity). Their transport lemmas below reduce them
to the Mathlib side for `simp`/`grind`. -/

instance instNatCast [Semiring R] : NatCast (Hex.Matrix R n n) :=
  ⟨fun k => matrixEquiv.symm (k : Matrix (Fin n) (Fin n) R)⟩

instance instIntCast [Ring R] : IntCast (Hex.Matrix R n n) :=
  ⟨fun k => matrixEquiv.symm (k : Matrix (Fin n) (Fin n) R)⟩

instance instPow [Semiring R] : Pow (Hex.Matrix R n n) ℕ :=
  ⟨fun M k => matrixEquiv.symm (matrixEquiv M ^ k)⟩

@[simp, grind =] theorem matrixEquiv_natCast [Semiring R] (k : ℕ) :
    matrixEquiv (k : Hex.Matrix R n n) = k :=
  matrixEquiv.apply_symm_apply (k : Matrix (Fin n) (Fin n) R)

@[simp, grind =] theorem matrixEquiv_intCast [Ring R] (k : ℤ) :
    matrixEquiv (k : Hex.Matrix R n n) = k :=
  matrixEquiv.apply_symm_apply (k : Matrix (Fin n) (Fin n) R)

@[simp, grind =] theorem matrixEquiv_pow [Semiring R] (M : Hex.Matrix R n n) (k : ℕ) :
    matrixEquiv (M ^ k) = matrixEquiv M ^ k :=
  matrixEquiv.apply_symm_apply (matrixEquiv M ^ k)

/-! ### Ring structure and the ring equivalence -/

instance instSemiring [Semiring R] : Semiring (Hex.Matrix R n n) :=
  matrixEquiv.injective.semiring _ matrixEquiv_zero matrixEquiv_one matrixEquiv_add
    matrixEquiv_mul (fun _ _ => matrixEquiv_smul _ _) (fun _ _ => matrixEquiv_pow _ _)
    matrixEquiv_natCast

instance instRing [Ring R] : Ring (Hex.Matrix R n n) :=
  matrixEquiv.injective.ring _ matrixEquiv_zero matrixEquiv_one matrixEquiv_add
    matrixEquiv_mul matrixEquiv_neg matrixEquiv_sub (fun _ _ => matrixEquiv_smul _ _)
    (fun _ _ => matrixEquiv_smul _ _) (fun _ _ => matrixEquiv_pow _ _)
    matrixEquiv_natCast matrixEquiv_intCast

/-- `matrixEquiv` as a ring equivalence on square matrices. -/
@[expose]
def matrixRingEquiv [Semiring R] : Hex.Matrix R n n ≃+* Matrix (Fin n) (Fin n) R :=
  { matrixEquiv with map_add' := matrixEquiv_add, map_mul' := matrixEquiv_mul }

@[simp] theorem matrixRingEquiv_apply [Semiring R] (M : Hex.Matrix R n n) :
    matrixRingEquiv M = matrixEquiv M := rfl

/-! ### Algebra structure and the algebra equivalence -/

instance instAlgebra [CommSemiring R] : Algebra R (Hex.Matrix R n n) :=
  Algebra.ofModule
    (fun r A B => matrixEquiv.injective (by simp [smul_mul_assoc]))
    (fun r A B => matrixEquiv.injective (by simp [mul_smul_comm]))

/-- `matrixEquiv` as an `R`-algebra equivalence on square matrices. -/
@[expose]
def matrixAlgEquiv [CommSemiring R] : Hex.Matrix R n n ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  { matrixRingEquiv with
    commutes' := fun r => by
      simp [Algebra.algebraMap_eq_smul_one] }

@[simp] theorem matrixAlgEquiv_apply [CommSemiring R] (M : Hex.Matrix R n n) :
    matrixAlgEquiv M = matrixEquiv M := rfl

end HexMatrixMathlib
