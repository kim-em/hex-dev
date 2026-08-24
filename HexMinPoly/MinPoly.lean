/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMinPoly.Lcm

public section

/-! The executable matrix minimal polynomial. -/

namespace Hex.Matrix

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F] {n : Nat}

/-- The monic generator of the polynomials annihilating `A`, computed as the
least common multiple of the order polynomials of every standard basis vector. -/
@[expose]
def minPoly (A : Matrix F n n) : DensePoly F :=
  basisOrderLcm A

private theorem monic_ne_zero {p : DensePoly F} (hp : p.Monic) : p ≠ 0 := by
  intro h
  rw [h, DensePoly.monic_iff_leadingCoeff_eq_one,
    DensePoly.leadingCoeff_zero] at hp
  exact Lean.Grind.Field.zero_ne_one hp

/-- The computed matrix minimal polynomial is monic, including for the empty
matrix where it is `1`. -/
theorem minPoly_monic (A : Matrix F n n) : (minPoly A).Monic := by
  unfold minPoly basisOrderLcm
  apply DensePoly.lcmList_monic
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact monic_ne_zero (vecMinPoly_monic A (basisVec n i))

/-- A multiple of a polynomial annihilating a vector also annihilates that
vector. -/
theorem evalVec_of_dvd {q p : DensePoly F} (A : Matrix F n n)
    (v : Vector F n) (hdvd : q ∣ p) (heval : evalVec q A v = 0) :
    evalVec p A v = 0 := by
  rcases hdvd with ⟨r, hr⟩
  rw [hr, DensePoly.mul_comm_poly, evalVec_mul, heval, evalVec_zero]

omit [DecidableEq F] in
private theorem foldl_basisVec (v : Vector F n) :
    (List.finRange n).foldl
        (fun acc i => acc + v[i] • basisVec n i) (0 : Vector F n) = v := by
  have hmat : Matrix.ofRows (Matrix.rows (Matrix.identity (R := F) n)) =
      Matrix.identity (R := F) n := by
    apply Matrix.ext
    rw [Matrix.rows_ofRows]
  calc
    (List.finRange n).foldl
        (fun acc i => acc + v[i] • basisVec n i) (0 : Vector F n) =
        (List.finRange n).foldl
          (fun acc i => acc + v[i] • (Matrix.rows (Matrix.identity (R := F) n))[i])
            (0 : Vector F n) := by
      apply List.foldl_add_congr
      intro i hi
      congr 1
      unfold basisVec Matrix.row
      change Matrix.getRow (Matrix.identity (R := F) n) i =
        (Matrix.rows (Matrix.identity (R := F) n))[i.val]
      rw [Matrix.getElem_rows]
    _ = Matrix.vecMul v
        (Matrix.ofRows (Matrix.rows (Matrix.identity (R := F) n))) := by
      exact (Matrix.vecMul_ofRows v _).symm
    _ = v := by rw [hmat, Matrix.vecMul_identity]

/-- A polynomial annihilates every vector exactly when it annihilates every
standard basis vector. -/
theorem evalVec_eq_zero_iff (A : Matrix F n n) (p : DensePoly F) :
    (∀ v, evalVec p A v = 0) ↔
      ∀ i : Fin n, evalVec p A (basisVec n i) = 0 := by
  constructor
  · intro h i
    exact h (basisVec n i)
  · intro h v
    rw [← foldl_basisVec v, evalVec_foldl_add, evalVec_zero]
    generalize List.finRange n = xs
    induction xs with
    | nil => rfl
    | cons i xs ih =>
        simp only [List.foldl_cons]
        have hterm : evalVec p A (v[i] • basisVec n i) = 0 := by
          rw [evalVec_smul, h i]
          ext j hj
          simp only [Vector.getElem_smul, Vector.getElem_zero]
          change v[i] * 0 = 0
          grind
        rw [hterm]
        have hzero (acc : Vector F n) : acc + 0 = acc := by
          ext j hj
          simp only [Vector.getElem_add, Vector.getElem_zero]
          grind
        rw [hzero]
        exact ih

/-- The minimal polynomial annihilates every vector. -/
theorem evalVec_minPoly (A : Matrix F n n) (v : Vector F n) :
    evalVec (minPoly A) A v = 0 := by
  have hall : ∀ w, evalVec (minPoly A) A w = 0 :=
    (evalVec_eq_zero_iff A (minPoly A)).2 (by
      intro i
      apply evalVec_of_dvd (q := vecMinPoly A (basisVec n i)) A (basisVec n i)
      · unfold minPoly basisOrderLcm
        apply DensePoly.dvd_lcmList_of_mem
        simp
      · exact evalVec_vecMinPoly A (basisVec n i))
  exact hall v

/-- The minimal polynomial divides every polynomial annihilating all vectors. -/
theorem minPoly_dvd (A : Matrix F n n) (p : DensePoly F) :
    (∀ v, evalVec p A v = 0) → minPoly A ∣ p := by
  intro hp
  unfold minPoly basisOrderLcm
  apply DensePoly.lcmList_dvd
  intro q hq
  rcases List.mem_map.mp hq with ⟨i, _, rfl⟩
  exact vecMinPoly_dvd A (basisVec n i) p (hp (basisVec n i))

/-- A polynomial is a multiple of the minimal polynomial exactly when it
annihilates every vector. -/
theorem minPoly_dvd_iff (A : Matrix F n n) (p : DensePoly F) :
    minPoly A ∣ p ↔ ∀ v, evalVec p A v = 0 := by
  constructor
  · intro hp v
    exact evalVec_of_dvd A v hp (evalVec_minPoly A v)
  · exact minPoly_dvd A p

@[simp, grind =]
theorem minPoly_empty (A : Matrix F 0 0) : minPoly A = 1 := rfl

end Hex.Matrix
