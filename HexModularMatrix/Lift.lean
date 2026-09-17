/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Decomp
public import HexModularMatrix.Product
public import HexDeterminant.Adjugate
public import HexArith.ExactDiv

public section

namespace Hex.Matrix
namespace Dixon

theorem map_get (A : Matrix R n m) (f : R → S) (i : Fin n) (j : Fin m) :
    (A.mapEntries f)[i][j] = f A[i][j] := by
  simpa only [getElem_pair_eq_nested] using getElem_mapEntries A f i j

/-- Matrix multiplication commutes with a coefficient homomorphism. -/
theorem map_mul {R S : Type} [Lean.Grind.CommRing R] [Lean.Grind.CommRing S]
    (A : Matrix R n m) (B : Matrix R m k) (f : R → S)
    (h0 : f 0 = 0) (ha : ∀ x y, f (x + y) = f x + f y)
    (hm : ∀ x y, f (x * y) = f x * f y) :
    (A * B).mapEntries f = A.mapEntries f * B.mapEntries f := by
  apply ext_getElem
  intro i j
  simp only [← getElem_pair_eq_nested, getElem_mapEntries]
  simp only [getElem_pair_eq_nested, getElem_mul, getElem_row, getElem_col,
    Vector.dotProduct]
  simp only [← getElem_pair_eq_nested, getElem_mapEntries]
  symm
  rw [← h0]
  apply List.foldl_hom f
  intro x y
  rw [ha, hm]

/-- Reducing a product modulo the lifting modulus. -/
theorem cast_mul (A : Matrix Int n m) (B : Matrix Int m k)
    (p : Nat) [ZMod64.Bounds p] :
    (A * B).mapEntries (ZMod64.intCast p) =
      A.mapEntries (ZMod64.intCast p) * B.mapEntries (ZMod64.intCast p) :=
  map_mul A B _ Lean.Grind.Ring.intCast_zero
    Lean.Grind.Ring.intCast_add Lean.Grind.Ring.intCast_mul

/-- The next simultaneous Dixon digit, using symmetric representatives. -/
def digit (D : Decomp n) (R : Matrix Int n m) : Matrix Int n m :=
  letI : ZMod64.Bounds D.p := D.bounds
  (Word.mul D.inv (R.mapEntries (ZMod64.intCast D.p))).mapEntries fun x =>
    Modular.symMod (x.toNat : Int) D.p

theorem cast_digit (D : Decomp n) (R : Matrix Int n m) :
    letI : ZMod64.Bounds D.p := D.bounds
    (digit D R).mapEntries (ZMod64.intCast D.p) =
      D.inv * R.mapEntries (ZMod64.intCast D.p) := by
  letI : ZMod64.Bounds D.p := D.bounds
  apply ext_getElem
  intro i j
  simp only [digit, Word.mul_eq, ← getElem_pair_eq_nested, getElem_mapEntries]
  apply ZMod64.ext_toNat
  apply Int.ofNat_inj.mp
  rw [ZMod64.toNat_intCast, Modular.symMod_emod (by have := D.one_lt; omega)]
  exact Int.emod_eq_of_lt (by omega) (by
    have h := (D.inv * R.mapEntries (ZMod64.intCast D.p))[(i, j)].toNat_lt
    omega)

/-- Each residual difference is exactly divisible by the modulus. -/
theorem digit_dvd (D : Decomp n) (R : Matrix Int n m) (i : Fin n) (j : Fin m) :
    (D.p : Int) ∣ R[i][j] - (D.A * digit D R)[i][j] := by
  letI : ZMod64.Bounds D.p := D.bounds
  have h : (D.A * digit D R).mapEntries (ZMod64.intCast D.p) =
      R.mapEntries (ZMod64.intCast D.p) := by
    rw [cast_mul, cast_digit, ← mul_assoc, mul_eq_one_comm D.inv_mul, identity_mul]
  have he := congrArg (fun M : Matrix (ZMod64 D.p) n m =>
    (M[(i, j)].toNat : Int)) h
  simp only [getElem_mapEntries, ZMod64.toNat_intCast] at he
  simp only [getElem_pair_eq_nested] at he
  apply Int.dvd_of_emod_eq_zero
  rw [Int.sub_emod, he, Int.sub_self, Int.zero_emod]

/-- One exact residual update for all right-hand sides. -/
def residual (D : Decomp n) (R : Matrix Int n m) : Matrix Int n m :=
  (R - D.A * digit D R).mapEntries fun x => HexArith.Int.exactDiv x D.p

theorem residual_eq (D : Decomp n) (R : Matrix Int n m) (i : Fin n) (j : Fin m) :
    (D.p : Int) * (residual D R)[i][j] = R[i][j] - (D.A * digit D R)[i][j] := by
  simp only [residual, map_get, getElem_sub, HexArith.Int.exactDiv]
  exact Int.mul_ediv_cancel' (digit_dvd D R i j)

/-- Accumulate digits for every right-hand side through one modular inverse. -/
def liftRaw (D : Decomp n) (R : Matrix Int n m) : Nat → Matrix Int n m
  | 0 => 0
  | k + 1 => digit D R + (D.p : Int) • liftRaw D (residual D R) k

/-- Tail-recursive digit accumulation, sharing each modular product with its
exact residual update. -/
def liftLoop (D : Decomp n) (R : Matrix Int n m) (acc : Matrix Int n m)
    (power : Int) : Nat → Matrix Int n m
  | 0 => acc
  | k + 1 =>
    let c := digit D R
    let next := (R - D.A * c).mapEntries fun x => HexArith.Int.exactDiv x D.p
    liftLoop D next (acc + power • c) (power * D.p) k

theorem liftLoop_eq (D : Decomp n) (R acc : Matrix Int n m) (power : Int) (k : Nat) :
    liftLoop D R acc power k = acc + power • liftRaw D R k := by
  induction k generalizing R acc power with
  | zero =>
    apply ext_getElem
    intro i j
    simp only [liftLoop, liftRaw, getElem_add, smul_getElem, getElem_zero]
    grind only
  | succ k ih =>
    rw [liftLoop, ih, liftRaw]
    change acc + power • digit D R + (power * D.p) • liftRaw D (residual D R) k = _
    apply ext_getElem
    intro i j
    simp only [getElem_add, smul_getElem]
    change acc[i][j] + power * (digit D R)[i][j] +
      (power * D.p) * (liftRaw D (residual D R) k)[i][j] =
      acc[i][j] + power * ((digit D R)[i][j] + D.p * (liftRaw D (residual D R) k)[i][j])
    grind only

def liftFast (D : Decomp n) (R : Matrix Int n m) (k : Nat) : Matrix Int n m :=
  liftLoop D R 0 1 k

@[csimp] theorem liftRaw_eq_fast : @liftRaw = @liftFast := by
  funext n m D R k
  rw [liftFast, liftLoop_eq]
  apply ext_getElem
  intro i j
  simp only [getElem_add, smul_getElem, getElem_zero]
  grind only

/-- Use inverse rows cached outside the lifting loop. -/
def digitRows (D : Decomp n) (rows : Vector (Vector (@ZMod64 D.p D.bounds) n) n)
    (R : Matrix Int n m) : Matrix Int n m :=
  letI : ZMod64.Bounds D.p := D.bounds
  (Word.mulRows rows (R.mapEntries (ZMod64.intCast D.p))).mapEntries fun x =>
    Modular.symMod (x.toNat : Int) D.p

theorem digitRows_eq (D : Decomp n) (R : Matrix Int n m) :
    digitRows D (Vector.ofFn D.inv.row) R = digit D R := by
  rfl

/-- Sparse integer products and inverse rows are shared across lifting steps. -/
def liftSparseLoop (D : Decomp n) (indices : Vector (List (Fin n)) n)
    (rows : Vector (Vector (@ZMod64 D.p D.bounds) n) n)
    (R acc : Matrix Int n m) (power : Int) : Nat → Matrix Int n m
  | 0 => acc
  | k + 1 =>
    let c := digitRows D rows R
    let next := (R - Sparse.mul D.A indices c).mapEntries fun x =>
      HexArith.Int.exactDiv x D.p
    liftSparseLoop D indices rows next (acc + power • c) (power * D.p) k

theorem liftSparseLoop_eq (D : Decomp n) (R acc : Matrix Int n m)
    (power : Int) (k : Nat) :
    liftSparseLoop D (Sparse.support D.A) (Vector.ofFn D.inv.row) R acc power k =
      liftLoop D R acc power k := by
  induction k generalizing R acc power with
  | zero => rfl
  | succ k ih => simp only [liftSparseLoop, liftLoop, digitRows_eq, Sparse.mul_eq, ih]

def liftSparse (D : Decomp n) (R : Matrix Int n m) (k : Nat) : Matrix Int n m :=
  liftSparseLoop D (Sparse.support D.A) (Vector.ofFn D.inv.row) R 0 1 k

@[csimp] theorem liftFast_eq_sparse : @liftFast = @liftSparse := by
  funext n m D R k
  exact (liftSparseLoop_eq D R 0 1 k).symm

/-- Simultaneous lifting with nonnegative representatives at the requested precision. -/
def liftMat (D : Decomp n) (R : Matrix Int n m) (k : Nat) : Matrix Int n m :=
  let modulus := (D.p : Int) ^ k
  (liftRaw D R k).mapEntries fun x => x % modulus

theorem mul_scale (A : Matrix Int n m) (B : Matrix Int m k) (c : Int) :
    A * (c • B) = c • (A * B) := by
  apply ext_getElem
  intro i j
  have hc : (c • B).col j = c • B.col j := by
    ext t ht
    change ((c • B).col j)[(⟨t, ht⟩ : Fin m)] = (c • B.col j)[(⟨t, ht⟩ : Fin m)]
    rw [getElem_col, smul_getElem]
    simp only [Fin.getElem_fin, Vector.getElem_smul]
    exact congrArg (fun x : Int => c * x) (getElem_col B j ⟨t, ht⟩).symm
  rw [smul_getElem, getElem_mul, getElem_mul, hc, Vector.dotProduct_smul_right]
  rfl

/-- The accumulated digits solve the system modulo the requested power. -/
theorem liftRaw_dvd (D : Decomp n) (R : Matrix Int n m) (k : Nat)
    (i : Fin n) (j : Fin m) :
    (D.p : Int) ^ k ∣ (D.A * liftRaw D R k)[i][j] - R[i][j] := by
  induction k generalizing R with
  | zero => simp
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih (residual D R)
    have hr := residual_eq D R i j
    refine ⟨q, ?_⟩
    rw [liftRaw, mul_add, mul_scale, getElem_add, smul_getElem, Int.pow_succ]
    change (D.A * digit D R)[i][j] + (D.p : Int) *
      (D.A * liftRaw D (residual D R) k)[i][j] - R[i][j] = _
    grind only

/-- Multiplication preserves entrywise congruence. -/
theorem mul_dvd (A : Matrix Int n m) (B C : Matrix Int m k) (q : Int)
    (h : ∀ (i : Fin m) (j : Fin k), q ∣ B[i][j] - C[i][j]) (i : Fin n) (j : Fin k) :
    q ∣ (A * B)[i][j] - (A * C)[i][j] := by
  simp only [getElem_mul, Vector.dotProduct, getElem_row, getElem_col]
  have go (xs : List (Fin m)) (a b : Int) (hab : q ∣ a - b) :
      q ∣ xs.foldl (fun a t => a + A[i][t] * B[t][j]) a -
        xs.foldl (fun b t => b + A[i][t] * C[t][j]) b := by
    induction xs generalizing a b with
    | nil => exact hab
    | cons t xs ih =>
      apply ih
      have ht : q ∣ A[i][t] * (B[t][j] - C[t][j]) := Int.dvd_mul_of_dvd_right (h t j)
      have hs := Int.dvd_add hab ht
      have heq : a + A[i][t] * B[t][j] - (b + A[i][t] * C[t][j]) =
          (a - b) + A[i][t] * (B[t][j] - C[t][j]) := by grind only
      rw [heq]
      exact hs
  exact go _ 0 0 (by simp)

theorem liftMat_spec (D : Decomp n) (R : Matrix Int n m) (k : Nat)
    (i : Fin n) (j : Fin m) :
    ((D.A * liftMat D R k)[i][j] - R[i][j]) % ((D.p : Int) ^ k) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  have hnorm := mul_dvd D.A (liftMat D R k) (liftRaw D R k) ((D.p : Int) ^ k)
    (fun i j => by
      simp only [liftMat, map_get]
      apply Int.dvd_of_emod_eq_zero
      rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod]) i j
  have h := Int.dvd_add hnorm (liftRaw_dvd D R k i j)
  have heq : (D.A * liftMat D R k)[i][j] - R[i][j] =
      ((D.A * liftMat D R k)[i][j] - (D.A * liftRaw D R k)[i][j]) +
        ((D.A * liftRaw D R k)[i][j] - R[i][j]) := by omega
  rw [heq]
  exact h

theorem mul_zero {R : Type} [Lean.Grind.CommRing R] (A : Matrix R n m) :
    A * (0 : Matrix R m k) = 0 := by
  apply ext_getElem
  intro i j
  simp only [getElem_mul, Vector.dotProduct, getElem_col, getElem_zero,
    Lean.Grind.Semiring.mul_zero]
  exact List.foldl_add_eq_self _ _ _ (by simp)

/-- The modular inverse cancels the matrix modulo its base modulus. -/
theorem cancel_base (D : Decomp n) (B : Matrix Int n m)
    (h : ∀ (i : Fin n) (j : Fin m), (D.p : Int) ∣ (D.A * B)[i][j]) :
    ∀ (i : Fin n) (j : Fin m), (D.p : Int) ∣ B[i][j] := by
  letI : ZMod64.Bounds D.p := D.bounds
  have hz : (D.A * B).mapEntries (ZMod64.intCast D.p) = 0 := by
    apply ext_getElem
    intro i j
    rw [map_get, getElem_zero]
    apply ZMod64.ext_toNat
    apply Int.ofNat_inj.mp
    rw [ZMod64.toNat_intCast]
    change (D.A * B)[i][j] % (D.p : Int) = 0
    exact Int.emod_eq_zero_of_dvd (h i j)
  rw [cast_mul] at hz
  have hb : B.mapEntries (ZMod64.intCast D.p) = 0 := by
    calc B.mapEntries (ZMod64.intCast D.p)
        = Matrix.identity n * B.mapEntries (ZMod64.intCast D.p) := (identity_mul _).symm
      _ = D.inv * (D.A.mapEntries (ZMod64.intCast D.p) * B.mapEntries (ZMod64.intCast D.p)) := by
        rw [← mul_assoc, D.inv_mul]
      _ = 0 := by rw [hz, mul_zero]
  intro i j
  have he := congrArg (fun M : Matrix (ZMod64 D.p) n m => (M[i][j].toNat : Int)) hb
  simp only [map_get, getElem_zero, ZMod64.toNat_intCast] at he
  exact Int.dvd_of_emod_eq_zero he

/-- Invertibility modulo `p` suffices to cancel the matrix modulo every `p^k`. -/
theorem cancel_power (D : Decomp n) (B : Matrix Int n m) (k : Nat)
    (h : ∀ (i : Fin n) (j : Fin m), (D.p : Int) ^ k ∣ (D.A * B)[i][j]) :
    ∀ (i : Fin n) (j : Fin m), (D.p : Int) ^ k ∣ B[i][j] := by
  induction k generalizing B with
  | zero => simp
  | succ k ih =>
    have hp : (D.p : Int) ≠ 0 := by have := D.one_lt; omega
    have hbase : ∀ (i : Fin n) (j : Fin m), (D.p : Int) ∣ B[i][j] := by
      apply cancel_base D B
      intro i j
      apply Int.dvd_trans ?_ (h i j)
      exact ⟨(D.p : Int) ^ k, by rw [Int.pow_succ, Int.mul_comm]⟩
    let C := B.mapEntries fun x => x / (D.p : Int)
    have hc : B = (D.p : Int) • C := by
      apply ext_getElem
      intro i j
      simp only [C, smul_getElem, map_get]
      exact (Int.mul_ediv_cancel' (hbase i j)).symm
    have hnext : ∀ (i : Fin n) (j : Fin m), (D.p : Int) ^ k ∣ (D.A * C)[i][j] := by
      intro i j
      obtain ⟨t, ht⟩ := h i j
      rw [hc, mul_scale, smul_getElem] at ht
      change (D.p : Int) * (D.A * C)[i][j] = (D.p : Int) ^ (k + 1) * t at ht
      refine ⟨t, Int.eq_of_mul_eq_mul_left hp ?_⟩
      change (D.p : Int) * (D.A * C)[i][j] = (D.p : Int) * ((D.p : Int) ^ k * t)
      rw [ht, Int.pow_succ]
      grind only
    intro i j
    obtain ⟨t, ht⟩ := ih C hnext i j
    refine ⟨t, ?_⟩
    rw [hc, smul_getElem, ht, Int.pow_succ]
    change (D.p : Int) * ((D.p : Int) ^ k * t) = ((D.p : Int) ^ k * D.p) * t
    grind only

end Dixon

/-- The solution modulo `p^k`, with nonnegative coordinate representatives. -/
def Decomp.lift (D : Decomp n) (b : Vector Int n) (k : Nat) : Vector Int n :=
  (Dixon.liftMat D (Matrix.ofFn fun i (_ : Fin 1) => b[i]) k).col 0

theorem Decomp.lift_spec (D : Decomp n) (b : Vector Int n) (k : Nat) :
    ∀ i : Fin n, ((D.A.mulVec (D.lift b k))[i] - b[i]) % ((D.p : Int) ^ k) = 0 := by
  intro i
  change ((D.A * (D.lift b k))[i] - b[i]) % ((D.p : Int) ^ k) = 0
  have h := Dixon.liftMat_spec D (Matrix.ofFn fun i (_ : Fin 1) => b[i]) k i 0
  simpa only [Decomp.lift, getElem_mulVec, getElem_mul, getElem_ofFn] using h

end Hex.Matrix
