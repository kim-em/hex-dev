/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Correct.Core
import Batteries.Data.Vector.Lemmas

public section

/-! Transform, inverse, compact-diagonal, and public Smith correctness. -/

namespace Hex.Matrix
namespace Smith

/-- The transform accumulator maps the original matrix to the current working
matrix on both sides. -/
private def TransformsInput (A : Matrix Int n m)
    (s : Result (Transforms n m) n m) : Prop :=
  s.accumulator.left * A * s.accumulator.right = s.matrix

private theorem swapRows_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s) (i k : Fin n) :
    TransformsInput A (swapRows (transformAccumulator n m) s i k) := by
  rw [swapRows]
  split
  · exact h
  · change Matrix.rowSwap s.accumulator.left i k * A * s.accumulator.right =
      Matrix.rowSwap s.matrix i k
    rw [Matrix.rowSwap_mul, Matrix.rowSwap_mul, h]

private theorem swapCols_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s) (i k : Fin m) :
    TransformsInput A (swapCols (transformAccumulator n m) s i k) := by
  rw [swapCols]
  split
  · exact h
  · change s.accumulator.left * A * Matrix.colSwap s.accumulator.right i k =
      Matrix.colSwap s.matrix i k
    rw [Hermite.mul_colSwap, h]

private theorem clearColumn_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (pivotRow row : Fin n) (pivotCol : Fin m) :
    TransformsInput A
      (clearColumn (transformAccumulator n m) s pivotRow row pivotCol) := by
  rw [clearColumn]
  split
  · change Matrix.rowAdd s.accumulator.left pivotRow row _ * A *
        s.accumulator.right = Matrix.rowAdd s.matrix pivotRow row _
    rw [Matrix.rowAdd_mul, Matrix.rowAdd_mul, h]
  · change Hermite.combineRows s.accumulator.left pivotRow row _ _ _ _ * A *
        s.accumulator.right = Hermite.combineRows s.matrix pivotRow row _ _ _ _
    unfold Hermite.gcdCoeffs HexArith.Int.extGcd Hex.pureIntExtGcd
    rw [Hermite.combineRows_mul, Hermite.combineRows_mul, h]

private theorem clearRow_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (pivotRow : Fin n) (pivotCol col : Fin m) :
    TransformsInput A
      (clearRow (transformAccumulator n m) s pivotRow pivotCol col) := by
  rw [clearRow]
  split
  · change s.accumulator.left * A *
        Matrix.colAdd s.accumulator.right pivotCol col _ =
          Matrix.colAdd s.matrix pivotCol col _
    rw [Matrix.mul_colAdd, h]
  · change s.accumulator.left * A *
        Hermite.combineCols s.accumulator.right pivotCol col _ _ _ _ =
          Hermite.combineCols s.matrix pivotCol col _ _ _ _
    unfold Hermite.gcdCoeffs HexArith.Int.extGcd Hex.pureIntExtGcd
    rw [Hermite.mul_combineCols, h]

private theorem repair_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (pivotRow row : Fin n) (pivotCol col : Fin m) :
    TransformsInput A
      (repair (transformAccumulator n m) s pivotRow row pivotCol col) := by
  change Matrix.rowAdd s.accumulator.left row pivotRow 1 * A *
      Hermite.combineCols s.accumulator.right pivotCol col _ _ _ _ =
    Hermite.combineCols (Matrix.rowAdd s.matrix row pivotRow 1) pivotCol col _ _ _ _
  rw [Matrix.rowAdd_mul, Hermite.mul_combineCols, Matrix.rowAdd_mul, h]

private theorem negateRow_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (row : Fin n) :
    TransformsInput A
      { s with
        matrix := Matrix.rowScale s.matrix row (-1)
        accumulator := (transformAccumulator n m).rowNegate s.accumulator row } := by
  change Matrix.rowScale s.accumulator.left row (-1) * A * s.accumulator.right =
    Matrix.rowScale s.matrix row (-1)
  rw [Matrix.rowScale_mul, Matrix.rowScale_mul, h]

private theorem reduceFuel_transforms (A : Matrix Int n m)
    (pivotRow : Fin n) (pivotCol : Fin m) (fuel : Nat)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s) :
    TransformsInput A
      (reduceFuel (transformAccumulator n m) pivotRow pivotCol fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [reduceFuel]
      split
      · exact h
      · split
        · exact ih (clearColumn_transforms A h pivotRow _ pivotCol)
        · split
          · exact ih (clearRow_transforms A h pivotRow pivotCol _)
          · split
            · have hneg := negateRow_transforms A h pivotRow
              simp only
              split
              · exact hneg
              · exact ih (repair_transforms A hneg pivotRow _ pivotCol _)
            · split
              · exact h
              · exact ih (repair_transforms A h pivotRow _ pivotCol _)

private theorem reduce_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (pivotRow : Fin n) (pivotCol : Fin m) :
    TransformsInput A (reduce (transformAccumulator n m) s pivotRow pivotCol) := by
  exact reduceFuel_transforms A pivotRow pivotCol _ h

private theorem runFuel_transforms (A : Matrix Int n m) (fuel : Nat)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s) :
    TransformsInput A (runFuel (transformAccumulator n m) fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [runFuel]
      split
      · split
        · split
          · exact h
          · simp only
            rename_i hn hm _ q _
            let pivotRow : Fin n := ⟨s.diag.length, by assumption⟩
            let pivotCol : Fin m := ⟨s.diag.length, by assumption⟩
            have hmoved := swapCols_transforms A
              (swapRows_transforms A h pivotRow q.1) pivotCol q.2
            have hreduced := reduce_transforms A hmoved pivotRow pivotCol
            split
            · exact hreduced
            · exact ih hreduced
        · exact h
      · exact h

/-- The full-data sweep's accumulated left and right transforms carry the
input to its final working matrix. -/
theorem run_transform (A : Matrix Int n m) :
    let s := run (transformAccumulator n m) A
    s.accumulator.left * A * s.accumulator.right = s.matrix := by
  apply runFuel_transforms A
  change Matrix.identity (R := Int) n * A * Matrix.identity m = A
  rw [Matrix.identity_mul, Matrix.mul_identity]

/-- Both explicitly accumulated inverse matrices remain right inverses. -/
private def HasInverses (s : Result (Transforms n m) n m) : Prop :=
  s.accumulator.left * s.accumulator.leftInv = Matrix.identity n ∧
    s.accumulator.right * s.accumulator.rightInv = Matrix.identity m

private theorem preserveRightInverse (R X F G : Matrix Int n n)
    (hRX : R * X = Matrix.identity n) (hFG : F * G = Matrix.identity n) :
    (R * F) * (G * X) = Matrix.identity n := by
  calc
    (R * F) * (G * X) = (R * (F * G)) * X := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F G X,
        ← Matrix.mul_assoc R (F * G) X]
    _ = R * X := by rw [hFG, Matrix.mul_identity]
    _ = Matrix.identity n := hRX

private theorem swapRows_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (i k : Fin n) :
    HasInverses (swapRows (transformAccumulator n m) s i k) := by
  rw [swapRows]
  split
  · exact h
  · constructor
    · change Matrix.rowSwap s.accumulator.left i k *
          Matrix.colSwap s.accumulator.leftInv i k = Matrix.identity n
      rw [Matrix.rowSwap_mul, Hermite.mul_colSwap, h.1,
        Hermite.swap_inverse_identity]
    · exact h.2

private theorem swapCols_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (i k : Fin m) :
    HasInverses (swapCols (transformAccumulator n m) s i k) := by
  rw [swapCols]
  split
  · exact h
  · constructor
    · exact h.1
    · apply mul_eq_one_comm
      have hrev := mul_eq_one_comm h.2
      change Matrix.rowSwap s.accumulator.rightInv i k *
          Matrix.colSwap s.accumulator.right i k = Matrix.identity m
      rw [Matrix.rowSwap_mul, Hermite.mul_colSwap, hrev,
        Hermite.swap_inverse_identity]

private theorem clearColumn_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (pivotRow row : Fin n) (pivotCol : Fin m)
    (hne : pivotRow ≠ row) (hb : s.matrix[(row, pivotCol)] ≠ 0) :
    HasInverses
      (clearColumn (transformAccumulator n m) s pivotRow row pivotCol) := by
  rw [clearColumn]
  split
  · constructor
    · change Matrix.rowAdd s.accumulator.left pivotRow row _ *
          Matrix.colAdd s.accumulator.leftInv row pivotRow (-_) = Matrix.identity n
      rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h.1]
      exact Hermite.add_inverse_identity pivotRow row hne _
    · exact h.2
  · let a := s.matrix[(pivotRow, pivotCol)]
    let b := s.matrix[(row, pivotCol)]
    rcases hc : Hermite.gcdCoeffs a b with ⟨x, y, z, w⟩
    have hdet := Hermite.gcdCoeffs_det (a := a) (b := b) hb
    rw [hc] at hdet
    dsimp only at hdet
    constructor
    · change Hermite.combineRows s.accumulator.left pivotRow row x y z w *
          Hermite.combineCols s.accumulator.leftInv pivotRow row w (-z) (-y) x =
            Matrix.identity n
      rw [Hermite.combineRows_mul, Hermite.mul_combineCols, h.1]
      exact Hermite.combine_inverse_identity pivotRow row hne x y z w hdet
    · exact h.2

set_option maxHeartbeats 800000 in
private theorem clearRow_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (pivotRow : Fin n) (pivotCol col : Fin m)
    (hne : pivotCol ≠ col) (hb : s.matrix[(pivotRow, col)] ≠ 0) :
    HasInverses
      (clearRow (transformAccumulator n m) s pivotRow pivotCol col) := by
  rw [clearRow]
  split
  · constructor
    · exact h.1
    · let c := -(HexArith.Int.exactDiv
          s.matrix[(pivotRow, col)] s.matrix[(pivotRow, pivotCol)])
      let F := Matrix.colAdd (Matrix.identity (R := Int) m) pivotCol col c
      let G := Matrix.rowAdd (Matrix.identity (R := Int) m) col pivotCol (-c)
      have hcancel : F * G = Matrix.identity m := by
        apply mul_eq_one_comm
        dsimp [F, G]
        rw [Matrix.rowAdd_mul, Matrix.identity_mul]
        simpa using Hermite.add_inverse_identity col pivotCol (Ne.symm hne) (-c)
      have hF : Matrix.colAdd s.accumulator.right pivotCol col c =
          s.accumulator.right * F := by
        dsimp [F]
        rw [Matrix.mul_colAdd, Matrix.mul_identity]
      have hG : Matrix.rowAdd s.accumulator.rightInv col pivotCol (-c) =
          G * s.accumulator.rightInv := by
        dsimp [G]
        rw [Matrix.rowAdd_mul, Matrix.identity_mul]
      change Matrix.colAdd s.accumulator.right pivotCol col c *
          Matrix.rowAdd s.accumulator.rightInv col pivotCol (-c) = Matrix.identity m
      rw [hF, hG]
      exact preserveRightInverse _ _ _ _ h.2 hcancel
  · let a := s.matrix[(pivotRow, pivotCol)]
    let b := s.matrix[(pivotRow, col)]
    rcases hc : Hermite.gcdCoeffs a b with ⟨x, y, z, w⟩
    have hdet := Hermite.gcdCoeffs_det (a := a) (b := b) hb
    rw [hc] at hdet
    dsimp only at hdet
    have hdetInv : w * x - (-z) * (-y) = 1 := by grind
    constructor
    · exact h.1
    · let F := Hermite.combineCols (Matrix.identity (R := Int) m)
          pivotCol col x y z w
      let G := Hermite.combineRows (Matrix.identity (R := Int) m)
          pivotCol col w (-z) (-y) x
      have hcancel : F * G = Matrix.identity m := by
        apply mul_eq_one_comm
        dsimp [F, G]
        rw [Hermite.combineRows_mul, Matrix.identity_mul]
        simpa using Hermite.combine_inverse_identity pivotCol col hne
          w (-z) (-y) x hdetInv
      have hF : Hermite.combineCols s.accumulator.right pivotCol col x y z w =
          s.accumulator.right * F := by
        dsimp [F]
        rw [Hermite.mul_combineCols, Matrix.mul_identity]
      have hG : Hermite.combineRows s.accumulator.rightInv pivotCol col w (-z) (-y) x =
          G * s.accumulator.rightInv := by
        dsimp [G]
        rw [Hermite.combineRows_mul, Matrix.identity_mul]
      change Hermite.combineCols s.accumulator.right pivotCol col x y z w *
          Hermite.combineRows s.accumulator.rightInv pivotCol col w (-z) (-y) x =
            Matrix.identity m
      rw [hF, hG]
      exact preserveRightInverse _ _ _ _ h.2 hcancel

private theorem negateRow_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (row : Fin n) :
    HasInverses
      { s with
        matrix := Matrix.rowScale s.matrix row (-1)
        accumulator := (transformAccumulator n m).rowNegate s.accumulator row } := by
  constructor
  · change Matrix.rowScale s.accumulator.left row (-1) *
        Matrix.colScale s.accumulator.leftInv row (-1) = Matrix.identity n
    rw [Matrix.rowScale_mul, Hermite.mul_colScale, h.1,
      Hermite.negate_inverse_identity]
  · exact h.2

set_option maxHeartbeats 800000 in
private theorem repair_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (pivotRow row : Fin n) (pivotCol col : Fin m)
    (hrow : pivotRow ≠ row) (hcol : pivotCol ≠ col)
    (hb : (Matrix.rowAdd s.matrix row pivotRow 1)[(pivotRow, col)] ≠ 0) :
    HasInverses
      (repair (transformAccumulator n m) s pivotRow row pivotCol col) := by
  rw [repair]
  let matrix := Matrix.rowAdd s.matrix row pivotRow 1
  let a := matrix[(pivotRow, pivotCol)]
  let b := matrix[(pivotRow, col)]
  rcases hc : Hermite.gcdCoeffs a b with ⟨x, y, z, w⟩
  have hdet := Hermite.gcdCoeffs_det (a := a) (b := b) hb
  rw [hc] at hdet
  dsimp only at hdet
  have hdetInv : w * x - (-z) * (-y) = 1 := by grind
  simp only
  constructor
  · change Matrix.rowAdd s.accumulator.left row pivotRow 1 *
        Matrix.colAdd s.accumulator.leftInv pivotRow row (-1) = Matrix.identity n
    rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h.1]
    exact Hermite.add_inverse_identity row pivotRow (Ne.symm hrow) 1
  · let F := Hermite.combineCols (Matrix.identity (R := Int) m)
        pivotCol col x y z w
    let G := Hermite.combineRows (Matrix.identity (R := Int) m)
        pivotCol col w (-z) (-y) x
    have hcancel : F * G = Matrix.identity m := by
      apply mul_eq_one_comm
      dsimp [F, G]
      rw [Hermite.combineRows_mul, Matrix.identity_mul]
      simpa using Hermite.combine_inverse_identity pivotCol col hcol
        w (-z) (-y) x hdetInv
    have hF : Hermite.combineCols s.accumulator.right pivotCol col x y z w =
        s.accumulator.right * F := by
      dsimp [F]
      rw [Hermite.mul_combineCols, Matrix.mul_identity]
    have hG : Hermite.combineRows s.accumulator.rightInv pivotCol col w (-z) (-y) x =
        G * s.accumulator.rightInv := by
      dsimp [G]
      rw [Hermite.combineRows_mul, Matrix.identity_mul]
    change Hermite.combineCols s.accumulator.right pivotCol col x y z w *
        Hermite.combineRows s.accumulator.rightInv pivotCol col w (-z) (-y) x =
      Matrix.identity m
    rw [hF, hG]
    exact preserveRightInverse _ _ _ _ h.2 hcancel

set_option maxHeartbeats 800000 in
private theorem reduceFuel_inverses (pivotRow : Fin n) (pivotCol : Fin m)
    (fuel : Nat) {s : Result (Transforms n m) n m} (h : HasInverses s) :
    HasInverses
      (reduceFuel (transformAccumulator n m) pivotRow pivotCol fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [reduceFuel]
      split
      · exact h
      · split
        · rename_i row hfind
          have hs := findColumn?_some hfind
          exact ih (clearColumn_inverses h pivotRow row pivotCol
            (by intro heq; subst row; omega) hs.2)
        · rename_i hcolumn
          split
          · rename_i col hfind
            have hs := findRow?_some hfind
            exact ih (clearRow_inverses h pivotRow pivotCol col
              (by intro heq; subst col; omega) hs.2)
          · rename_i hrow
            split
            · have hneg := negateRow_inverses h pivotRow
              simp only
              split
              · exact hneg
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hrowNe : pivotRow ≠ q.1 := by
                  intro heq
                  have := congrArg Fin.val heq
                  omega
                have hcolNe : pivotCol ≠ q.2 := by
                  intro heq
                  have := congrArg Fin.val heq
                  omega
                have hzero := findRow?_none hrow q.2 hs.2.1
                let normalized := Matrix.rowScale s.matrix pivotRow (-1)
                have hzero' : normalized[pivotRow][q.2] = 0 := by
                  dsimp only [normalized]
                  rw [Matrix.getElem_rowScale, if_pos rfl]
                  have hz : s.matrix[pivotRow][q.2] = 0 := by
                    simpa only [Matrix.getElem_pair_eq_nested] using hzero
                  rw [hz]
                  omega
                have hsource : normalized[(q.1, q.2)] ≠ 0 := by
                  intro hz
                  rw [hz, Int.zero_emod] at hs
                  exact hs.2.2 rfl
                let repairedMatrix := Matrix.rowAdd normalized q.1 pivotRow 1
                have hb : repairedMatrix[(pivotRow, q.2)] ≠ 0 := by
                  dsimp only [repairedMatrix]
                  rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd,
                    if_pos rfl, hzero']
                  simpa using hsource
                exact ih (repair_inverses hneg pivotRow q.1 pivotCol q.2
                  hrowNe hcolNe hb)
            · split
              · exact h
              · rename_i q hbad
                have hs := findBad?_some hbad
                have hrowNe : pivotRow ≠ q.1 := by
                  intro heq
                  have := congrArg Fin.val heq
                  omega
                have hcolNe : pivotCol ≠ q.2 := by
                  intro heq
                  have := congrArg Fin.val heq
                  omega
                have hzero := findRow?_none hrow q.2 hs.2.1
                have hzero' : s.matrix[pivotRow][q.2] = 0 := by
                  simpa only [Matrix.getElem_pair_eq_nested] using hzero
                have hsource : s.matrix[(q.1, q.2)] ≠ 0 := by
                  intro hz
                  rw [hz, Int.zero_emod] at hs
                  exact hs.2.2 rfl
                have hb : (Matrix.rowAdd s.matrix q.1 pivotRow 1)[(pivotRow, q.2)] ≠ 0 := by
                  rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd, if_pos rfl, hzero']
                  simpa using hsource
                exact ih (repair_inverses h pivotRow q.1 pivotCol q.2
                  hrowNe hcolNe hb)

private theorem reduce_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (pivotRow : Fin n) (pivotCol : Fin m) :
    HasInverses (reduce (transformAccumulator n m) s pivotRow pivotCol) := by
  exact reduceFuel_inverses pivotRow pivotCol _ h

set_option maxHeartbeats 800000 in
private theorem runFuel_inverses (fuel : Nat)
    {s : Result (Transforms n m) n m} (h : HasInverses s) :
    HasInverses (runFuel (transformAccumulator n m) fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [runFuel]
      split
      · split
        · split
          · exact h
          · simp only
            rename_i hn hm _ q _
            let pivotRow : Fin n := ⟨s.diag.length, hn⟩
            let pivotCol : Fin m := ⟨s.diag.length, hm⟩
            have hmoved := swapCols_inverses
              (swapRows_inverses h pivotRow q.1) pivotCol q.2
            have hreduced := reduce_inverses hmoved pivotRow pivotCol
            split
            · exact hreduced
            · exact ih hreduced
        · exact h
      · exact h

/-- The full Smith run preserves both explicit inverse products. -/
theorem run_inverses (A : Matrix Int n m) :
    let s := run (transformAccumulator n m) A
    s.accumulator.left * s.accumulator.leftInv = Matrix.identity n ∧
      s.accumulator.right * s.accumulator.rightInv = Matrix.identity m := by
  apply runFuel_inverses
  constructor <;> exact Matrix.identity_mul _

private theorem rowAdd_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (src dst : Fin n) (c : Int) :
    TransformsInput A
      { s with
        matrix := Matrix.rowAdd s.matrix src dst c
        accumulator := (transformAccumulator n m).rowAdd s.accumulator src dst c } := by
  change Matrix.rowAdd s.accumulator.left src dst c * A * s.accumulator.right =
    Matrix.rowAdd s.matrix src dst c
  rw [Matrix.rowAdd_mul, Matrix.rowAdd_mul, h]

private theorem colCombine_transforms (A : Matrix Int n m)
    {s : Result (Transforms n m) n m} (h : TransformsInput A s)
    (i j : Fin m) (a b c d : Int) :
    TransformsInput A
      { s with
        matrix := Hermite.combineCols s.matrix i j a b c d
        accumulator := (transformAccumulator n m).colCombine
          s.accumulator i j a b c d } := by
  change s.accumulator.left * A *
      Hermite.combineCols s.accumulator.right i j a b c d =
    Hermite.combineCols s.matrix i j a b c d
  rw [Hermite.mul_combineCols, h]

/-! # Compact diagonal correspondence -/

private theorem diagMatrix_swap (v : Vector Int r) (i j : Fin r) :
    Matrix.colSwap (Matrix.rowSwap (diagMatrix v r r) i j) i j =
      diagMatrix (v.swap i.val j.val i.isLt j.isLt) r r := by
  apply Matrix.ext_getElem
  intro row col
  rw [← Matrix.getElem_pair_eq_nested, ← Matrix.getElem_pair_eq_nested]
  conv =>
    lhs
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_colSwap]
  conv =>
    rhs
    rw [Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
  rw [Matrix.getElem_rowSwap _ i j row i]
  rw [Matrix.getElem_rowSwap _ i j row j]
  rw [Matrix.getElem_rowSwap _ i j row col]
  simp only [getElem_diagMatrix]
  by_cases hri : row = i <;> by_cases hrj : row = j <;>
    by_cases hci : col = i <;> by_cases hcj : col = j
  all_goals simp_all [Fin.ext_iff]
  all_goals split <;> simp_all <;> omega

private theorem diagMatrix_negate (v : Vector Int r) (i : Fin r) :
    Matrix.rowScale (diagMatrix v r r) i (-1) =
      diagMatrix (v.set i.val (-v[i]) i.isLt) r r := by
  apply Matrix.ext_getElem
  intro row col
  rw [← Matrix.getElem_pair_eq_nested, ← Matrix.getElem_pair_eq_nested]
  conv =>
    lhs
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowScale]
  conv =>
    rhs
    rw [Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
  simp only [getElem_diagMatrix]
  by_cases hri : row = i <;> by_cases hrc : row = col
  all_goals simp_all [Vector.getElem_set, Fin.ext_iff]
  all_goals omega

private structure Diagonal.Compact.Agrees
    (compact : Diagonal.Compact.Result α r) (dense : Smith.Result α r r) : Prop where
  matrix : dense.matrix = diagMatrix compact.values r r
  accumulator : dense.accumulator = compact.accumulator

private theorem Diagonal.Compact.swap_agrees (ops : Accumulator α r r)
    {compact : Diagonal.Compact.Result α r} {dense : Smith.Result α r r}
    (h : Agrees compact dense) (i j : Fin r) :
    Agrees (Diagonal.Compact.swap ops compact i j)
      (Diagonal.swap ops dense i j) := by
  rcases compact with ⟨values, compactAcc⟩
  rcases dense with ⟨matrix, diag, denseAcc⟩
  have hmatrix : matrix = diagMatrix values r r := h.matrix
  have hacc : denseAcc = compactAcc := h.accumulator
  subst matrix
  subst denseAcc
  simp only [Diagonal.Compact.swap, Diagonal.swap, swapRows, swapCols]
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact ⟨rfl, rfl⟩
  · simp only [if_neg hij]
    exact ⟨diagMatrix_swap values i j, rfl⟩

private theorem Diagonal.findNonzero?_diag (values : Vector Int r)
    (target : Nat) :
    Diagonal.findNonzero? (diagMatrix values r r) target =
      Diagonal.Compact.findNonzero? values target := by
  unfold Diagonal.findNonzero? Diagonal.Compact.findNonzero?
  congr 1
  funext i
  rw [Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
  simp

set_option maxHeartbeats 800000 in
private theorem Diagonal.Compact.normalizeFuel_agrees
    (ops : Accumulator α r r) (fuel target : Nat)
    {compact : Diagonal.Compact.Result α r}
    {dense : Smith.Result α r r} (h : Agrees compact dense) :
    Agrees (Diagonal.Compact.normalizeFuel ops fuel target compact)
      (Diagonal.normalizeFuel ops fuel target dense) := by
  induction fuel generalizing target compact dense with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.Compact.normalizeFuel, Diagonal.normalizeFuel]
      by_cases ht : target < r
      · rw [dif_pos ht, dif_pos ht]
        rw [h.matrix, Diagonal.findNonzero?_diag]
        cases hf : Diagonal.Compact.findNonzero? compact.values target with
        | none => simp only [hf]; exact h
        | some found =>
            simp only [hf]
            let pivot : Fin r := ⟨target, ht⟩
            have hmoved := swap_agrees ops h pivot found
            have hpivot :
                (Diagonal.swap ops dense pivot found).matrix[(pivot, pivot)] =
                  (Diagonal.Compact.swap ops compact pivot found).values[pivot] := by
              rw [hmoved.matrix, Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
              simp
            by_cases hp : (Diagonal.Compact.swap ops compact pivot found).values[pivot] < 0
            · have hp' : (Diagonal.swap ops dense pivot found).matrix[(pivot, pivot)] < 0 := by
                rw [hpivot]
                exact hp
              rw [if_pos hp, if_pos hp']
              apply ih
              exact ⟨(congrArg (fun M => Matrix.rowScale M pivot (-1))
                hmoved.matrix).trans (diagMatrix_negate _ pivot),
                congrArg (fun acc => ops.rowNegate acc pivot) hmoved.accumulator⟩
            · have hp' : ¬ (Diagonal.swap ops dense pivot found).matrix[(pivot, pivot)] < 0 := by
                rw [hpivot]
                exact hp
              rw [if_neg hp, if_neg hp']
              exact ih (target + 1) hmoved
      · rw [dif_neg ht, dif_neg ht]
        exact h

private def Diagonal.Compact.NonnegTo (s : Diagonal.Compact.Result α r)
    (target : Nat) : Prop :=
  ∀ i : Fin r, i.val < target → 0 ≤ s.values[i]

private theorem Diagonal.Compact.normalizeFuel_nonneg
    (ops : Accumulator α r r) (fuel target : Nat)
    (s : Diagonal.Compact.Result α r)
    (hp : Diagonal.Compact.NonnegTo s target)
    (hsize : target + fuel = r) :
    ∀ i : Fin r,
      0 ≤ (Diagonal.Compact.normalizeFuel ops fuel target s).values[i] := by
  induction fuel generalizing target s with
  | zero =>
      intro i
      exact hp i (by omega)
  | succ fuel ih =>
      rw [Diagonal.Compact.normalizeFuel]
      have ht : target < r := by omega
      rw [dif_pos ht]
      cases hf : Diagonal.Compact.findNonzero? s.values target with
      | none =>
          intro i
          by_cases hi : i.val < target
          · exact hp i hi
          · have hfind := List.find?_eq_none.mp hf i (by simp)
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hfind
            have hz : s.values[i] = 0 := by
              apply Classical.byContradiction
              intro hn
              exact hfind ⟨Nat.le_of_not_gt hi, hn⟩
            simpa [hz]
      | some found =>
          simp only [hf]
          let pivot : Fin r := ⟨target, ht⟩
          have hfound := List.find?_some hf
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfound
          have hge : target ≤ found.val := by
            exact hfound.1
          let moved := Diagonal.Compact.swap ops s pivot found
          have hmoved : Diagonal.Compact.NonnegTo moved target := by
            intro i hi
            simp only [moved, Diagonal.Compact.swap]
            split
            · exact hp i hi
            · change 0 ≤ (s.values.swap pivot.val found.val
                pivot.isLt found.isLt)[i.val]'i.isLt
              rw [Vector.getElem_swap]
              have hip : i.val ≠ pivot.val := by simp [pivot]; omega
              have hif : i.val ≠ found.val := by omega
              simp [hip, hif]
              exact hp i hi
          let p := moved.values[pivot]
          by_cases hneg : p < 0
          · let next : Diagonal.Compact.Result α r :=
              { moved with
                values := moved.values.set pivot.val (-p) pivot.isLt
                accumulator := ops.rowNegate moved.accumulator pivot }
            have hnext : Diagonal.Compact.NonnegTo next (target + 1) := by
              intro i hi
              by_cases hip : i.val = pivot.val
              · simp [next, Vector.getElem_set, hip]
                omega
              · have hip' : pivot.val ≠ i.val := Ne.symm hip
                simp [next, Vector.getElem_set, hip, hip']
                exact hmoved i (by simp [pivot] at hip; omega)
            have hout := ih (target + 1) next hnext (by omega)
            simpa only [moved, pivot, p, if_pos hneg, next] using hout
          · have hnext : Diagonal.Compact.NonnegTo moved (target + 1) := by
              intro i hi
              by_cases hip : i.val = pivot.val
              · have : i = pivot := Fin.ext hip
                subst i
                exact Int.le_of_not_gt hneg
              · exact hmoved i (by simp [pivot] at hip; omega)
            have hout := ih (target + 1) moved hnext (by omega)
            simpa only [moved, pivot, p, if_neg hneg] using hout

private theorem Diagonal.Compact.normalize_nonneg
    (ops : Accumulator α r r) (s : Diagonal.Compact.Result α r) :
    ∀ i : Fin r, 0 ≤ (Diagonal.Compact.normalize ops s).values[i] := by
  unfold Diagonal.Compact.normalize
  exact Diagonal.Compact.normalizeFuel_nonneg ops r 0 s
    (by intro i hi; omega) (by omega)

private theorem Hermite.getRow_combineCols (M : Matrix Int n m)
    (i j : Fin m) (a b c d : Int) (row : Fin n) (col : Fin m) :
    (Matrix.getRow (Hermite.combineCols M i j a b c d) row)[col.val]'col.isLt =
      if col = i then a * M[(row, i)] + b * M[(row, j)]
      else if col = j then c * M[(row, i)] + d * M[(row, j)]
      else M[(row, col)] := by
  change (Hermite.combineCols M i j a b c d)[row][col] = _
  exact Hermite.getElem_combineCols M i j row col a b c d

private theorem Matrix.getRow_rowAdd (M : Matrix Int n m)
    (src dst row : Fin n) (c : Int) (col : Fin m) :
    (Matrix.getRow (Matrix.rowAdd M src dst c) row)[col.val]'col.isLt =
      if row = dst then M[dst][col] + c * M[src][col] else M[row][col] := by
  change (Matrix.rowAdd M src dst c)[row][col] = _
  exact Matrix.getElem_rowAdd M src dst row c col

private theorem getRow_diagMatrix (values : Vector Int r) (row col : Fin r) :
    (Matrix.getRow (diagMatrix values r r) row)[col.val]'col.isLt =
      if h : row.val = col.val then values[(⟨row.val, row.isLt⟩ : Fin r)] else 0 := by
  change (diagMatrix values r r)[row][col] = _
  rw [getElem_diagMatrix]
  split <;> simp_all

private theorem Diagonal.Compact.quotient_lcm (a b : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha0 : a ≠ 0) :
    HexArith.Int.exactDiv (a * b)
        (Int.ofNat (Nat.gcd a.natAbs b.natAbs)) =
      Int.ofNat (Nat.lcm a.natAbs b.natAbs) := by
  let g := Nat.gcd a.natAbs b.natAbs
  let l := Nat.lcm a.natAbs b.natAbs
  let g' := Int.ofNat g
  have ha_cast : Int.ofNat a.natAbs = a := by
    simpa [Int.natAbs_of_nonneg ha] using Int.ofNat_toNat ha
  have hb_cast : Int.ofNat b.natAbs = b := by
    simpa [Int.natAbs_of_nonneg hb] using Int.ofNat_toNat hb
  have hga : g' ∣ a := by
    dsimp only [g, g']
    rw [← ha_cast]
    exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hdiv : g' ∣ a * b := Int.dvd_mul_of_dvd_left hga
  have hg0 : g' ≠ 0 := by
    intro hz
    have hg : g = 0 := by simpa [g'] using hz
    have hzero := (Nat.gcd_eq_zero_iff.mp hg).1
    exact ha0 (by simpa [Int.natAbs_eq_zero] using hzero)
  apply Int.eq_of_mul_eq_mul_right hg0
  calc
    HexArith.Int.exactDiv (a * b) g' * g' = a * b := by
      simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hdiv
    _ = Int.ofNat l * g' := by
      rw [← ha_cast, ← hb_cast]
      have hnat : a.natAbs * b.natAbs = l * g := by
        dsimp only [l, g]
        calc
          a.natAbs * b.natAbs =
              Nat.gcd a.natAbs b.natAbs * Nat.lcm a.natAbs b.natAbs :=
            (Nat.gcd_mul_lcm _ _).symm
          _ = Nat.lcm a.natAbs b.natAbs * Nat.gcd a.natAbs b.natAbs :=
            Nat.mul_comm _ _
      dsimp only [g']
      change Int.ofNat (a.natAbs * b.natAbs) = Int.ofNat (l * g)
      exact congrArg Int.ofNat hnat

private theorem Diagonal.Compact.cast_natAbs (x : Int) (hx : 0 ≤ x) :
    Int.ofNat x.natAbs = x := by
  simpa [Int.natAbs_of_nonneg hx] using Int.ofNat_toNat hx

set_option maxHeartbeats 800000 in
private theorem Diagonal.Compact.pairStep_model
    (ops : Accumulator α r r) (s : Diagonal.Compact.Result α r)
    (i j : Fin r) (hne : i ≠ j)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    (Diagonal.Compact.pairStep ops s i j).values =
      (Diagonal.Bubble.vectorStep (s.values.map Int.natAbs) i j).map
        Int.ofNat := by
  let a := s.values[i]
  let b := s.values[j]
  have ha : 0 ≤ a := hn i
  have hb : 0 ≤ b := hn j
  have hcast : ∀ k : Fin r, Int.ofNat s.values[k].natAbs = s.values[k] := by
    intro k
    exact cast_natAbs s.values[k] (hn k)
  have hcastNat (k : Nat) (hk : k < r) :
      Int.ofNat s.values[k].natAbs = s.values[k] := hcast ⟨k, hk⟩
  have hij : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hji : j.val ≠ i.val := Ne.symm hij
  rw [Diagonal.Compact.pairStep]
  by_cases ha0 : a = 0
  · rw [if_pos ha0]
    have hai : s.values[i] = 0 := by simpa [a] using ha0
    have hai' : s.values[i.val] = 0 := hai
    by_cases hb0 : b = 0
    · rw [if_pos hb0]
      have hbj : s.values[j] = 0 := by simpa [b] using hb0
      have hbj' : s.values[j.val] = 0 := hbj
      apply Vector.ext
      intro k hk
      by_cases hki : k = i.val
      · subst k
        simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hai, hai', hbj, hbj',
          Vector.getElem_set, hne, hij, hji]
      · by_cases hkj : k = j.val
        · subst k
          simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hai, hai', hbj, hbj',
            Vector.getElem_set, hne, hij, hji]
        · have hik : i.val ≠ k := Ne.symm hki
          have hjk : j.val ≠ k := Ne.symm hkj
          simp [Diagonal.Bubble.vectorStep, Vector.getElem_set, hki, hkj,
            hik, hjk, hij, hji, hcastNat k hk]
          exact (hcastNat k hk).symm

    · rw [if_neg hb0]
      apply Vector.ext
      intro k hk
      by_cases hki : k = i.val
      · subst k
        simp [Diagonal.Compact.swap, Diagonal.Bubble.vectorStep, a, b, hai, hai',
          ha0, hb0, Vector.getElem_set, Vector.getElem_swap, hne,
          hij, hji, cast_natAbs b hb]
        exact (hcastNat j.val j.isLt).symm
      · by_cases hkj : k = j.val
        · subst k
          simp [Diagonal.Compact.swap, Diagonal.Bubble.vectorStep, a, b, hai, hai',
            ha0, hb0, Vector.getElem_set, Vector.getElem_swap, hne, hij, hji]
        · have hik : i.val ≠ k := Ne.symm hki
          have hjk : j.val ≠ k := Ne.symm hkj
          simp [Diagonal.Compact.swap, Diagonal.Bubble.vectorStep,
            Vector.getElem_set, Vector.getElem_swap, hki, hkj, hik, hjk, hne,
            hij, hji, hcastNat k hk]
          exact (hcastNat k hk).symm
  · rw [if_neg ha0]
    by_cases hb0 : b = 0
    · rw [if_pos hb0]
      have hbj : s.values[j] = 0 := by simpa [b] using hb0
      have hbj' : s.values[j.val] = 0 := hbj
      apply Vector.ext
      intro k hk
      by_cases hki : k = i.val
      · subst k
        simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hbj, hbj',
          Vector.getElem_set, hij, hji, cast_natAbs a ha]
        exact (hcastNat i.val i.isLt).symm
      · by_cases hkj : k = j.val
        · subst k
          simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hbj, hbj',
            Vector.getElem_set, hne, hij, hji]
        · have hik : i.val ≠ k := Ne.symm hki
          have hjk : j.val ≠ k := Ne.symm hkj
          simp [Diagonal.Bubble.vectorStep, Vector.getElem_set, hki, hkj,
            hik, hjk, hij, hji, hcastNat k hk]
          exact (hcastNat k hk).symm
    · rw [if_neg hb0]
      by_cases hab : a = b
      · rw [if_pos hab]
        have habv : s.values[i.val] = s.values[j.val] := by
          simpa [a, b] using hab
        apply Vector.ext
        intro k hk
        by_cases hki : k = i.val
        · subst k
          simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hab,
            Vector.getElem_set, hne, hij, hji, hcastNat i.val i.isLt]
          rw [habv, Nat.gcd_self]
          exact (hcastNat j.val j.isLt).symm
        · by_cases hkj : k = j.val
          · subst k
            simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hab,
              Vector.getElem_set, hne, hij, hji, hcastNat j.val j.isLt]
            rw [habv, Nat.lcm_self]
            exact (hcastNat j.val j.isLt).symm
          · have hik : i.val ≠ k := Ne.symm hki
            have hjk : j.val ≠ k := Ne.symm hkj
            simp [Diagonal.Bubble.vectorStep, a, b, ha0, hb0, hab,
              Vector.getElem_set, hki, hkj, hik, hjk, hij, hji,
              hcastNat k hk]
            exact (hcastNat k hk).symm
      · rw [if_neg hab]
        rcases he : HexArith.Int.extGcd a b with ⟨g, u, v⟩
        have hg : g = Nat.gcd a.natAbs b.natAbs := by
          have := HexArith.Int.extGcd_fst a b
          rw [he] at this
          exact this
        have hl := quotient_lcm a b ha hb ha0
        have hl' : HexArith.Int.exactDiv (s.values[i] * s.values[j])
            (Int.ofNat (Nat.gcd s.values[i].natAbs s.values[j].natAbs)) =
            Int.ofNat (Nat.lcm s.values[i].natAbs s.values[j].natAbs) := by
          simpa [a, b] using hl
        have hlNat : HexArith.Int.exactDiv (s.values[i.val] * s.values[j.val])
            (Int.ofNat (Nat.gcd s.values[i.val].natAbs s.values[j.val].natAbs)) =
            Int.ofNat (Nat.lcm s.values[i.val].natAbs s.values[j.val].natAbs) := hl'
        apply Vector.ext
        intro k hk
        by_cases hki : k = i.val
        · subst k
          simp [Diagonal.Bubble.vectorStep, a, b, he, hg,
            Vector.getElem_set, hne, hij, hji]
        · by_cases hkj : k = j.val
          · subst k
            simp [Diagonal.Bubble.vectorStep, a, b, he, hg, hl, hl', hlNat,
              Vector.getElem_set, hne, hij, hji]
            exact hlNat
          · have hik : i.val ≠ k := Ne.symm hki
            have hjk : j.val ≠ k := Ne.symm hkj
            simp [Diagonal.Bubble.vectorStep, a, b, he,
              Vector.getElem_set, hki, hkj, hik, hjk, hij, hji,
              hcastNat k hk]
            exact (hcastNat k hk).symm

private theorem Diagonal.Compact.pairStep_nonneg
    (ops : Accumulator α r r) (s : Diagonal.Compact.Result α r)
    (i j : Fin r) (hne : i ≠ j)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    ∀ k : Fin r, 0 ≤ (Diagonal.Compact.pairStep ops s i j).values[k] := by
  rw [pairStep_model ops s i j hne hn]
  intro k
  simp

private theorem Diagonal.Compact.passFuel_model
    (ops : Accumulator α r r) (fuel index : Nat)
    (s : Diagonal.Compact.Result α r)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    (Diagonal.Compact.passFuel ops fuel index s).values =
      (Diagonal.Bubble.vectorPassFuel fuel index
        (s.values.map Int.natAbs)).map Int.ofNat := by
  induction fuel generalizing index s with
  | zero =>
      rw [Diagonal.Compact.passFuel, Diagonal.Bubble.vectorPassFuel]
      apply Vector.ext
      intro k hk
      simp
      exact (cast_natAbs (s.values[k]'hk) (hn (⟨k, hk⟩ : Fin r))).symm
  | succ fuel ih =>
      rw [Diagonal.Compact.passFuel, Diagonal.Bubble.vectorPassFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi, dif_pos hi]
        let i : Fin r := ⟨index, by omega⟩
        let j : Fin r := ⟨index + 1, hi⟩
        let next := Diagonal.Compact.pairStep ops s i j
        have hne : i ≠ j := by simp [i, j]
        have hmodel := pairStep_model ops s i j hne hn
        have hnnext := pairStep_nonneg ops s i j hne hn
        rw [ih (index + 1) next hnnext]
        have habs : next.values.map Int.natAbs =
            Diagonal.Bubble.vectorStep (s.values.map Int.natAbs) i j := by
          rw [hmodel]
          apply Vector.ext
          intro k hk
          simp
        rw [habs]
      · rw [dif_neg hi, dif_neg hi]
        apply Vector.ext
        intro k hk
        simp
        exact (cast_natAbs (s.values[k]'hk) (hn (⟨k, hk⟩ : Fin r))).symm

private theorem Diagonal.Compact.pass_model
    (ops : Accumulator α r r) (s : Diagonal.Compact.Result α r)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    (Diagonal.Compact.pass ops s).values =
      (Diagonal.Bubble.vectorPass (s.values.map Int.natAbs)).map Int.ofNat := by
  unfold Diagonal.Compact.pass Diagonal.Bubble.vectorPass
  exact passFuel_model ops (r - 1) 0 s hn

private theorem Diagonal.Compact.pass_nonneg
    (ops : Accumulator α r r) (s : Diagonal.Compact.Result α r)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    ∀ k : Fin r, 0 ≤ (Diagonal.Compact.pass ops s).values[k] := by
  rw [pass_model ops s hn]
  intro k
  simp

private theorem Diagonal.Compact.networkFuel_model
    (ops : Accumulator α r r) (fuel : Nat)
    (s : Diagonal.Compact.Result α r)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    (Diagonal.Compact.networkFuel ops fuel s).values =
      (Diagonal.Bubble.vectorNetwork fuel
        (s.values.map Int.natAbs)).map Int.ofNat := by
  induction fuel generalizing s with
  | zero =>
      rw [Diagonal.Compact.networkFuel, Diagonal.Bubble.vectorNetwork]
      apply Vector.ext
      intro k hk
      simp
      exact (cast_natAbs (s.values[k]'hk) (hn (⟨k, hk⟩ : Fin r))).symm
  | succ fuel ih =>
      rw [Diagonal.Compact.networkFuel, Diagonal.Bubble.vectorNetwork]
      have hp := pass_model ops s hn
      have hpn := pass_nonneg ops s hn
      rw [ih (Diagonal.Compact.pass ops s) hpn]
      have habs : (Diagonal.Compact.pass ops s).values.map Int.natAbs =
          Diagonal.Bubble.vectorPass (s.values.map Int.natAbs) := by
        rw [hp]
        apply Vector.ext
        intro k hk
        simp
      rw [habs]

private theorem Diagonal.Compact.networkFuel_nonneg
    (ops : Accumulator α r r) (fuel : Nat)
    (s : Diagonal.Compact.Result α r)
    (hn : ∀ k : Fin r, 0 ≤ s.values[k]) :
    ∀ k : Fin r, 0 ≤ (Diagonal.Compact.networkFuel ops fuel s).values[k] := by
  rw [networkFuel_model ops fuel s hn]
  intro k
  simp

private theorem Diagonal.Compact.run_model
    (ops : Accumulator α r r) (d : Vector Int r) :
    let normalized := Diagonal.Compact.normalize ops
      ({ values := d, accumulator := ops.init } : Diagonal.Compact.Result α r)
    (Diagonal.Compact.run ops d).values =
      (Diagonal.Bubble.vectorNetwork r
        (normalized.values.map Int.natAbs)).map Int.ofNat := by
  dsimp only
  unfold Diagonal.Compact.run
  exact networkFuel_model ops r _ (normalize_nonneg ops _)

private theorem Diagonal.Compact.run_nonneg
    (ops : Accumulator α r r) (d : Vector Int r) :
    ∀ k : Fin r, 0 ≤ (Diagonal.Compact.run ops d).values[k] := by
  unfold Diagonal.Compact.run
  exact networkFuel_nonneg ops r _ (normalize_nonneg ops _)

private theorem Diagonal.Compact.run_chain
    (ops : Accumulator α r r) (d : Vector Int r) :
    Diagonal.Bubble.Chain
      ((Diagonal.Compact.run ops d).values.map Int.natAbs).toList := by
  let normalized := Diagonal.Compact.normalize ops
    ({ values := d, accumulator := ops.init } : Diagonal.Compact.Result α r)
  have hm := run_model ops d
  dsimp only at hm
  have habs : (Diagonal.Compact.run ops d).values.map Int.natAbs =
      Diagonal.Bubble.vectorNetwork r
        (normalized.values.map Int.natAbs) := by
    dsimp only [normalized]
    rw [hm]
    apply Vector.ext
    intro k hk
    simp
  rw [habs]
  exact Diagonal.Bubble.vectorNetwork_chain _

private theorem Diagonal.Compact.takeWhile_abs (xs : List Int)
    (hn : ∀ x ∈ xs, 0 ≤ x) :
    xs.takeWhile (fun x => decide (x ≠ 0)) =
      (Diagonal.Bubble.nonzeros (xs.map Int.natAbs)).map Int.ofNat := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have ha := hn a (by simp)
      by_cases ha0 : a = 0
      · subst a
        simp [Diagonal.Bubble.nonzeros]
      · rw [List.takeWhile_cons, if_pos (by simpa)]
        rw [List.map_cons, Diagonal.Bubble.nonzeros, if_neg (by simpa [ha0])]
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨(cast_natAbs a ha).symm, ih (by
          intro x hx
          exact hn x (by simp [hx]))⟩

private theorem Diagonal.Compact.collect_abs (values : Vector Int r)
    (hn : ∀ i : Fin r, 0 ≤ values[i]) :
    Diagonal.Compact.collect values =
      (Diagonal.Bubble.nonzeros
        (values.map Int.natAbs).toList).map Int.ofNat := by
  unfold Diagonal.Compact.collect
  rw [Vector.toList_map]
  apply takeWhile_abs
  intro x hx
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx
  have hir : i < r := by simpa using hi
  rw [Vector.getElem_toList] at hget
  have := hn (⟨i, hir⟩ : Fin r)
  simpa [hget] using this

private theorem Diagonal.Compact.values_abs (values : Vector Int r)
    (hn : ∀ i : Fin r, 0 ≤ values[i]) :
    values.toList = (values.map Int.natAbs).toList.map Int.ofNat := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkr : k < r := by simpa using hk
    rw [Vector.getElem_toList]
    simp only [Vector.toList_map, List.getElem_map, Vector.getElem_toList]
    exact (cast_natAbs (values[k]'hkr) (hn ⟨k, hkr⟩)).symm

private theorem Diagonal.Compact.run_split
    (ops : Accumulator α r r) (d : Vector Int r) :
    ∃ k, (Diagonal.Compact.run ops d).values.toList =
      Diagonal.Compact.collect (Diagonal.Compact.run ops d).values ++
        List.replicate k 0 := by
  let result := Diagonal.Compact.run ops d
  have hn := run_nonneg ops d
  have hc := run_chain ops d
  obtain ⟨k, hsplit, _hchain, _hpos⟩ :=
    Diagonal.Bubble.chain_split _ hc
  refine ⟨k, ?_⟩
  have hn' : ∀ i : Fin r, 0 ≤ result.values[i] := by
    simpa [result] using hn
  have hsplit' : (result.values.map Int.natAbs).toList =
      Diagonal.Bubble.nonzeros (result.values.map Int.natAbs).toList ++
        List.replicate k 0 := by simpa [result] using hsplit
  rw [values_abs result.values hn', collect_abs result.values hn']
  have hmap := congrArg (List.map Int.ofNat) hsplit'
  simpa using hmap

private theorem Diagonal.Compact.diagMatrix_split
    (values : Vector Int r) (xs : List Int) (k : Nat)
    (hsplit : values.toList = xs ++ List.replicate k 0) :
    diagMatrix values r r =
      diagMatrix (⟨xs.toArray, by simp⟩ : Vector Int xs.length) r r := by
  have hlen : xs.length + k = r := by
    have := congrArg List.length hsplit
    simpa using this.symm
  apply Matrix.ext_getElem
  intro i j
  rw [← Matrix.getElem_pair_eq_nested, ← Matrix.getElem_pair_eq_nested,
    Matrix.getElem_pair_eq_nested, getElem_diagMatrix,
    Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
  by_cases hij : i.val = j.val
  · have hij' : i = j := Fin.ext hij
    subst j
    by_cases hi : i.val < xs.length
    · rw [dif_pos ⟨rfl, i.isLt⟩, dif_pos ⟨rfl, hi⟩]
      change values.toList[i.val] = xs.toArray[i.val]
      rw [List.getElem_toArray]
      simp [hsplit, List.getElem_append, hi]
    · have hv : values.toList[i.val] = 0 := by
        simp [hsplit, List.getElem_append, hi]
      simp only [Fin.getElem_fin, hi, and_self, dif_neg, i.isLt, dif_pos]
      rw [Vector.getElem_toList] at hv
      exact hv
  · simp [hij]

/-- The compact fixed network always satisfies its Smith-shape certificate. -/
theorem Diagonal.Compact.run_valid
    (ops : Accumulator α r r) (d : Vector Int r) :
    Diagonal.Valid
      (Diagonal.Compact.erase (Diagonal.Compact.run ops d)) := by
  let result := Diagonal.Compact.run ops d
  have hn : ∀ i : Fin r, 0 ≤ result.values[i] := by
    simpa [result] using Diagonal.Compact.run_nonneg ops d
  have hc : Diagonal.Bubble.Chain
      (result.values.map Int.natAbs).toList := by
    simpa [result] using Diagonal.Compact.run_chain ops d
  obtain ⟨zeroCount, hsplit, hchain, hpos⟩ :=
    Diagonal.Bubble.chain_split _ hc
  have hcollect := Diagonal.Compact.collect_abs result.values hn
  have hposInt : ∀ x ∈ Diagonal.Compact.collect result.values, 0 < x := by
    intro x hx
    rw [hcollect] at hx
    obtain ⟨n, hnmem, rfl⟩ := List.mem_map.mp hx
    exact Int.ofNat_lt.mpr (hpos n hnmem)
  have hchainInt : ∀ i (hi : i + 1 <
      (Diagonal.Compact.collect result.values).length),
      (Diagonal.Compact.collect result.values)[i]'(by omega) ∣
        (Diagonal.Compact.collect result.values)[i + 1]'hi := by
    intro i hi
    have hi' : i + 1 <
        (Diagonal.Bubble.nonzeros
          (result.values.map Int.natAbs).toList).length := by
      simpa [hcollect] using hi
    have hd := Diagonal.Bubble.chain_get hchain i hi'
    have hd' := Int.natCast_dvd_natCast.mpr hd
    simpa [hcollect] using hd'
  obtain ⟨k, hvalues⟩ := Diagonal.Compact.run_split ops d
  have hvalues' : result.values.toList =
      Diagonal.Compact.collect result.values ++ List.replicate k 0 := by
    simpa [result] using hvalues
  have hlen : (Diagonal.Compact.collect result.values).length + k = r := by
    have := congrArg List.length hvalues'
    simpa using this.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Diagonal.Compact.collect
      (Diagonal.Compact.run ops d).values).length ≤ r
    simpa [result] using (show
      (Diagonal.Compact.collect result.values).length ≤ r by omega)
  · dsimp only [Diagonal.Compact.erase]
    exact Diagonal.Compact.diagMatrix_split result.values
      (Diagonal.Compact.collect result.values) k hvalues'
  · intro i
    have hi : i.val < (Diagonal.Compact.collect result.values).length := by
      simpa [result, Diagonal.Compact.erase] using i.isLt
    have hp := hposInt
      ((Diagonal.Compact.collect result.values)[i.val]'hi)
      (List.getElem_mem hi)
    change 0 < (Diagonal.Compact.collect
      (Diagonal.Compact.run ops d).values)[i.val]'(by
        simpa [Diagonal.Compact.erase] using i.isLt)
    simpa [result] using hp
  · intro i
    have hiRun : i.val + 1 < (Diagonal.Compact.collect
        (Diagonal.Compact.run ops d).values).length := by
      have hiDiag : i.val + 1 <
          (Diagonal.Compact.erase (Diagonal.Compact.run ops d)).diag.length := by
        omega
      simpa [Diagonal.Compact.erase] using hiDiag
    have hi : i.val + 1 <
        (Diagonal.Compact.collect result.values).length := by
      simpa [result] using hiRun
    have hd := hchainInt i.val hi
    change (Diagonal.Compact.collect
        (Diagonal.Compact.run ops d).values)[i.val]'(by omega) ∣
      (Diagonal.Compact.collect
        (Diagonal.Compact.run ops d).values)[i.val + 1]'hiRun
    simpa [result] using hd

set_option maxHeartbeats 1600000 in
private theorem Diagonal.Compact.pair_matrix (values : Vector Int r)
    (i j : Fin r) (hne : i ≠ j)
    (ha0 : values[i] ≠ 0) (hb0 : values[j] ≠ 0) :
    let a := values[i]
    let b := values[j]
    let (g, u, v) := HexArith.Int.extGcd a b
    let g' := Int.ofNat g
    let qa := HexArith.Int.exactDiv a g'
    let qb := HexArith.Int.exactDiv b g'
    let c := -(HexArith.Int.exactDiv (b * v) g')
    Matrix.rowAdd
        (Hermite.combineCols (Matrix.rowAdd (diagMatrix values r r) j i 1)
          i j u v (-qb) qa) i j c =
      diagMatrix ((values.set i.val g' i.isLt).set j.val
        (HexArith.Int.exactDiv (a * b) g') j.isLt) r r := by
  let a := values[i]
  let b := values[j]
  have ha : a ≠ 0 := ha0
  have hb : b ≠ 0 := hb0
  rcases he : HexArith.Int.extGcd a b with ⟨g, u, v⟩
  have hspec := HexArith.Int.extGcd_spec a b
  rw [he] at hspec
  simp only at hspec
  rcases hspec with ⟨hg, hbez⟩
  let g' := Int.ofNat g
  let qa := HexArith.Int.exactDiv a g'
  let qb := HexArith.Int.exactDiv b g'
  let l := HexArith.Int.exactDiv (a * b) g'
  let c := -(HexArith.Int.exactDiv (b * v) g')
  have hne' : j.val ≠ i.val := by
    intro h
    exact hne (Fin.ext h.symm)
  have hga : g' ∣ a := by
    dsimp only [g']
    rw [hg]
    exact Int.gcd_dvd_left a b
  have hgb : g' ∣ b := by
    dsimp only [g']
    rw [hg]
    exact Int.gcd_dvd_right a b
  have hg0 : g' ≠ 0 := by
    intro hz
    rcases hga with ⟨q, hq⟩
    rw [hz, Int.zero_mul] at hq
    exact ha hq
  have hqa : qa * g' = a := by
    simpa [qa, HexArith.Int.exactDiv] using Int.ediv_mul_cancel hga
  have hqb : qb * g' = b := by
    simpa [qb, HexArith.Int.exactDiv] using Int.ediv_mul_cancel hgb
  have hgl : g' ∣ a * b := Int.dvd_mul_of_dvd_left hga
  have hl : l * g' = a * b := by
    simpa [l, HexArith.Int.exactDiv] using Int.ediv_mul_cancel hgl
  have hgv : g' ∣ b * v := Int.dvd_mul_of_dvd_left hgb
  have hv : HexArith.Int.exactDiv (b * v) g' * g' = b * v := by
    simpa [HexArith.Int.exactDiv] using Int.ediv_mul_cancel hgv
  have hcross : -qb * a + qa * b = 0 := by
    rw [← hqa, ← hqb]
    rw [← Int.mul_assoc, ← Int.mul_assoc, ← Int.add_mul,
      Int.neg_mul, Int.mul_comm qb qa]
    omega
  have hclear : v * b + c * g' = 0 := by
    dsimp only [c]
    rw [Int.neg_mul, hv]
    rw [Int.mul_comm v b]
    omega
  have hql : qa * b = l := by
    apply Int.eq_of_mul_eq_mul_right hg0
    calc
      (qa * b) * g' = (qa * g') * b := by ac_rfl
      _ = a * b := by rw [hqa]
      _ = l * g' := hl.symm
  simp only [a, b, he]
  apply Matrix.ext_getElem
  intro row col
  rw [← Matrix.getElem_pair_eq_nested, ← Matrix.getElem_pair_eq_nested]
  conv =>
    lhs
    rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_rowAdd]
  conv =>
    rhs
    rw [Matrix.getElem_pair_eq_nested, getElem_diagMatrix]
  by_cases hri : row = i <;> by_cases hrj : row = j <;>
    by_cases hci : col = i <;> by_cases hcj : col = j
  all_goals simp_all [Hermite.getRow_combineCols,
    Matrix.getElem_pair_eq_nested,
    Matrix.getRow_rowAdd, getRow_diagMatrix,
    Vector.getElem_set, Fin.ext_iff]
  all_goals grind

private theorem Diagonal.Compact.pairStep_agrees (ops : Accumulator α r r)
    {compact : Diagonal.Compact.Result α r}
    {dense : Smith.Result α r r} (h : Agrees compact dense)
    (i j : Fin r) (hne : i ≠ j) :
    Agrees (Diagonal.Compact.pairStep ops compact i j)
      (Diagonal.pairStep ops dense i j) := by
  rcases compact with ⟨values, compactAcc⟩
  rcases dense with ⟨matrix, diag, denseAcc⟩
  have hmatrix : matrix = diagMatrix values r r := h.matrix
  have hacc : denseAcc = compactAcc := h.accumulator
  subst matrix
  subst denseAcc
  have hii : (diagMatrix values r r)[(i, i)] = values[i] := by
    rw [Matrix.getElem_pair_eq_nested]
    exact diagMatrix_apply_diag values i i rfl i.isLt
  have hjj : (diagMatrix values r r)[(j, j)] = values[j] := by
    rw [Matrix.getElem_pair_eq_nested]
    exact diagMatrix_apply_diag values j j rfl j.isLt
  rw [Diagonal.Compact.pairStep, Diagonal.pairStep, hii, hjj]
  by_cases ha : values[i] = 0
  · rw [if_pos ha, if_pos ha]
    by_cases hb : values[j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb, if_neg hb]
      exact swap_agrees ops ⟨rfl, rfl⟩ i j
  · rw [if_neg ha, if_neg ha]
    by_cases hb : values[j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb, if_neg hb]
      by_cases hab : values[i] = values[j]
      · rw [if_pos hab, if_pos hab]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hab, if_neg hab]
        exact ⟨Diagonal.Compact.pair_matrix values i j hne ha hb, rfl⟩

private theorem Diagonal.Compact.passFuel_agrees (ops : Accumulator α r r)
    (fuel index : Nat) {compact : Diagonal.Compact.Result α r}
    {dense : Smith.Result α r r} (h : Agrees compact dense) :
    Agrees (Diagonal.Compact.passFuel ops fuel index compact)
      (Diagonal.passFuel ops fuel index dense) := by
  induction fuel generalizing index compact dense with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.Compact.passFuel, Diagonal.passFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi, dif_pos hi]
        exact ih (index + 1) (pairStep_agrees ops h
          ⟨index, by omega⟩ ⟨index + 1, hi⟩ (by simp))
      · rw [dif_neg hi, dif_neg hi]
        exact h

private theorem Diagonal.Compact.pass_agrees (ops : Accumulator α r r)
    {compact : Diagonal.Compact.Result α r}
    {dense : Smith.Result α r r} (h : Agrees compact dense) :
    Agrees (Diagonal.Compact.pass ops compact) (Diagonal.pass ops dense) := by
  unfold Diagonal.Compact.pass Diagonal.pass
  exact passFuel_agrees ops (r - 1) 0 h

private theorem Diagonal.Compact.networkFuel_agrees (ops : Accumulator α r r)
    (fuel : Nat) {compact : Diagonal.Compact.Result α r}
    {dense : Smith.Result α r r} (h : Agrees compact dense) :
    Agrees (Diagonal.Compact.networkFuel ops fuel compact)
      (Diagonal.networkFuel ops fuel dense) := by
  induction fuel generalizing compact dense with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.Compact.networkFuel, Diagonal.networkFuel]
      exact ih (pass_agrees ops h)

private theorem Diagonal.Compact.run_agrees (ops : Accumulator α r r)
    (d : Vector Int r) :
    Agrees (Diagonal.Compact.run ops d) (Diagonal.run ops d) := by
  unfold Diagonal.Compact.run Diagonal.run Diagonal.Compact.normalize
    Diagonal.normalize
  have hnorm := normalizeFuel_agrees ops r 0
    (⟨rfl, rfl⟩ : Agrees
      ({ values := d, accumulator := ops.init } : Diagonal.Compact.Result α r)
      ({ matrix := diagMatrix d r r, diag := [], accumulator := ops.init } :
        Smith.Result α r r))
  have hnet := networkFuel_agrees ops r hnorm
  exact ⟨hnet.matrix, hnet.accumulator⟩

private theorem Diagonal.swap_transforms (A : Matrix Int r r)
    {s : Result (Transforms r r) r r} (h : TransformsInput A s)
    (i j : Fin r) :
    TransformsInput A (Diagonal.swap (transformAccumulator r r) s i j) := by
  exact swapCols_transforms A
    (swapRows_transforms A h i j) i j

set_option maxHeartbeats 800000 in
private theorem Diagonal.normalizeFuel_transforms (A : Matrix Int r r)
    (fuel target : Nat) {s : Result (Transforms r r) r r}
    (h : TransformsInput A s) :
    TransformsInput A
      (Diagonal.normalizeFuel (transformAccumulator r r) fuel target s) := by
  induction fuel generalizing target s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.normalizeFuel]
      split
      · rename_i ht
        cases hf : Diagonal.findNonzero? s.matrix target with
        | none => exact h
        | some found =>
            simp only [hf]
            let pivot : Fin r := ⟨target, ht⟩
            have hmoved := Diagonal.swap_transforms A h pivot found
            split
            · exact ih _ (negateRow_transforms A hmoved pivot)
            · exact ih _ hmoved
      · exact h

private theorem Diagonal.pairStep_transforms (A : Matrix Int r r)
    {s : Result (Transforms r r) r r} (h : TransformsInput A s)
    (i j : Fin r) :
    TransformsInput A
      (Diagonal.pairStep (transformAccumulator r r) s i j) := by
  rw [Diagonal.pairStep]
  split
  · split
    · exact h
    · exact Diagonal.swap_transforms A h i j
  · split
    · exact h
    · split
      · exact h
      · let a := s.matrix[(i, i)]
        let b := s.matrix[(j, j)]
        let rowAdded : Result (Transforms r r) r r :=
          { s with
            matrix := Matrix.rowAdd s.matrix j i 1
            accumulator := (transformAccumulator r r).rowAdd s.accumulator j i 1 }
        let ext := HexArith.Int.extGcd a b
        let g' := Int.ofNat ext.1
        let qa := HexArith.Int.exactDiv a g'
        let qb := HexArith.Int.exactDiv b g'
        let columns : Result (Transforms r r) r r :=
          { rowAdded with
            matrix := Hermite.combineCols rowAdded.matrix i j ext.2.1 ext.2.2 (-qb) qa
            accumulator := (transformAccumulator r r).colCombine
              rowAdded.accumulator i j ext.2.1 ext.2.2 (-qb) qa }
        let c := -(HexArith.Int.exactDiv (b * ext.2.2) g')
        exact rowAdd_transforms A
          (colCombine_transforms A (rowAdd_transforms A h j i 1)
            i j ext.2.1 ext.2.2 (-qb) qa) i j c

private theorem Diagonal.passFuel_transforms (A : Matrix Int r r)
    (fuel index : Nat) {s : Result (Transforms r r) r r}
    (h : TransformsInput A s) :
    TransformsInput A
      (Diagonal.passFuel (transformAccumulator r r) fuel index s) := by
  induction fuel generalizing index s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.passFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi]
        exact ih (index + 1) (Diagonal.pairStep_transforms A h
          ⟨index, by omega⟩ ⟨index + 1, hi⟩)
      · rw [dif_neg hi]
        exact h

private theorem Diagonal.pass_transforms (A : Matrix Int r r)
    {s : Result (Transforms r r) r r} (h : TransformsInput A s) :
    TransformsInput A (Diagonal.pass (transformAccumulator r r) s) := by
  unfold Diagonal.pass
  exact Diagonal.passFuel_transforms A (r - 1) 0 h

set_option maxHeartbeats 800000 in
private theorem Diagonal.networkFuel_transforms (A : Matrix Int r r)
    (fuel : Nat) {s : Result (Transforms r r) r r} (h : TransformsInput A s) :
    TransformsInput A
      (Diagonal.networkFuel (transformAccumulator r r) fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.networkFuel]
      exact ih (Diagonal.pass_transforms A h)

/-- The fixed diagonal sweep's transforms carry its input to its working
matrix. -/
theorem Diagonal.run_transform (d : Vector Int r) :
    let s := Diagonal.run (transformAccumulator r r) d
    s.accumulator.left * diagMatrix d r r * s.accumulator.right = s.matrix := by
  unfold Diagonal.run Diagonal.normalize
  apply Diagonal.networkFuel_transforms
  apply Diagonal.normalizeFuel_transforms
  change Matrix.identity (R := Int) r * diagMatrix d r r * Matrix.identity r =
    diagMatrix d r r
  rw [Matrix.identity_mul, Matrix.mul_identity]

private theorem rowAdd_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (src dst : Fin n) (c : Int) (hne : src ≠ dst) :
    HasInverses
      { s with
        matrix := Matrix.rowAdd s.matrix src dst c
        accumulator := (transformAccumulator n m).rowAdd s.accumulator src dst c } := by
  constructor
  · change Matrix.rowAdd s.accumulator.left src dst c *
        Matrix.colAdd s.accumulator.leftInv dst src (-c) = Matrix.identity n
    rw [Matrix.rowAdd_mul, Matrix.mul_colAdd, h.1]
    exact Hermite.add_inverse_identity src dst hne c
  · exact h.2

private theorem colCombine_inverses {s : Result (Transforms n m) n m}
    (h : HasInverses s) (i j : Fin m) (a b c d : Int)
    (hne : i ≠ j) (hdet : a * d - b * c = 1) :
    HasInverses
      { s with
        matrix := Hermite.combineCols s.matrix i j a b c d
        accumulator := (transformAccumulator n m).colCombine
          s.accumulator i j a b c d } := by
  constructor
  · exact h.1
  · let F := Hermite.combineCols (Matrix.identity (R := Int) m) i j a b c d
    let G := Hermite.combineRows (Matrix.identity (R := Int) m)
      i j d (-c) (-b) a
    have hdetInv : d * a - (-c) * (-b) = 1 := by grind
    have hcancel : F * G = Matrix.identity m := by
      apply mul_eq_one_comm
      dsimp [F, G]
      rw [Hermite.combineRows_mul, Matrix.identity_mul]
      simpa using Hermite.combine_inverse_identity i j hne
        d (-c) (-b) a hdetInv
    have hF : Hermite.combineCols s.accumulator.right i j a b c d =
        s.accumulator.right * F := by
      dsimp [F]
      rw [Hermite.mul_combineCols, Matrix.mul_identity]
    have hG : Hermite.combineRows s.accumulator.rightInv i j d (-c) (-b) a =
        G * s.accumulator.rightInv := by
      dsimp [G]
      rw [Hermite.combineRows_mul, Matrix.identity_mul]
    change Hermite.combineCols s.accumulator.right i j a b c d *
        Hermite.combineRows s.accumulator.rightInv i j d (-c) (-b) a =
      Matrix.identity m
    rw [hF, hG]
    exact preserveRightInverse _ _ _ _ h.2 hcancel

private theorem Diagonal.swap_inverses
    {s : Result (Transforms r r) r r} (h : HasInverses s) (i j : Fin r) :
    HasInverses (Diagonal.swap (transformAccumulator r r) s i j) := by
  exact swapCols_inverses (swapRows_inverses h i j) i j

set_option maxHeartbeats 800000 in
private theorem Diagonal.normalizeFuel_inverses (fuel target : Nat)
    {s : Result (Transforms r r) r r} (h : HasInverses s) :
    HasInverses
      (Diagonal.normalizeFuel (transformAccumulator r r) fuel target s) := by
  induction fuel generalizing target s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.normalizeFuel]
      split
      · rename_i ht
        cases hf : Diagonal.findNonzero? s.matrix target with
        | none => exact h
        | some found =>
            simp only [hf]
            let pivot : Fin r := ⟨target, ht⟩
            have hmoved := Diagonal.swap_inverses h pivot found
            split
            · exact ih _ (negateRow_inverses hmoved pivot)
            · exact ih _ hmoved
      · exact h

set_option maxHeartbeats 800000 in
private theorem Diagonal.pairStep_inverses
    {s : Result (Transforms r r) r r} (h : HasInverses s)
    (i j : Fin r) (hne : i ≠ j) :
    HasInverses (Diagonal.pairStep (transformAccumulator r r) s i j) := by
  rw [Diagonal.pairStep]
  split
  · split
    · exact h
    · exact Diagonal.swap_inverses h i j
  · rename_i ha
    split
    · exact h
    · rename_i hb
      split
      · exact h
      · let a := s.matrix[(i, i)]
        let b := s.matrix[(j, j)]
        have hb0 : b ≠ 0 := by simpa [b] using hb
        rcases he : HexArith.Int.extGcd a b with ⟨g, u, v⟩
        let g' := Int.ofNat g
        let qa := HexArith.Int.exactDiv a g'
        let qb := HexArith.Int.exactDiv b g'
        have hdet := Hermite.gcdCoeffs_det (a := a) (b := b) hb0
        unfold Hermite.gcdCoeffs at hdet
        rw [he] at hdet
        dsimp only at hdet
        let rowAdded : Result (Transforms r r) r r :=
          { s with
            matrix := Matrix.rowAdd s.matrix j i 1
            accumulator := (transformAccumulator r r).rowAdd s.accumulator j i 1 }
        let columns : Result (Transforms r r) r r :=
          { rowAdded with
            matrix := Hermite.combineCols rowAdded.matrix i j u v (-qb) qa
            accumulator := (transformAccumulator r r).colCombine
              rowAdded.accumulator i j u v (-qb) qa }
        let c := -(HexArith.Int.exactDiv (b * v) g')
        exact rowAdd_inverses
          (colCombine_inverses (rowAdd_inverses h j i 1 (Ne.symm hne))
            i j u v (-qb) qa hne hdet) i j c hne

private theorem Diagonal.passFuel_inverses (fuel index : Nat)
    {s : Result (Transforms r r) r r} (h : HasInverses s) :
    HasInverses
      (Diagonal.passFuel (transformAccumulator r r) fuel index s) := by
  induction fuel generalizing index s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.passFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi]
        exact ih (index + 1) (Diagonal.pairStep_inverses h
          ⟨index, by omega⟩ ⟨index + 1, hi⟩ (by
            intro heq
            have := congrArg Fin.val heq
            simp only at this
            omega))
      · rw [dif_neg hi]
        exact h

private theorem Diagonal.pass_inverses
    {s : Result (Transforms r r) r r} (h : HasInverses s) :
    HasInverses (Diagonal.pass (transformAccumulator r r) s) := by
  unfold Diagonal.pass
  exact Diagonal.passFuel_inverses (r - 1) 0 h

set_option maxHeartbeats 800000 in
private theorem Diagonal.networkFuel_inverses (fuel : Nat)
    {s : Result (Transforms r r) r r} (h : HasInverses s) :
    HasInverses (Diagonal.networkFuel (transformAccumulator r r) fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      rw [Diagonal.networkFuel]
      exact ih (Diagonal.pass_inverses h)

/-- Both inverses accumulated by the fixed diagonal sweep remain right
inverses. -/
theorem Diagonal.run_inverses (d : Vector Int r) :
    let s := Diagonal.run (transformAccumulator r r) d
    s.accumulator.left * s.accumulator.leftInv = Matrix.identity r ∧
      s.accumulator.right * s.accumulator.rightInv = Matrix.identity r := by
  unfold Diagonal.run Diagonal.normalize
  apply Diagonal.networkFuel_inverses
  apply Diagonal.normalizeFuel_inverses
  constructor <;> exact Matrix.identity_mul _

/-- The compact transform accumulator carries diagonal input to the compact
working diagonal. -/
theorem Diagonal.Compact.run_transform (d : Vector Int r) :
    let s := Diagonal.Compact.run (transformAccumulator r r) d
    s.accumulator.left * diagMatrix d r r * s.accumulator.right =
      diagMatrix s.values r r := by
  have hagree := Diagonal.Compact.run_agrees (transformAccumulator r r) d
  dsimp only
  rw [← hagree.accumulator, ← hagree.matrix]
  exact Diagonal.run_transform d

/-- The transforms accumulated by the compact diagonal sweep retain their
explicit right inverses. -/
theorem Diagonal.Compact.run_inverses (d : Vector Int r) :
    let s := Diagonal.Compact.run (transformAccumulator r r) d
    s.accumulator.left * s.accumulator.leftInv = Matrix.identity r ∧
      s.accumulator.right * s.accumulator.rightInv = Matrix.identity r := by
  have hagree := Diagonal.Compact.run_agrees (transformAccumulator r r) d
  dsimp only
  rw [← hagree.accumulator]
  exact Diagonal.run_inverses d

private theorem run_complete (ops : Accumulator α n m) (A : Matrix Int n m) :
    let result := run ops A
    Prefix result ∧ result.matrix = diagMatrix result.diagVector n m := by
  have h := runFuel_complete ops (Nat.min n m)
    (Prefix.initial A ops.init) (by simp)
  simpa only [run] using h

/-- Every accumulator path finishes at the diagonal encoded by its reported
invariant-factor list. -/
theorem run_matrix (ops : Accumulator α n m) (A : Matrix Int n m) :
    let result := run ops A
    result.matrix = diagMatrix result.diagVector n m :=
  (run_complete ops A).2

/-- Every reported invariant factor is positive. -/
theorem run_positive (ops : Accumulator α n m) (A : Matrix Int n m)
    (i : Nat) (hi : i < (run ops A).diag.length) :
    0 < (run ops A).diag[i]'hi :=
  (run_complete ops A).1.positive i hi

/-- Reported invariant factors form a divisibility chain. -/
theorem run_chain (ops : Accumulator α n m) (A : Matrix Int n m)
    (i : Nat) (hi : i + 1 < (run ops A).diag.length) :
    (run ops A).diag[i]'(by omega) ∣ (run ops A).diag[i + 1]'hi :=
  (run_complete ops A).1.chain i hi

end Smith

/-- The form-only and full-data schedules report the same rank. -/
theorem snfRank_eq_data (A : Matrix Int n m) :
    snfRank A = (snfData A).rank := by
  exact congrArg List.length (Smith.run_same
    (Smith.formAccumulator n m) (Smith.transformAccumulator n m) A).diag

/-- The form-only and full-data schedules carry the same invariant-factor
vector, after transporting across their equal reported ranks. -/
theorem invariantFactors_cast_eq_data (A : Matrix Int n m) :
    (invariantFactors A).cast (snfRank_eq_data A) = (snfData A).diag := by
  unfold invariantFactors snfRank snfData
  have hd := (Smith.run_same (Smith.formAccumulator n m)
    (Smith.transformAccumulator n m) A).diag
  apply Vector.toArray_injective
  simp only [Vector.toArray_cast, Smith.Result.diagVector]
  exact congrArg List.toArray hd

/-- The full-data left transform has the recorded right inverse. -/
theorem snfData_left_inv (A : Matrix Int n m) :
    (snfData A).left * (snfData A).leftInv = Matrix.identity n := by
  exact (Smith.run_inverses A).1

/-- The full-data right transform has the recorded right inverse. -/
theorem snfData_right_inv (A : Matrix Int n m) :
    (snfData A).right * (snfData A).rightInv = Matrix.identity m := by
  exact (Smith.run_inverses A).2

/-- The accumulated transforms carry the input to the full-data run's final
working matrix. -/
theorem snfData_mul_eq_run (A : Matrix Int n m) :
    (snfData A).left * A * (snfData A).right =
      (Smith.run (Smith.transformAccumulator n m) A).matrix := by
  exact Smith.run_transform A

/-- Smith rank never exceeds the row dimension. -/
theorem snfRank_le_n (A : Matrix Int n m) : snfRank A ≤ n := by
  have h := Smith.runFuel_diag_le (Smith.formAccumulator n m) (Nat.min n m)
    ({ matrix := A, diag := [],
       accumulator := (Smith.formAccumulator n m).init } : Smith.Result Unit n m)
  change (Smith.run (Smith.formAccumulator n m) A).diag.length ≤ n
  rw [Smith.run]
  have h' : (Smith.runFuel (Smith.formAccumulator n m) (Nat.min n m)
      { matrix := A, diag := [], accumulator := (Smith.formAccumulator n m).init }).diag.length
      ≤ Nat.min n m := by simpa using h
  exact Nat.le_trans h' (Nat.min_le_left n m)

/-- Smith rank never exceeds the column dimension. -/
theorem snfRank_le_m (A : Matrix Int n m) : snfRank A ≤ m := by
  have h := Smith.runFuel_diag_le (Smith.formAccumulator n m) (Nat.min n m)
    ({ matrix := A, diag := [],
       accumulator := (Smith.formAccumulator n m).init } : Smith.Result Unit n m)
  change (Smith.run (Smith.formAccumulator n m) A).diag.length ≤ m
  rw [Smith.run]
  have h' : (Smith.runFuel (Smith.formAccumulator n m) (Nat.min n m)
      { matrix := A, diag := [], accumulator := (Smith.formAccumulator n m).init }).diag.length
      ≤ Nat.min n m := by simpa using h
  exact Nat.le_trans h' (Nat.min_le_right n m)

/-- The full-data rank obeys the row bound. -/
theorem snfData_rank_le_n (A : Matrix Int n m) : (snfData A).rank ≤ n := by
  rw [← snfRank_eq_data]
  exact snfRank_le_n A

/-- The full-data rank obeys the column bound. -/
theorem snfData_rank_le_m (A : Matrix Int n m) : (snfData A).rank ≤ m := by
  rw [← snfRank_eq_data]
  exact snfRank_le_m A

/-- The executable full-data Smith sweep satisfies the complete Smith normal
form contract. -/
theorem snfData_isSNF (A : Matrix Int n m) : IsSNF A (snfData A) := by
  refine
    { left_inv := snfData_left_inv A
      right_inv := snfData_right_inv A
      mul_eq := ?_
      rank_le_n := snfData_rank_le_n A
      rank_le_m := snfData_rank_le_m A
      diag_pos := ?_
      chain := ?_ }
  · rw [snfData_mul_eq_run]
    simpa only [snfData] using
      Smith.run_matrix (Smith.transformAccumulator n m) A
  · intro i
    simp only [snfData] at i ⊢
    change 0 < (Smith.run (Smith.transformAccumulator n m) A).diagVector.get i
    rw [Smith.Result.diagVector_get]
    exact Smith.run_positive (Smith.transformAccumulator n m) A i.val i.isLt
  · intro i hi
    simp only [snfData] at hi ⊢
    change (Smith.run (Smith.transformAccumulator n m) A).diagVector.get
        ⟨i, by omega⟩ ∣
      (Smith.run (Smith.transformAccumulator n m) A).diagVector.get ⟨i + 1, hi⟩
    rw [Smith.Result.diagVector_get, Smith.Result.diagVector_get]
    exact Smith.run_chain (Smith.transformAccumulator n m) A i hi

/-- The form-only path agrees with the diagonal carried by full Smith data. -/
theorem snf_eq_data (A : Matrix Int n m) :
    snf A = diagMatrix (snfData A).diag n m := by
  have hsame := Smith.run_same (Smith.formAccumulator n m)
    (Smith.transformAccumulator n m) A
  rw [snf]
  rw [hsame.matrix]
  simpa only [snfData] using Smith.run_matrix (Smith.transformAccumulator n m) A

/-- The fixed diagonal schedule satisfies the complete Smith contract. -/
theorem snfDiagonalData_isSNF {r : Nat} (d : Vector Int r) :
    IsSNF (diagMatrix d r r) (snfDiagonalData d) := by
  rw [snfDiagonalData]
  let st := Smith.Diagonal.Compact.run (Smith.transformAccumulator r r) d
  let et := Smith.Diagonal.Compact.erase st
  have hvt : Smith.Diagonal.Valid et :=
    Smith.Diagonal.Compact.run_valid (Smith.transformAccumulator r r) d
  rcases hvt with ⟨hrank, hmatrix, hpos, hchain⟩
  dsimp only [et, Smith.Diagonal.Compact.erase] at hrank hmatrix hpos hchain
  have hinv := Smith.Diagonal.Compact.run_inverses d
  refine
    { left_inv := hinv.1
      right_inv := hinv.2
      mul_eq := ?_
      rank_le_n := hrank
      rank_le_m := hrank
      diag_pos := ?_
      chain := ?_ }
  · exact (Smith.Diagonal.Compact.run_transform d).trans hmatrix
  · intro i
    simp only [Smith.Diagonal.Compact.candidateData]
    exact hpos i
  · intro i hi
    simp only [Smith.Diagonal.Compact.candidateData] at hi ⊢
    have hi' : i < (Smith.Diagonal.Compact.collect st.values).length - 1 := by
      dsimp only [st] at hi ⊢
      omega
    exact hchain ⟨i, hi'⟩

/-- The form-only diagonal path agrees with the diagonal carried by the
full-data path. -/
theorem snfDiagonal_eq_data {r : Nat} (d : Vector Int r) :
    snfDiagonal d = diagMatrix (snfDiagonalData d).diag r r := by
  rw [snfDiagonal, snfDiagonalData]
  let sf := Smith.Diagonal.Compact.run (Smith.formAccumulator r r) d
  let st := Smith.Diagonal.Compact.run (Smith.transformAccumulator r r) d
  let et := Smith.Diagonal.Compact.erase st
  have hsame := Smith.Diagonal.Compact.run_same (Smith.formAccumulator r r)
    (Smith.transformAccumulator r r) d
  have hvt : Smith.Diagonal.Valid et :=
    Smith.Diagonal.Compact.run_valid (Smith.transformAccumulator r r) d
  have hm := hvt.2.1
  dsimp only [et, Smith.Diagonal.Compact.erase, Smith.Result.diagVector] at hm
  simp only [Smith.Diagonal.Compact.candidateData]
  rw [Smith.Diagonal.Compact.runValues_eq, hsame.values]
  exact hm

/-- Every invariant factor returned by the form-only path is positive. -/
theorem invariantFactors_pos (A : Matrix Int n m) (i : Fin (snfRank A)) :
    0 < (invariantFactors A)[i] := by
  exact Smith.run_positive (Smith.formAccumulator n m) A i.val i.isLt

/-- The invariant factors returned by the form-only path form a divisibility
chain. -/
theorem invariantFactors_chain (A : Matrix Int n m) (i : Nat)
    (h : i + 1 < snfRank A) :
    (invariantFactors A)[(⟨i, by omega⟩ : Fin (snfRank A))] ∣
      (invariantFactors A)[(⟨i + 1, h⟩ : Fin (snfRank A))] := by
  exact Smith.run_chain (Smith.formAccumulator n m) A i h

end Hex.Matrix
