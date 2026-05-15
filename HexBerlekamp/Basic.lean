import HexMatrix
import HexPolyFp

/-!
Executable Berlekamp-matrix support for `hex-berlekamp`.

This module builds the Berlekamp matrix `Q_f` for a monic polynomial
`f : FpPoly p` by expressing the Frobenius image of each monomial basis vector
in the quotient basis `{1, X, ..., X^(n - 1)}`. It also exposes the fixed-space
matrix `Q_f - I` together with a kernel wrapper that reuses `HexMatrix`'s
nullspace API and converts basis vectors back into polynomial representatives.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- The basis size used for the Berlekamp matrix of `f`. -/
def basisSize (f : FpPoly p) : Nat :=
  f.degree?.getD 0

private theorem size_pos_of_basisSize_pos (f : FpPoly p)
    (h : 0 < basisSize f) : 0 < f.size := by
  by_cases hfz : 0 < f.size
  · exact hfz
  · exfalso
    have hfsize : f.size = 0 := Nat.eq_zero_of_not_pos hfz
    unfold basisSize DensePoly.degree? at h
    simp [hfsize] at h

private theorem basisSize_eq_size_sub_one (f : FpPoly p)
    (h : 0 < f.size) : basisSize f = f.size - 1 := by
  unfold basisSize DensePoly.degree?
  simp [Nat.ne_of_gt h]

/-- Read a polynomial's first `degree f` coefficients as a vector. -/
def coeffVector (f g : FpPoly p) : Vector (ZMod64 p) (basisSize f) :=
  Vector.ofFn fun i => g.coeff i.val

/--
The `j`-th Berlekamp-matrix column, obtained by reducing
`(X^p mod f)^j` modulo `f` and reading the result in the monomial basis.
-/
def berlekampColumn (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (j : Fin (basisSize f)) : Vector (ZMod64 p) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let image := FpPoly.powModMonic frobX f hmonic j.val
  coeffVector f image

/-- The executable `j`-th Berlekamp column represents `X^(p*j)` modulo `f`. -/
theorem berlekampColumn_poly_mod_eq_linearPow_X
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (j : Fin (basisSize f)) :
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
      FpPoly.linearPow FpPoly.X (p * j.val) % f := by
  have hfrob :
      (FpPoly.frobeniusXMod f hmonic) % f =
        FpPoly.linearPow FpPoly.X p % f := by
    unfold FpPoly.frobeniusXMod
    exact FpPoly.powModMonic_mod_eq_linearPow FpPoly.X f hmonic p
  calc
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f
        = FpPoly.linearPow (FpPoly.frobeniusXMod f hmonic) j.val % f :=
            FpPoly.powModMonic_mod_eq_linearPow
              (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
    _ = FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val % f :=
            FpPoly.linearPow_mod_eq_of_mod_eq_mod f
              (FpPoly.frobeniusXMod f hmonic) (FpPoly.linearPow FpPoly.X p)
              j.val hfrob
    _ = FpPoly.linearPow FpPoly.X (p * j.val) % f := by
            rw [FpPoly.linearPow_iterate_mul]

/--
Iteratively build the array of Berlekamp-matrix column polynomials
`[1, frobX, frobX^2, …, frobX^(n - 1)]`, each reduced modulo `f`.
Each step costs one polynomial product and one monic reduction, both
quadratic in `n`, so the array of `n` columns is built in `O(n^3)` total.
-/
private def berlekampColumnPolys (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (frobX : FpPoly p) : Nat → FpPoly p → Array (FpPoly p) → Array (FpPoly p)
  | 0, _, acc => acc
  | k + 1, current, acc =>
      berlekampColumnPolys f hmonic frobX k
        (FpPoly.modByMonic f (current * frobX) hmonic) (acc.push current)

private theorem berlekampColumnPolys_toList_eq_powModMonicLinear
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (frobX : FpPoly p)
    (fuel offset : Nat) (acc : Array (FpPoly p)) :
    (berlekampColumnPolys f hmonic frobX fuel
        (FpPoly.powModMonicLinear frobX f hmonic offset) acc).toList =
      acc.toList ++
        (List.range fuel).map fun k => FpPoly.powModMonicLinear frobX f hmonic (offset + k) := by
  induction fuel generalizing offset acc with
  | zero =>
      simp [berlekampColumnPolys]
  | succ fuel ih =>
      rw [berlekampColumnPolys]
      have hstep :
          FpPoly.modByMonic f
              (FpPoly.powModMonicLinear frobX f hmonic offset * frobX) hmonic =
            FpPoly.powModMonicLinear frobX f hmonic (offset + 1) := by
        change FpPoly.modByMonic f
              (FpPoly.powModMonicLinear frobX f hmonic offset * frobX) hmonic =
            FpPoly.powModMonicLinear frobX f hmonic (offset + 1)
        rw [show offset + 1 = Nat.succ offset by omega]
        rfl
      rw [hstep]
      rw [ih (offset + 1)]
      rw [Array.toList_push]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.append_assoc, List.append_cancel_left_eq]
      apply List.cons_eq_cons.mpr
      constructor
      · rfl
      · apply List.map_congr_left
        intro k _hk
        rw [show offset + 1 + k = offset + Nat.succ k by omega]
        rfl

private theorem array_toList_getD {α : Type}
    (xs : Array α) (i : Nat) (fallback : α) :
    xs.toList.getD i fallback = xs.getD i fallback := by
  cases xs with
  | mk data =>
      rw [List.getD_eq_getElem?_getD]
      unfold Array.getD Array.size Array.getInternal
      by_cases hlt : i < data.length
      · rw [dif_pos hlt]
        simp [List.getElem?_eq_getElem hlt]
      · rw [dif_neg hlt]
        simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hlt)]

private theorem list_getD_map_range
    {α : Type} [Zero α] (fuel n : Nat) (g : Nat → α) (hn : n < fuel) :
    ((List.range fuel).map g).getD n 0 = g n := by
  rw [List.getD_eq_getElem?_getD]
  have hlen : n < ((List.range fuel).map g).length := by
    simp [hn]
  rw [List.getElem?_eq_getElem hlen]
  simp [List.getElem_map, List.getElem_range]

private theorem berlekampColumnPolys_getD_eq_powModMonicLinear
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (frobX : FpPoly p)
    (j : Fin fuel) :
    (berlekampColumnPolys f hmonic frobX fuel
        (FpPoly.powModMonicLinear frobX f hmonic 0) #[]).getD j.val 0 =
      FpPoly.powModMonicLinear frobX f hmonic j.val := by
  have hlist := congrArg (fun xs : List (FpPoly p) => xs.getD j.val 0)
    (berlekampColumnPolys_toList_eq_powModMonicLinear f hmonic frobX fuel 0 #[])
  rw [← array_toList_getD
    (berlekampColumnPolys f hmonic frobX fuel
      (FpPoly.powModMonicLinear frobX f hmonic 0) #[]) j.val 0]
  simpa [list_getD_map_range fuel j.val
      (fun k => FpPoly.powModMonicLinear frobX f hmonic (0 + k)) j.isLt] using hlist

/--
The Berlekamp matrix `Q_f`, whose `j`-th column records the coordinates of
`X^(p * j) mod f` in the basis `{1, X, ..., X^(n - 1)}`. Columns are computed
iteratively from the recurrence `column (j + 1) = column j * (X^p mod f) mod f`
to avoid the per-column fast-exponentiation log factor.
-/
def berlekampMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let polys := berlekampColumnPolys f hmonic frobX (basisSize f) 1 #[]
  Matrix.ofFn fun i j => (polys[j.val]?.getD 0).coeff i.val

/-- A Berlekamp matrix entry is the corresponding coefficient of the executable
column-polynomial array used by `berlekampMatrix`. -/
theorem berlekampMatrix_entry_eq_columnPolys_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampMatrix f hmonic)[i][j] =
      ((berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f) 1 #[])[j.val]?.getD 0).coeff i.val := by
  simp [berlekampMatrix, Matrix.ofFn]

/-- A Berlekamp matrix entry is the corresponding coefficient of the public
`powModMonic` column representative. -/
theorem berlekampMatrix_entry_eq_powModMonic_coeff
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampMatrix f hmonic)[i][j] =
      (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i.val := by
  rw [berlekampMatrix_entry_eq_columnPolys_coeff]
  have hpoly :
      ((berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f) 1 #[])[j.val]?.getD 0) =
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val := by
    rw [← Array.getD_eq_getD_getElem?]
    change (berlekampColumnPolys f hmonic (FpPoly.frobeniusXMod f hmonic)
        (basisSize f)
        (FpPoly.powModMonicLinear (FpPoly.frobeniusXMod f hmonic) f hmonic 0) #[]).getD
        j.val 0 =
      FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
    rw [berlekampColumnPolys_getD_eq_powModMonicLinear]
    exact FpPoly.powModMonicLinear_eq_powModMonic
      (FpPoly.frobeniusXMod f hmonic) f hmonic j.val
  rw [hpoly]

/-- A public Berlekamp column entry is the corresponding coefficient of the
`powModMonic` column representative. -/
theorem berlekampColumn_entry_eq_powModMonic_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (i j : Fin (basisSize f)) :
    (berlekampColumn f hmonic j)[i] =
      (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i.val := by
  simp [berlekampColumn, coeffVector]

/-- The public Berlekamp column representative has the expected `X^(p*j)`
residue modulo `f`. -/
theorem berlekampColumn_powModMonic_mod_eq_linearPow_X
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (j : Fin (basisSize f)) :
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
      FpPoly.linearPow FpPoly.X (p * j.val) % f :=
  berlekampColumn_poly_mod_eq_linearPow_X f hmonic j

/-! ### Berlekamp matrix action on coefficient vectors

The Berlekamp matrix `Q_f` is the matrix of the `g ↦ g^p` map on the
quotient `F_p[X] / (f)` in the basis `{1, X, …, X^(n - 1)}`. Applied to
the coefficient vector of `w` with `w.size ≤ n`, it produces the
coefficient vector of `w^p mod f`. The proof factors through the
compose-form Frobenius identity
`compose w (linearPow X p) = linearPow w p`. -/

/-- Polynomial-level representation of `berlekampMatrix · coeffVector f w`:
the column-scaled sum `Σ_{j < n} C(w.coeff j) · powModMonic frobX f hmonic j`,
where each column is already reduced modulo `f`. -/
private def matrixActionPolySum (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (w : FpPoly p) : FpPoly p :=
  (List.finRange (basisSize f)).foldl
    (fun acc j =>
      acc + DensePoly.C (w.coeff j.val) *
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val)
    0

/-- Coefficient extraction commutes with a `+`-foldl over polynomials. -/
private theorem foldl_add_poly_coeff {α : Type _}
    (xs : List α) (g : α → FpPoly p) (init : FpPoly p) (i : Nat) :
    (xs.foldl (fun acc x => acc + g x) init).coeff i =
      xs.foldl (fun acc x => acc + (g x).coeff i) (init.coeff i) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have h_zero : ((0 : ZMod64 p) + 0) = 0 := by grind
      rw [ih (init + g x), DensePoly.coeff_add init (g x) i h_zero]

/-- `+`-foldl over a list is congruent when the inner step functions agree
pointwise on the list. -/
private theorem foldl_add_congr {α : Type _} {R : Type _} [Add R]
    (xs : List α) (f g : α → R) (init : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) init =
      xs.foldl (fun acc x => acc + g x) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih _ hxs

/-- The coefficient vector of `matrixActionPolySum` (over the first
`basisSize f` indices) is the matrix-vector product
`berlekampMatrix · coeffVector f w`. -/
private theorem coeffVector_matrixActionPolySum_eq_mulVec
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (w : FpPoly p) :
    coeffVector f (matrixActionPolySum f hmonic w) =
      Matrix.mulVec (berlekampMatrix f hmonic) (coeffVector f w) := by
  apply Vector.ext
  intro i hi
  let ii : Fin (basisSize f) := ⟨i, hi⟩
  rw [show (coeffVector f (matrixActionPolySum f hmonic w))[i] =
        (matrixActionPolySum f hmonic w).coeff i from by
      simp [coeffVector]]
  unfold matrixActionPolySum
  rw [foldl_add_poly_coeff (List.finRange (basisSize f))
      (fun j => DensePoly.C (w.coeff j.val) *
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val)
      0 i]
  rw [DensePoly.coeff_zero]
  simp [HMul.hMul, Matrix.mulVec, Matrix.dot, Matrix.row, Hex.Vector.dotProduct]
  apply foldl_add_congr
  intro j _hj
  show (DensePoly.C (w.coeff j.val) *
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i =
    (berlekampMatrix f hmonic)[ii][j] * (coeffVector f w)[j.val]
  rw [FpPoly.C_mul_eq_scale]
  have h_zero : w.coeff j.val * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ h_zero]
  rw [berlekampMatrix_entry_eq_powModMonic_coeff f hmonic ii j]
  rw [show (coeffVector f w)[j.val] = w.coeff j.val from by simp [coeffVector]]
  show w.coeff j.val *
      (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i =
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).coeff i *
      w.coeff j.val
  grind

/-- The `j`-th column polynomial has size at most `basisSize f`, which is
the underlying degree bound of `f`. -/
private theorem powModMonic_column_size_le
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (j : Fin (basisSize f)) :
    (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).size ≤
      basisSize f := by
  have hbasis_pos : 0 < basisSize f := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hf_size_pos : 0 < f.size := size_pos_of_basisSize_pos f hbasis_pos
  have hbasis_eq : basisSize f = f.size - 1 :=
    basisSize_eq_size_sub_one f hf_size_pos
  have hf_deg_eq : f.degree?.getD 0 = f.size - 1 := hbasis_eq
  -- Case split on whether the column is the constant-1 column (j.val = 0)
  -- or a positive power.
  by_cases hj_zero : j.val = 0
  · -- j.val = 0: powModMonic ... 0 = 1
    have h_pow_zero :
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic 0 =
          (1 : FpPoly p) := by
      rw [← FpPoly.powModMonicLinear_eq_powModMonic]
      rfl
    rw [hj_zero, h_pow_zero]
    have hC1 : (1 : FpPoly p) = DensePoly.C (1 : ZMod64 p) := rfl
    rw [hC1]
    exact Nat.le_trans (DensePoly.size_C_le_one _) (by omega : 1 ≤ basisSize f)
  · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj_zero
    -- j.val ≥ 1: powModMonic is self-reduced via powModMonic_pos_self_mod.
    -- Hence degree < f.degree, so size ≤ f.size - 1 = basisSize f.
    have h_self :
        (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
          FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val :=
      FpPoly.powModMonic_pos_self_mod (FpPoly.frobeniusXMod f hmonic) f hmonic
        j.val hj_pos
    -- Translate self-reduction to a size bound.
    have h_deg :
        (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).degree?.getD 0 <
          f.degree?.getD 0 := by
      rw [← h_self]
      exact DensePoly.mod_degree_lt_of_pos_degree _ _ (by rw [hf_deg_eq]; omega)
    -- Convert to a size bound.
    by_cases hsize :
        (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).size = 0
    · rw [hsize]
      exact Nat.zero_le _
    · have hsize_pos :
          0 < (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).size :=
        Nat.pos_of_ne_zero hsize
      have hdeg_eq :
          (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).degree?.getD 0 =
            (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val).size - 1 := by
        unfold DensePoly.degree?
        simp [Nat.ne_of_gt hsize_pos]
      rw [hdeg_eq, hf_deg_eq] at h_deg
      -- Note: avoid rewriting `basisSize f` here because it captures
      -- `Fin (basisSize f)` in `j`'s type, breaking the motive.
      omega

/-- `composeCoeffPowerSumUpTo` written with the last term appended on the
right. -/
private theorem composeCoeffPowerSumUpTo_succ_right
    [ZMod64.PrimeModulus p]
    (coeff : Nat → ZMod64 p) (q : FpPoly p) (n : Nat) :
    ∀ base,
      FpPoly.composeCoeffPowerSumUpTo coeff (n + 1) base q =
        FpPoly.composeCoeffPowerSumUpTo coeff n base q +
          DensePoly.C (coeff (base + n)) * FpPoly.linearPow q (base + n) := by
  induction n with
  | zero =>
      intro base
      show DensePoly.C (coeff base) * FpPoly.linearPow q base + 0 =
        0 + DensePoly.C (coeff (base + 0)) * FpPoly.linearPow q (base + 0)
      rw [Nat.add_zero, FpPoly.zero_add, FpPoly.add_zero]
  | succ n ih =>
      intro base
      show DensePoly.C (coeff base) * FpPoly.linearPow q base +
          FpPoly.composeCoeffPowerSumUpTo coeff (n + 1) (base + 1) q =
        (DensePoly.C (coeff base) * FpPoly.linearPow q base +
          FpPoly.composeCoeffPowerSumUpTo coeff n (base + 1) q) +
        DensePoly.C (coeff (base + (n + 1))) * FpPoly.linearPow q (base + (n + 1))
      rw [ih (base + 1)]
      rw [show base + 1 + n = base + (n + 1) from by omega]
      rw [FpPoly.add_assoc]

/-- `composeCoeffPowerSumUpTo … n 0 q` viewed as the `List.finRange n`-foldl
sum `Σ_{j < n} C(coeff j) · linearPow q j`. -/
private theorem composeCoeffPowerSumUpTo_eq_foldl_finRange
    [ZMod64.PrimeModulus p]
    (coeff : Nat → ZMod64 p) (q : FpPoly p) (n : Nat) :
    FpPoly.composeCoeffPowerSumUpTo coeff n 0 q =
      (List.finRange n).foldl
        (fun acc j => acc + DensePoly.C (coeff j.val) * FpPoly.linearPow q j.val)
        0 := by
  induction n with
  | zero =>
      simp [FpPoly.composeCoeffPowerSumUpTo]
  | succ n ih =>
      rw [composeCoeffPowerSumUpTo_succ_right coeff q n 0]
      rw [Nat.zero_add]
      rw [ih]
      rw [List.finRange_succ_last]
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      -- foldl over (finRange n).map Fin.castSucc = foldl over finRange n
      have hmap :
          ((List.finRange n).map Fin.castSucc).foldl
              (fun acc j =>
                acc + DensePoly.C (coeff j.val) * FpPoly.linearPow q j.val) 0 =
            (List.finRange n).foldl
              (fun acc j =>
                acc + DensePoly.C (coeff j.val) * FpPoly.linearPow q j.val) 0 := by
        rw [List.foldl_map]
        rfl
      rw [hmap]
      -- Fin.last n has val = n.
      simp only [Fin.val_last]

/-- The polynomial `matrixActionPolySum f hmonic w` has size at most
`basisSize f`: each summand has size at most `basisSize f`, and a foldl
of `+` over such summands stays bounded. -/
private theorem foldl_zero_of_each_zero
    {α : Type _} (xs : List α) (g : α → ZMod64 p)
    (h : ∀ x ∈ xs, g x = 0) :
    xs.foldl (fun acc x => acc + g x) (0 : ZMod64 p) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : g x = 0 := h x (by simp)
      have hxs : ∀ y ∈ xs, g y = 0 := fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have h_zero : ((0 : ZMod64 p) + 0) = 0 := by grind
      rw [h_zero]
      exact ih hxs

private theorem poly_size_le_of_coeff_eq_zero_from
    (q : FpPoly p) (bound : Nat) (h : ∀ i, bound ≤ i → q.coeff i = 0) :
    q.size ≤ bound := by
  by_cases hle : q.size ≤ bound
  · exact hle
  · exfalso
    have hgt : bound < q.size := Nat.lt_of_not_ge hle
    have hpos : 0 < q.size := by omega
    have htop_zero : q.coeff (q.size - 1) = 0 := h (q.size - 1) (by omega)
    exact DensePoly.coeff_last_ne_zero_of_pos_size q hpos htop_zero

private theorem matrixActionPolySum_size_le
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (w : FpPoly p) :
    (matrixActionPolySum f hmonic w).size ≤ basisSize f := by
  apply poly_size_le_of_coeff_eq_zero_from (matrixActionPolySum f hmonic w) (basisSize f)
  intro i hi
  unfold matrixActionPolySum
  rw [foldl_add_poly_coeff (List.finRange (basisSize f))
      (fun j => DensePoly.C (w.coeff j.val) *
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val)
      0 i]
  rw [DensePoly.coeff_zero]
  apply foldl_zero_of_each_zero
  intro j _hj
  rw [FpPoly.C_mul_eq_scale]
  have h_zero : w.coeff j.val * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ h_zero]
  have hsize := powModMonic_column_size_le f hmonic j
  rw [DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_trans hsize hi)]
  show w.coeff j.val * (Zero.zero : ZMod64 p) = 0
  rw [show (Zero.zero : ZMod64 p) = 0 from rfl]
  exact h_zero

/-- Modular equivalence of `+`-foldls when init values and each term agree
mod the modulus. -/
private theorem foldl_add_mod_congr {α : Type _} [ZMod64.PrimeModulus p]
    (xs : List α) (g h : α → FpPoly p) (mod : FpPoly p) (init1 init2 : FpPoly p)
    (h_init : init1 % mod = init2 % mod)
    (h_term : ∀ x ∈ xs, (g x) % mod = (h x) % mod) :
    (xs.foldl (fun acc x => acc + g x) init1) % mod =
      (xs.foldl (fun acc x => acc + h x) init2) % mod := by
  induction xs generalizing init1 init2 with
  | nil => exact h_init
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · have h_add1 : (init1 + g x) % mod = ((init1 % mod) + (g x % mod)) % mod :=
          @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
            (ZMod64.instDivModLawsZMod64Fp p) init1 (g x) mod
        have h_add2 : (init2 + h x) % mod = ((init2 % mod) + (h x % mod)) % mod :=
          @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
            (ZMod64.instDivModLawsZMod64Fp p) init2 (h x) mod
        rw [h_add1, h_add2, h_init, h_term x (by simp)]
      · intro y hy
        exact h_term y (List.mem_cons_of_mem _ hy)

/-- The matrix-action polysum agrees modulo `f` with the corresponding
`linearPow X (p · j)`-sum. -/
private theorem matrixActionPolySum_mod_eq_polySumLin_mod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (w : FpPoly p) :
    matrixActionPolySum f hmonic w % f =
      (List.finRange (basisSize f)).foldl
        (fun acc j =>
          acc + DensePoly.C (w.coeff j.val) *
            FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val)
        0 % f := by
  unfold matrixActionPolySum
  apply foldl_add_mod_congr
  · rfl
  intro j _hj
  -- Each column polynomial is congruent to its `linearPow` analogue modulo `f`.
  show (DensePoly.C (w.coeff j.val) *
        FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
      (DensePoly.C (w.coeff j.val) *
        FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val) % f
  have h_mm1 :
      (DensePoly.C (w.coeff j.val) *
          FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val) % f =
        ((DensePoly.C (w.coeff j.val) % f) *
          (FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val % f)) % f :=
    @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ f
  have h_mm2 :
      (DensePoly.C (w.coeff j.val) *
          FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val) % f =
        ((DensePoly.C (w.coeff j.val) % f) *
          (FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val % f)) % f :=
    @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ f
  rw [h_mm1, h_mm2]
  congr 1
  congr 1
  have h1 :
      FpPoly.powModMonic (FpPoly.frobeniusXMod f hmonic) f hmonic j.val % f =
        FpPoly.linearPow (FpPoly.frobeniusXMod f hmonic) j.val % f :=
    FpPoly.powModMonic_mod_eq_linearPow _ f hmonic j.val
  have h2 :
      FpPoly.linearPow (FpPoly.frobeniusXMod f hmonic) j.val % f =
        FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val % f := by
    apply FpPoly.linearPow_mod_eq_of_mod_eq_mod
    show FpPoly.frobeniusXMod f hmonic % f = FpPoly.linearPow FpPoly.X p % f
    unfold FpPoly.frobeniusXMod
    exact FpPoly.powModMonic_mod_eq_linearPow FpPoly.X f hmonic p
  exact h1.trans h2

/-- The matrix-action polysum equals `linearPow w p mod f` when `w.size`
fits in the basis. -/
private theorem matrixActionPolySum_eq_linearPow_mod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (w : FpPoly p)
    (hw : w.size ≤ basisSize f) :
    matrixActionPolySum f hmonic w = FpPoly.linearPow w p % f := by
  -- Step 1: polySum mod f = polySumLin mod f.
  have hmod1 :
      matrixActionPolySum f hmonic w % f =
        (List.finRange (basisSize f)).foldl
          (fun acc j =>
            acc + DensePoly.C (w.coeff j.val) *
              FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val)
          0 % f :=
    matrixActionPolySum_mod_eq_polySumLin_mod f hmonic w
  -- Step 2: polySumLin = compose w (linearPow X p) = linearPow w p.
  have hsum :
      (List.finRange (basisSize f)).foldl
          (fun acc j =>
            acc + DensePoly.C (w.coeff j.val) *
              FpPoly.linearPow (FpPoly.linearPow FpPoly.X p) j.val)
          0 = FpPoly.linearPow w p := by
    rw [← composeCoeffPowerSumUpTo_eq_foldl_finRange (fun i => w.coeff i)
        (FpPoly.linearPow FpPoly.X p) (basisSize f)]
    rw [← FpPoly.compose_eq_coeff_power_sum_upTo_bound w (FpPoly.linearPow FpPoly.X p) hw]
    exact FpPoly.compose_w_linearPow_X w
  rw [hsum] at hmod1
  -- Step 3: polySum is self-reduced since its size is ≤ basisSize f.
  have hself : matrixActionPolySum f hmonic w % f = matrixActionPolySum f hmonic w := by
    have hsize := matrixActionPolySum_size_le f hmonic w
    by_cases h_basis_zero : basisSize f = 0
    · -- basisSize f = 0 means polySum.size = 0, so polySum = 0.
      rw [h_basis_zero] at hsize
      have h_zero : matrixActionPolySum f hmonic w = 0 := by
        apply DensePoly.ext_coeff
        intro n
        show (matrixActionPolySum f hmonic w).coeff n = (0 : FpPoly p).coeff n
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega : _ ≤ n)]
        rw [DensePoly.coeff_zero]
        rfl
      rw [h_zero]
      exact DensePoly.zero_mod_eq_zero_core (S := ZMod64 p) f
    · apply DensePoly.mod_eq_self_of_degree_lt
      have hbasis_pos : 0 < basisSize f := Nat.pos_of_ne_zero h_basis_zero
      have hf_size_pos : 0 < f.size := size_pos_of_basisSize_pos f hbasis_pos
      have hbasis_eq : basisSize f = f.size - 1 :=
        basisSize_eq_size_sub_one f hf_size_pos
      have hf_deg_eq : f.degree?.getD 0 = f.size - 1 := hbasis_eq
      by_cases h_poly_size : (matrixActionPolySum f hmonic w).size = 0
      · have h_poly_deg :
            (matrixActionPolySum f hmonic w).degree?.getD 0 = 0 := by
          unfold DensePoly.degree?
          simp [h_poly_size]
        rw [h_poly_deg, hf_deg_eq]
        omega
      · have h_poly_pos : 0 < (matrixActionPolySum f hmonic w).size :=
          Nat.pos_of_ne_zero h_poly_size
        have h_poly_deg :
            (matrixActionPolySum f hmonic w).degree?.getD 0 =
              (matrixActionPolySum f hmonic w).size - 1 := by
          unfold DensePoly.degree?
          simp [Nat.ne_of_gt h_poly_pos]
        rw [h_poly_deg, hf_deg_eq]
        omega
  -- Combine: polySum = polySum % f = linearPow w p % f.
  rw [← hself]
  exact hmod1

/-- The Berlekamp matrix acts on the basis-`{1, X, …, X^(n-1)}` coefficient
vector of `w` as the Frobenius map on `F_p[X] / (f)`: when `w` has degree
less than `n = basisSize f`, multiplying `coeffVector f w` by
`berlekampMatrix f hmonic` returns the coefficient vector of
`w^p mod f`. The proof factors through the compose-form Frobenius identity
`compose w (linearPow X p) = linearPow w p` from `HexPolyFp/Compose.lean`. -/
theorem berlekampMatrix_mulVec_coeffVector_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (w : FpPoly p)
    (hw : w.size ≤ basisSize f) :
    Matrix.mulVec (berlekampMatrix f hmonic) (coeffVector f w) =
      coeffVector f (FpPoly.linearPow w p % f) := by
  rw [← coeffVector_matrixActionPolySum_eq_mulVec f hmonic w]
  rw [matrixActionPolySum_eq_linearPow_mod f hmonic w hw]

/-- The fixed-space matrix `Q_f - I` used in Berlekamp's kernel computation. -/
def fixedSpaceMatrix (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Ring (ZMod64 p)] :
    Matrix (ZMod64 p) (basisSize f) (basisSize f) :=
  let Q := berlekampMatrix f hmonic
  Matrix.ofFn fun i j =>
    @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
      (@instHSub (ZMod64 p) inst.toSub) Q[i][j]
      (if i = j then
        @OfNat.ofNat (ZMod64 p) 1 (inst.toSemiring.ofNat 1)
      else
        @OfNat.ofNat (ZMod64 p) 0 (inst.toSemiring.ofNat 0))

/-- Convert a coefficient vector back to its polynomial representative. -/
def vectorToPoly {n : Nat} (v : Vector (ZMod64 p) n) : FpPoly p :=
  FpPoly.ofCoeffs v.toArray

/-- Re-reading the coefficients of a polynomial built from a Berlekamp-basis
coefficient vector recovers the original vector. -/
theorem coeffVector_vectorToPoly (f : FpPoly p) (v : Vector (ZMod64 p) (basisSize f)) :
    coeffVector f (vectorToPoly v) = v := by
  apply Vector.ext
  intro i hi
  simp [coeffVector, vectorToPoly, FpPoly.ofCoeffs]

/--
The fixed-space kernel of `Q_f - I`, reusing `HexMatrix.nullspace` instead of a
Berlekamp-local linear-algebra implementation.
-/
def fixedSpaceKernelVectors (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] :
    Vector (Vector (ZMod64 p) (basisSize f))
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) :=
  Matrix.nullspace (fixedSpaceMatrix (inst := inst.toRing) f hmonic)

/-- The fixed-space kernel basis converted back to polynomial representatives. -/
def fixedSpaceKernel (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] :
    Vector (FpPoly p)
      (basisSize f - Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) :=
  Vector.ofFn fun i => vectorToPoly ((fixedSpaceKernelVectors f hmonic).get i)

/-- Vector-level executable Berlekamp kernel condition for the fixed-space
matrix `Q_f - I`. -/
def IsFixedSpaceKernelVector (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (v : Vector (ZMod64 p) (basisSize f)) [inst : Lean.Grind.Field (ZMod64 p)] : Prop :=
  @HMul.hMul (Matrix (ZMod64 p) (basisSize f) (basisSize f))
      (Vector (ZMod64 p) (basisSize f)) (Vector (ZMod64 p) (basisSize f))
      (@Matrix.instHMulVectorOfMulOfAddOfOfNatOfNatNat
        (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0))
      (fixedSpaceMatrix (inst := inst.toRing) f hmonic) v =
    @OfNat.ofNat (Vector (ZMod64 p) (basisSize f)) 0
      (@Zero.toOfNat0 (Vector (ZMod64 p) (basisSize f))
        (@Vector.instZero (ZMod64 p) (basisSize f)
          (@Zero.ofOfNat0 (ZMod64 p)
            (@Lean.Grind.Semiring.ofNat (ZMod64 p) inst.toCommSemiring.toSemiring 0))))

private theorem vector_sub_eq_zero_iff_eq [Lean.Grind.Ring R] (u v : Vector R n) :
    u - v = 0 ↔ u = v := by
  constructor
  · intro h
    apply Vector.ext
    intro i hi
    have hget := congrArg (fun w : Vector R n => w[i]) h
    grind
  · intro h
    rw [h]
    apply Vector.ext
    intro i hi
    grind

/-- The executable kernel predicate for `Q_f - I` is equivalent to the usual
fixed-space equation `Q_f * v = v`. -/
theorem isFixedSpaceKernelVector_iff_berlekampMatrix_mulVec_eq
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] (v : Vector (ZMod64 p) (basisSize f)) :
    IsFixedSpaceKernelVector f hmonic v ↔
      @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v = v := by
  unfold IsFixedSpaceKernelVector
  dsimp only [fixedSpaceMatrix]
  letI : Lean.Grind.Ring (ZMod64 p) := inst.toRing
  change
    @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0)
        (Matrix.ofFn fun i j =>
          @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
            (@instHSub (ZMod64 p) inst.toSub) (berlekampMatrix f hmonic)[i][j]
            (if i = j then
              @OfNat.ofNat (ZMod64 p) 1 (inst.toCommSemiring.toSemiring.ofNat 1)
            else
              @OfNat.ofNat (ZMod64 p) 0 (inst.toCommSemiring.toSemiring.ofNat 0))) v =
      @OfNat.ofNat (Vector (ZMod64 p) (basisSize f)) 0
        (@Zero.toOfNat0 (Vector (ZMod64 p) (basisSize f))
          (@Vector.instZero (ZMod64 p) (basisSize f)
            (@Zero.ofOfNat0 (ZMod64 p)
              (@Lean.Grind.Semiring.ofNat (ZMod64 p) inst.toCommSemiring.toSemiring 0)))) ↔
    @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
        inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
        (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v = v
  have hsub :
      @Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
          inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
          (inst.toCommSemiring.toSemiring.ofNat 0)
          (Matrix.ofFn fun i j =>
            @HSub.hSub (ZMod64 p) (ZMod64 p) (ZMod64 p)
              (@instHSub (ZMod64 p) inst.toSub) (berlekampMatrix f hmonic)[i][j]
              (if i = j then
                @OfNat.ofNat (ZMod64 p) 1 (inst.toCommSemiring.toSemiring.ofNat 1)
              else
                @OfNat.ofNat (ZMod64 p) 0 (inst.toCommSemiring.toSemiring.ofNat 0))) v =
        @HSub.hSub (Vector (ZMod64 p) (basisSize f))
          (Vector (ZMod64 p) (basisSize f)) (Vector (ZMod64 p) (basisSize f))
          (@instHSub (Vector (ZMod64 p) (basisSize f))
            (@Vector.instSub (ZMod64 p) (basisSize f) inst.toSub))
          (@Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v) v :=
    Matrix.sub_identity_mulVec (berlekampMatrix f hmonic) v
  rw [hsub]
  exact vector_sub_eq_zero_iff_eq
    (@Matrix.mulVec (ZMod64 p) (basisSize f) (basisSize f)
      inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
      (inst.toCommSemiring.toSemiring.ofNat 0) (berlekampMatrix f hmonic) v) v

/-- Polynomial-level executable Berlekamp kernel condition, by reading the
representative in the quotient basis used by `fixedSpaceMatrix`. -/
def IsFixedSpaceKernelPolynomial (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (g : FpPoly p) [Lean.Grind.Field (ZMod64 p)] : Prop :=
  IsFixedSpaceKernelVector f hmonic (coeffVector f g)

/-- Every vector returned by `fixedSpaceKernelVectors` satisfies the executable
fixed-space kernel condition. -/
theorem fixedSpaceKernelVectors_sound (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)]
    (k : Fin (basisSize f -
      Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))) :
    IsFixedSpaceKernelVector f hmonic ((fixedSpaceKernelVectors f hmonic).get k) := by
  unfold IsFixedSpaceKernelVector fixedSpaceKernelVectors
  exact Matrix.nullspace_sound (fixedSpaceMatrix (inst := inst.toRing) f hmonic) k

/-- Every polynomial representative returned by `fixedSpaceKernel` satisfies the
executable fixed-space kernel condition. -/
theorem fixedSpaceKernel_sound (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)]
    (k : Fin (basisSize f -
      Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))) :
    IsFixedSpaceKernelPolynomial f hmonic ((fixedSpaceKernel f hmonic).get k) := by
  unfold IsFixedSpaceKernelPolynomial fixedSpaceKernel
  rw [Vector.get_ofFn, coeffVector_vectorToPoly]
  exact fixedSpaceKernelVectors_sound f hmonic k

/-- Every vector satisfying the executable fixed-space kernel condition is a
linear combination of the public nullspace-basis matrix for `Q_f - I`. -/
theorem fixedSpaceKernelVectors_complete (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [inst : Lean.Grind.Field (ZMod64 p)] (v : Vector (ZMod64 p) (basisSize f)) :
    IsFixedSpaceKernelVector f hmonic v →
      ∃ c : Vector (ZMod64 p)
          (basisSize f -
            Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)),
        @Matrix.mulVec (ZMod64 p) (basisSize f)
            (basisSize f -
              Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0)
            (Matrix.nullspaceBasisMatrix
              (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) c = v := by
  intro hv
  exact Matrix.nullspace_complete (fixedSpaceMatrix (inst := inst.toRing) f hmonic) v hv

/-- Polynomial representatives satisfying the executable fixed-space kernel
condition have coefficient vectors in the span of the nullspace basis. -/
theorem fixedSpaceKernelPolynomial_coeffVector_complete (f : FpPoly p)
    (hmonic : DensePoly.Monic f) [inst : Lean.Grind.Field (ZMod64 p)] (g : FpPoly p) :
    IsFixedSpaceKernelPolynomial f hmonic g →
      ∃ c : Vector (ZMod64 p)
          (basisSize f -
            Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic)),
        @Matrix.mulVec (ZMod64 p) (basisSize f)
            (basisSize f -
              Matrix.rref_rank (fixedSpaceMatrix (inst := inst.toRing) f hmonic))
            inst.toCommSemiring.toMul inst.toCommSemiring.toAdd
            (inst.toCommSemiring.toSemiring.ofNat 0)
            (Matrix.nullspaceBasisMatrix
              (fixedSpaceMatrix (inst := inst.toRing) f hmonic)) c = coeffVector f g := by
  intro hg
  exact fixedSpaceKernelVectors_complete f hmonic (coeffVector f g) hg

end Berlekamp

end Hex
