/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.CharPoly
public import HexMatrix.Certificate
public import HexMatrix.Lists

public section

/-! Packed integer-list certificates for the Berkowitz recursion. -/

namespace Hex.Matrix.CharPolyKernel

/-- The maximum absolute value in a coefficient list. -/
@[expose] def maxAbs : List Int → Nat
  | [] => 0
  | x :: xs => Nat.max x.natAbs (maxAbs xs)

/-- The maximum absolute value in a list of rows. -/
@[expose] def maxRows : List (List Int) → Nat
  | [] => 0
  | x :: xs => Nat.max (maxAbs x) (maxRows xs)

/-- Every coefficient is at most the supplied absolute bound. -/
@[expose] def bounded (b : Nat) : List Int → Bool
  | [] => true
  | x :: xs => Nat.ble x.natAbs b && bounded b xs

/-- An absolute bound on every entry of every row. -/
@[expose] def boundedRows (b : Nat) : List (List Int) → Bool
  | [] => true
  | x :: xs => bounded b x && boundedRows b xs

/-- The radix for balanced signed digits. -/
@[expose] def radix (K : Nat) : Int := Int.ofNat (Nat.pow 2 K)

/-- Pack a row in balanced base `2^K`. -/
@[expose] def pack (K : Nat) : List Int → Int
  | [] => 0
  | x :: xs => Int.add x (Int.shiftLeft (pack K xs) K)

/-- Pack every row at the same width. -/
@[expose] def packs (K : Nat) : List (List Int) → List Int
  | [] => []
  | r :: rs => pack K r :: packs K rs

/-- Add a scaled row, padding the shorter operand with zeros. -/
@[expose] def addScaled (z : Int) : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs.map (Int.mul z)
  | x :: xs, y :: ys => Int.add (Int.mul z x) y :: addScaled z xs ys

/-- A linear combination of rows, with an explicit output dimension. -/
@[expose] def combine (m : Nat) : List Int → List (List Int) → List Int
  | z :: zs, r :: rs => addScaled z r (combine m zs rs)
  | _, _ => List.replicate m 0

/-- Check a linear combination by one dot product of packed rows. -/
@[expose] def checkCombination (K : Nat) (coefficients packedRows result : List Int) : Bool :=
  decide (Lists.dot coefficients packedRows = pack K result)

theorem radix_eq (K : Nat) : radix K = (2 : Int) ^ K := by
  rfl

theorem pack_nil (K : Nat) : pack K [] = 0 := rfl

theorem pack_cons (K : Nat) (x : Int) (xs : List Int) :
    pack K (x :: xs) = x + radix K * pack K xs := by
  change x + (pack K xs <<< K) = _
  rw [Int.shiftLeft_eq, radix_eq, Int.mul_comm]

theorem pack_eq (K : Nat) (xs : List Int) :
    pack K xs = Hex.Internal.packDigits ((2 : Int) ^ K) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pack_cons, Hex.Internal.packDigits, radix_eq, ih]

theorem bounded_iff (b : Nat) (xs : List Int) :
    bounded b xs = true ↔ ∀ x ∈ xs, x.natAbs ≤ b := by
  induction xs with
  | nil => simp [bounded]
  | cons x xs ih => simp [bounded, ih]

theorem boundedRows_iff (b : Nat) (rs : List (List Int)) :
    boundedRows b rs = true ↔ ∀ r ∈ rs, ∀ x ∈ r, x.natAbs ≤ b := by
  induction rs with
  | nil => simp [boundedRows]
  | cons r rs ih => simp [boundedRows, bounded_iff, ih]

theorem pack_addScaled (K : Nat) (z : Int) (xs ys : List Int) :
    pack K (addScaled z xs ys) = z * pack K xs + pack K ys := by
  induction xs generalizing ys with
  | nil => simp [addScaled, pack_nil]
  | cons x xs ih =>
    cases ys with
    | nil =>
      have he : addScaled z xs [] = xs.map (Int.mul z) := by cases xs <;> rfl
      have h := ih []
      rw [he] at h
      simp only [addScaled, pack_cons, pack_nil, List.map_cons] at h ⊢
      rw [h]
      change z * x + radix K * (z * pack K xs + 0) =
        z * (x + radix K * pack K xs) + 0
      simp only [Int.add_zero, Int.mul_add, Int.mul_left_comm]
    | cons y ys =>
      simp only [addScaled, pack_cons, ih]
      grind

theorem pack_zeros (K m : Nat) : pack K (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, pack_cons, ih]

theorem pack_combine (K m : Nat) (zs : List Int) (rs : List (List Int)) :
    pack K (combine m zs rs) = Lists.dot zs (packs K rs) := by
  induction zs generalizing rs with
  | nil => simp [combine, Lists.dot, pack_zeros]
  | cons z zs ih =>
    cases rs with
    | nil => simp [combine, packs, Lists.dot, pack_zeros]
    | cons r rs => simp [combine, pack_addScaled, ih, packs, Lists.dot]

theorem length_addScaled (z : Int) (xs ys : List Int) :
    (addScaled z xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addScaled]
  | cons x xs ih => cases ys <;> simp [addScaled, ih, Nat.succ_max_succ]

theorem length_combine (m : Nat) (zs : List Int) (rs : List (List Int))
    (h : ∀ r ∈ rs, r.length = m) : (combine m zs rs).length = m := by
  induction zs generalizing rs with
  | nil => simp [combine]
  | cons z zs ih =>
    cases rs with
    | nil => simp [combine]
    | cons r rs =>
      rw [combine, length_addScaled, h r (by simp), ih rs (by simp_all)]
      simp

theorem bound_addScaled (z : Int) (xs ys : List Int) (a b : Nat)
    (hx : ∀ x ∈ xs, x.natAbs ≤ a) (hy : ∀ y ∈ ys, y.natAbs ≤ b) :
    ∀ v ∈ addScaled z xs ys, v.natAbs ≤ z.natAbs * a + b := by
  induction xs generalizing ys with
  | nil => simpa [addScaled] using fun v hv => Nat.le_trans (hy v hv) (by omega)
  | cons x xs ih =>
    cases ys with
    | nil =>
      intro v hv
      simp only [addScaled, List.mem_map] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      change (z * u).natAbs ≤ _
      rw [Int.natAbs_mul]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (hx u hu)) (by omega)
    | cons y ys =>
      intro v hv
      simp only [addScaled, List.mem_cons] at hv
      rcases hv with rfl | hv
      · have ha := Nat.mul_le_mul_left z.natAbs (hx x (by simp))
        have hb := hy y (by simp)
        change (z * x + y).natAbs ≤ _
        have ht := Int.natAbs_add_le (z * x) y
        rw [Int.natAbs_mul] at ht
        omega
      · exact ih ys (by simp_all) (by simp_all) v hv

theorem bound_combine (m : Nat) (zs : List Int) (rs : List (List Int)) (b : Nat)
    (hz : ∀ z ∈ zs, z.natAbs ≤ b)
    (hr : ∀ r ∈ rs, ∀ x ∈ r, x.natAbs ≤ b) :
    ∀ v ∈ combine m zs rs, v.natAbs ≤ zs.length * (b * b) := by
  induction zs generalizing rs with
  | nil => simp [combine]
  | cons z zs ih =>
    cases rs with
    | nil => simp [combine]
    | cons r rs =>
      intro v hv
      have ht := bound_addScaled z r (combine m zs rs) b (zs.length * (b * b))
        (hr r (by simp)) (ih rs (fun u hu => hz u (by simp [hu]))
          (fun r hr' => hr r (by simp [hr']))) v hv
      have hz' := Nat.mul_le_mul_right b (hz z (by simp))
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- Balanced-digit injectivity recovers every entry of the linear combination. -/
theorem combine_eq_of_check {K n m b : Nat} {zs : List Int} {rs : List (List Int)}
    {result : List Int} (hlen : result.length = m) (hrlen : ∀ r ∈ rs, r.length = m)
    (hzlen : zs.length ≤ n) (hz : bounded b zs = true)
    (hr : boundedRows b rs = true) (hout : bounded b result = true)
    (hwidth : 2 * (n * (b * b) + b) < 2 ^ K)
    (h : checkCombination K zs (packs K rs) result = true) :
    combine m zs rs = result := by
  apply Hex.Internal.packDigits_inj K
  · rw [length_combine m zs rs hrlen, hlen]
  · intro x hx
    have hbound := bound_combine m zs rs b ((bounded_iff ..).mp hz)
      ((boundedRows_iff ..).mp hr) x hx
    have hmul := Nat.mul_le_mul_right (b * b) hzlen
    omega
  · intro x hx
    have hbound := (bounded_iff ..).mp hout x hx
    omega
  · rw [← pack_eq, ← pack_eq, pack_combine]
    exact of_decide_eq_true h


/-- List dot products agree with the reference finite fold. -/
theorem dot_ofFn (n : Nat) (f g : Fin n → Int) :
    Lists.dot (List.ofFn f) (List.ofFn g) =
      (List.finRange n).foldl (fun acc i => acc + f i * g i) 0 := by
  induction n with
  | zero => simp [Lists.dot]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Lists.dot, ih,
      List.finRange_succ, List.foldl_cons, List.foldl_map]
    conv => rhs; rw [List.foldl_add_eq_add_foldl]
    simp only [Int.zero_add]
    rfl

/-- List representation of a vector. -/
theorem ofFn_vector {n : Nat} (v : Vector Int n) : List.ofFn (fun i : Fin n => v[i]) = v.toList := by
  apply List.ext_getElem <;> simp

/-- The list dot product has the public vector semantics. -/
theorem dot_toList {n : Nat} (u v : Vector Int n) :
    Lists.dot u.toList v.toList = u.dotProduct v := by
  rw [← ofFn_vector u, ← ofFn_vector v, dot_ofFn]
  rfl

/-- Entry of a padded scaled sum. -/
theorem getD_addScaled (z : Int) (xs ys : List Int) (i : Nat) :
    (addScaled z xs ys).getD i 0 = z * xs.getD i 0 + ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp [addScaled]
  | cons x xs ih =>
    cases ys with
    | nil =>
      cases i with
      | zero => simp [addScaled]
      | succ i =>
        have he : addScaled z xs [] = xs.map (Int.mul z) := by cases xs <;> rfl
        simpa only [addScaled, List.map_cons, List.getD_cons_succ, List.getD_nil,
          he] using ih [] i
    | cons y ys => cases i <;> simp only [addScaled, List.getD_cons_zero,
        List.getD_cons_succ, ih] <;> rfl

theorem getD_zeros (m i : Nat) : (List.replicate m (0 : Int)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- An entry of a row combination is a list dot product. -/
theorem getD_combine (m : Nat) (zs : List Int) (rs : List (List Int)) (i : Nat) :
    (combine m zs rs).getD i 0 = Lists.dot zs (rs.map (fun r => r.getD i 0)) := by
  induction zs generalizing rs with
  | nil => simp only [combine, Lists.dot, getD_zeros]
  | cons z zs ih => cases rs <;> simp only [combine, Lists.dot, getD_addScaled, ih,
      getD_zeros, List.map_nil, List.map_cons] <;> rfl


/-- The rows of a matrix, used only in the soundness theorem and producer. -/
def toRows {n m : Nat} (A : Matrix Int n m) : List (List Int) :=
  List.ofFn fun i => (row A i).toList

/-- Remove the first entry of each row. -/
@[expose] def tails : List (List Int) → List (List Int)
  | [] => []
  | r :: rs => r.tail :: tails rs

/-- The first entry of each row, with zero padding. -/
@[expose] def heads : List (List Int) → List Int
  | [] => []
  | r :: rs => r.headD 0 :: heads rs

/-- Transpose by walking each remaining row once per column. -/
@[expose] def columns : Nat → List (List Int) → List (List Int)
  | 0, _ => []
  | k + 1, rs => heads rs :: columns k (tails rs)

/-- The moment vectors and descending coefficients for one Berkowitz step. -/
structure Step where
  column : List Int
  vectors : List (List Int)
  coefficients : List Int
  /-- Packed block columns, validated once before the moment loop. -/
  packedColumns : List Int := []
  /-- Full convolution; its initial coefficients are the Toeplitz product. -/
  product : List Int := []
  deriving Repr, Inhabited, DecidableEq

/-- List equality with direct integer comparison. -/
@[expose] def eqList : List Int → List Int → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && eqList xs ys
  | _, _ => false

/-- Shape, bound and packed identity for the output of a row combination.
The rows are packed and their bounds checked once by the enclosing step. -/
@[expose] def checkLinear (K b n m : Nat) (zs prs result : List Int) : Bool :=
  Nat.beq zs.length n && Nat.beq result.length m && bounded b zs && bounded b result &&
    checkCombination K zs prs result

/-- Check successive scalar moments and packed matrix-vector products. -/
@[expose] def checkMoments (K b k : Nat) (row prs : List Int) :
    List Int → List (List Int) → List Int → Bool
  | [], [], _ => true
  | [t], [], w => (t == Int.neg (Lists.dot row w))
  | t :: ts, v :: vs, w => (t == Int.neg (Lists.dot row w)) &&
      checkLinear K b k k w prs v && checkMoments K b k row prs ts vs v
  | _, _, _ => false

/-- Validate row lengths structurally. -/
@[expose] def rowLengths (m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length m && rowLengths m rs

/-- Check the full Toeplitz convolution with one packed multiplication. -/
@[expose] def checkProduct (K b k : Nat) (prev column product result : List Int) : Bool :=
  Nat.beq product.length (2 * k + 2) && bounded b prev && bounded b column && bounded b product &&
    eqList (product.take (k + 2)) result &&
    (Int.mul (pack K prev) (pack K column) == pack K product)

/-- Check the recursion from the largest block down to the empty matrix. -/
@[expose] def checkSteps (K b : Nat) : Nat → List (List Int) → List Step → List Int → Bool
  | 0, [], [], result => eqList result [1]
  | k + 1, (a :: r) :: rs, c :: cs, result =>
      let block := tails rs
      let cols := columns k block
      let prev := match cs with | [] => [1] | d :: _ => d.coefficients
      eqList result c.coefficients &&
      Nat.beq c.column.length (k + 2) &&
      eqList (c.column.take 2) [1, Int.neg a] &&
      boundedRows b cols && rowLengths k cols &&
      eqList c.packedColumns (packs K cols) &&
      checkMoments K b k r c.packedColumns (c.column.drop 2) c.vectors (heads rs) &&
      checkProduct K b k prev c.column c.product c.coefficients &&
      checkSteps K b k block cs prev
  | _, _, _, _ => false

/-- A width and bound are part of the certificate, and validated by the checker. -/
structure Witness where
  bound : Nat
  width : Nat
  steps : List Step
  deriving Repr, Inhabited, DecidableEq

/-- Kernel-form Berkowitz certificate over integer lists. -/
@[expose] def checkCharPolyList (n : Nat) (rows : List (List Int))
    (w : Witness) (result : List Int) : Bool :=
  Nat.beq rows.length n && rowLengths n rows &&
    Nat.blt (2 * ((n + 1) * (w.bound * w.bound) + w.bound)) (Nat.pow 2 w.width) &&
    checkSteps w.width w.bound n rows w.steps result


theorem eqList_iff (xs ys : List Int) : eqList xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eqList]
  | cons x xs ih => cases ys <;> simp [eqList, ih]

theorem rowLengths_iff (m : Nat) (rs : List (List Int)) :
    rowLengths m rs = true ↔ ∀ r ∈ rs, r.length = m := by
  induction rs with
  | nil => simp [rowLengths]
  | cons r rs ih => simp [rowLengths, ih]

theorem getD_ofFn {n : Nat} (f : Fin n → Int) (i : Fin n) :
    (List.ofFn f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem combine_ofFn (m n : Nat) (z : Fin n → Int) (r : Fin n → Fin m → Int) :
    combine m (List.ofFn z) (List.ofFn fun j => List.ofFn (r j)) =
      List.ofFn (fun i => (List.finRange n).foldl (fun acc j => acc + z j * r j i) 0) := by
  have hl : (combine m (List.ofFn z) (List.ofFn fun j => List.ofFn (r j))).length = m :=
    length_combine _ _ _ (by simp [List.mem_ofFn])
  apply List.ext_getElem
  · simpa using hl
  · intro i hi hj
    have hi' : i < m := by simpa [hl] using hi
    have h := getD_combine m (List.ofFn z) (List.ofFn fun j => List.ofFn (r j)) i
    rw [List.map_ofFn] at h
    simp only [dot_ofFn] at h
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hi'] using h

theorem tails_map (rs : List (List Int)) : tails rs = rs.map List.tail := by
  induction rs <;> simp [tails, *]

theorem heads_map (rs : List (List Int)) : heads rs = rs.map (fun r => r.headD 0) := by
  induction rs <;> simp [heads, *]

theorem columns_ofFn (n m : Nat) (a : Fin n → Fin m → Int) :
    columns m (List.ofFn fun i => List.ofFn (a i)) =
      List.ofFn fun j => List.ofFn fun i => a i j := by
  induction m with
  | zero => simp [columns]
  | succ m ih =>
    rw [columns, List.ofFn_succ]
    congr 1
    · simp [heads_map, List.map_ofFn, List.ofFn_succ, Function.comp_def]
    · simp only [tails_map, List.map_ofFn, List.ofFn_succ, Function.comp_def, List.tail_cons]
      exact ih _


/-- A checked packed combination recovers a matrix-vector product. -/
theorem checkLinear_mulVec {K b k : Nat} (B : Matrix Int k k) (w : Vector Int k)
    (result : List Int)
    (hb : boundedRows b (columns k (toRows B)) = true)
    (hw : 2 * (k * (b * b) + b) < 2 ^ K)
    (hc : checkLinear K b k k w.toList (packs K (columns k (toRows B))) result = true) :
    result = (B * w).toList := by
  simp only [checkLinear, Bool.and_eq_true, Nat.beq_eq] at hc
  have hrows : columns k (toRows B) = List.ofFn (fun j : Fin k => List.ofFn fun i : Fin k => B[i][j]) := by
    simp only [toRows, ← ofFn_vector, getElem_row, columns_ofFn]
  rw [hrows] at hb hc
  have h := combine_eq_of_check hc.1.1.1.2 (by simp [List.mem_ofFn])
    (n := k) (by simp) hc.1.1.2 hb hc.1.2 hw hc.2
  rw [← ofFn_vector w, combine_ofFn] at h
  rw [← h, ← ofFn_vector]
  congr 1
  funext i
  simp only [getElem_mulVec, Vector.dotProduct, getElem_row]
  apply List.foldl_add_congr
  intro j _
  exact Int.mul_comm _ _


/-- The checked list moments are the moments in the reference algorithm. -/
theorem checkMoments_eq {K b k : Nat} (B : Matrix Int k k) (r : Vector Int k)
    (ts : List Int) (vs : List (List Int)) (w : Vector Int k)
    (hb : boundedRows b (columns k (toRows B)) = true)
    (hw : 2 * (k * (b * b) + b) < 2 ^ K)
    (hc : checkMoments K b k r.toList (packs K (columns k (toRows B))) ts vs w.toList = true) :
    ts = berkowitzMoments B r ts.length w := by
  induction ts generalizing vs w with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil =>
      cases vs with
      | nil =>
        simp only [checkMoments, beq_iff_eq] at hc
        simp only [dot_toList] at hc
        change [t] = [-r.dotProduct w]
        exact congrArg (fun x => [x]) hc
      | cons v vs =>
        simp only [checkMoments, Bool.and_eq_true] at hc
        have he := checkLinear_mulVec B w v hb hw hc.1.2
        have ht : t = -(r.dotProduct w) := by
          have h := hc.1.1
          simp only [beq_iff_eq, dot_toList] at h
          exact h
        simp [ht, berkowitzMoments]
    | cons t' ts =>
      cases vs with
      | nil => simp [checkMoments] at hc
      | cons v vs =>
        simp only [checkMoments, Bool.and_eq_true] at hc
        have he := checkLinear_mulVec B w v hb hw hc.1.2
        have ht : t = -(r.dotProduct w) := by
          have h := hc.1.1
          simp only [beq_iff_eq, dot_toList] at h
          exact h
        have hm := ih vs (B * w) (he ▸ hc.2)
        simp only [List.length_cons, berkowitzMoments, ht]
        exact congrArg (List.cons _) hm


theorem trailing_entry {n : Nat} (A : Matrix Int n n) (k : Nat) (hk : k ≤ n)
    (i j : Nat) (hi : i < k) (hj : j < k) :
    (trailingBlock A k hk)[(i, j)]'(by omega) = A[(n - k + i, n - k + j)]'(by omega) := by
  have h := getElem_trailingBlock A k hk ⟨i, hi⟩ ⟨j, hj⟩
  simpa only [getElem_pair_nat, rows, Hex.Vector.getElem_ofFn', getElem_eq_getRow,
    Fin.getElem_fin] using h

/-- Trailing blocks compose, independently of the matrix representation. -/
theorem trailing_trailing {n : Nat} (A : Matrix Int n n) (k j : Nat)
    (hk : k ≤ n) (hj : j ≤ k) :
    trailingBlock (trailingBlock A k hk) j hj = trailingBlock A j (by omega) := by
  apply Matrix.ext_getElem
  intro i l
  rw [getElem_trailingBlock, trailing_entry, getElem_trailingBlock] <;> try omega
  simp only [show n - k + (k - j + i.val) = n - j + i.val by omega,
    show n - k + (k - j + l.val) = n - j + l.val by omega]

theorem row_trailing {n : Nat} (A : Matrix Int n n) (k j : Nat)
    (hk : k ≤ n) (hj : j + 1 ≤ k) :
    berkowitzRow (trailingBlock A k hk) j hj = berkowitzRow A j (by omega) := by
  apply Vector.ext
  intro i hi
  simp only [berkowitzRow, Hex.Vector.getElem_ofFn']
  rw [trailing_entry] <;> try omega
  simp only [show n - k + (k - j - 1) = n - j - 1 by omega,
    show n - k + (k - j + i) = n - j + i by omega]

theorem col_trailing {n : Nat} (A : Matrix Int n n) (k j : Nat)
    (hk : k ≤ n) (hj : j + 1 ≤ k) :
    berkowitzCol (trailingBlock A k hk) j hj = berkowitzCol A j (by omega) := by
  apply Vector.ext
  intro i hi
  simp only [berkowitzCol, Hex.Vector.getElem_ofFn']
  rw [trailing_entry] <;> try omega
  simp only [show n - k + (k - j - 1) = n - j - 1 by omega,
    show n - k + (k - j + i) = n - j + i by omega]

theorem column_trailing {n : Nat} (A : Matrix Int n n) (k j : Nat)
    (hk : k ≤ n) (hj : j + 1 ≤ k) :
    berkowitzColumn (trailingBlock A k hk) j hj = berkowitzColumn A j (by omega) := by
  have ha : (trailingBlock A k hk)[(k - j - 1, k - j - 1)]'(by omega) =
      A[(n - j - 1, n - j - 1)]'(by omega) := by
    rw [trailing_entry] <;> try omega
    simp only [show n - k + (k - j - 1) = n - j - 1 by omega]
  simp only [berkowitzColumn, row_trailing, col_trailing, trailing_trailing, ha]

theorem aux_trailing {n : Nat} (A : Matrix Int n n) (k j : Nat)
    (hk : k ≤ n) (hj : j ≤ k) :
    berkowitzAux (trailingBlock A k hk) j hj = berkowitzAux A j (by omega) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [berkowitzAux, berkowitzStep, column_trailing, ih]


theorem toRows_ofFn {n m : Nat} (A : Matrix Int n m) :
    toRows A = List.ofFn (fun i : Fin n => List.ofFn fun j : Fin m => A[i][j]) := by
  simp only [toRows, ← ofFn_vector, getElem_row]

theorem toRows_block {k : Nat} (A : Matrix Int (k + 1) (k + 1)) :
    tails (toRows A).tail = toRows (trailingBlock A k (by omega)) := by
  simp only [toRows_ofFn, List.ofFn_succ, List.tail_cons, tails_map,
    List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  rw [getElem_trailingBlock]
  simp [getElem_pair_nat, rows, getElem_eq_getRow, Fin.getElem_fin, Nat.add_comm]
  rfl

theorem toRows_border {k : Nat} (A : Matrix Int (k + 1) (k + 1)) :
    toRows A = (A[(0, 0)]'(by omega) :: (berkowitzRow A k (by omega)).toList) ::
      (toRows A).tail := by
  rw [toRows_ofFn]
  rw [List.ofFn_succ]
  simp only [List.tail_cons, List.cons.injEq, and_true]
  rw [List.ofFn_succ, ← ofFn_vector]
  congr 1
  · simp [getElem_pair_nat, rows, getElem_eq_getRow]
  · congr 1
    funext j
    simp [berkowitzRow, getElem_pair_nat, rows, getElem_eq_getRow,
      Fin.getElem_fin, Nat.add_comm]

theorem toRows_heads {k : Nat} (A : Matrix Int (k + 1) (k + 1)) :
    heads (toRows A).tail = (berkowitzCol A k (by omega)).toList := by
  simp only [toRows_ofFn, List.ofFn_succ, List.tail_cons, heads_map,
    List.map_ofFn, Function.comp_def, List.headD_cons, ← ofFn_vector]
  congr 1
  funext i
  simp [berkowitzCol, getElem_pair_nat, rows, getElem_eq_getRow,
    Fin.getElem_fin, Nat.add_comm]
  rfl

theorem column_list {n : Nat} (A : Matrix Int n n) (k : Nat) (hk : k + 1 ≤ n) :
    (berkowitzColumn A k hk).toList =
      1 :: -A[(n - k - 1, n - k - 1)]'(by omega) ::
        berkowitzMoments (trailingBlock A k (by omega)) (berkowitzRow A k hk) k
          (berkowitzCol A k hk) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    cases i with
    | zero => exact getElem_berkowitzColumn_zero A k hk
    | succ i => cases i with
      | zero => exact getElem_berkowitzColumn_one A k hk
      | succ i =>
        simp only [Vector.getElem_toList, List.getElem_cons_succ]
        exact getElem_berkowitzColumn_add_two A k hk ⟨i, by simp at hi; omega⟩


theorem getD_entry {α : Type} (xs : List α) (i : Nat) (d : α) (h : i < xs.length) :
    xs.getD i d = xs[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Full polynomial convolution, before the Toeplitz product is truncated. -/
@[expose] def convolution : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => addScaled x ys (0 :: convolution xs ys)

theorem pack_convolution (K : Nat) (xs ys : List Int) :
    pack K (convolution xs ys) = pack K xs * pack K ys := by
  induction xs with
  | nil => simp [convolution, pack_nil]
  | cons x xs ih =>
    rw [convolution, pack_addScaled, pack_cons, ih, pack_cons]
    simp only [Int.zero_add, Int.add_mul, Int.mul_assoc]

theorem length_convolution (xs ys : List Int) (hy : 0 < ys.length) :
    (convolution xs ys).length = if xs.isEmpty then 0 else xs.length + ys.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [convolution, length_addScaled]
    simp only [List.length_cons, ih]
    cases xs <;> simp_all <;> omega

theorem bound_convolution (xs ys : List Int) (b : Nat)
    (hx : ∀ x ∈ xs, x.natAbs ≤ b) (hy : ∀ y ∈ ys, y.natAbs ≤ b) :
    ∀ z ∈ convolution xs ys, z.natAbs ≤ xs.length * (b * b) := by
  induction xs with
  | nil => simp [convolution]
  | cons x xs ih =>
    intro z hz
    have ht := bound_addScaled x ys (0 :: convolution xs ys) b (xs.length * (b * b)) hy
      (by intro v hv; rcases List.mem_cons.mp hv with rfl | hv
          · simp
          · exact ih (fun v hv => hx v (by simp [hv])) v hv) z hz
    have hm := Nat.mul_le_mul_right b (hx x (by simp))
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem getD_convolution (n : Nat) (f : Fin n → Int) (ys : List Int) (i : Nat) :
    (convolution (List.ofFn f) ys).getD i 0 =
      (List.finRange n).foldl (fun acc j => acc + f j *
        (if j.val ≤ i then ys.getD (i - j.val) 0 else 0)) 0 := by
  induction n generalizing i with
  | zero => simp [convolution]
  | succ n ih =>
    rw [List.ofFn_succ, convolution, getD_addScaled, List.finRange_succ,
      List.foldl_cons, List.foldl_map]
    conv => rhs; rw [List.foldl_add_eq_add_foldl]
    cases i with
    | zero => simp [List.foldl_const_step]
    | succ i =>
      rw [List.getD_cons_succ, ih]
      simp only [Fin.val_zero, Nat.zero_le, ite_true, Nat.sub_zero, Int.zero_add,
        Fin.val_succ, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- A single packed product certifies the full convolution. -/
theorem convolution_eq_of_check {K b n : Nat} (xs ys result : List Int)
    (hy : 0 < ys.length) (hlen : result.length = if xs.isEmpty then 0 else xs.length + ys.length - 1)
    (hxlen : xs.length ≤ n) (hx : bounded b xs = true) (hyb : bounded b ys = true)
    (hr : bounded b result = true) (hw : 2 * (n * (b * b) + b) < 2 ^ K)
    (hc : (Int.mul (pack K xs) (pack K ys) == pack K result) = true) :
    convolution xs ys = result := by
  apply Hex.Internal.packDigits_inj K
  · rw [length_convolution xs ys hy, hlen]
  · intro z hz
    have h := bound_convolution xs ys b ((bounded_iff ..).mp hx) ((bounded_iff ..).mp hyb) z hz
    have hm := Nat.mul_le_mul_right (b * b) hxlen
    omega
  · intro z hz
    have h := (bounded_iff ..).mp hr z hz
    omega
  · rw [← pack_eq, ← pack_eq, pack_convolution]
    exact eq_of_beq hc

theorem convolution_take {k : Nat} (t : Vector Int (k + 2)) (v : Vector Int (k + 1)) :
    (convolution v.toList t.toList).take (k + 2) = (toeplitzMulVec t v).toList := by
  have hl : (convolution v.toList t.toList).length = 2 * k + 2 := by
    rw [length_convolution _ _ (by simp)]
    simp; omega
  apply List.ext_getElem
  · simp [hl]; omega
  · intro i hi hj
    have hi' : i < k + 2 := by simpa using hj
    have h := getD_convolution (k + 1) (fun j : Fin (k + 1) => v[j]) t.toList i
    rw [ofFn_vector] at h
    rw [getD_entry _ _ _ (by omega)] at h
    simp only [List.getElem_take, Vector.getElem_toList]
    rw [h]
    change _ = (toeplitzMulVec t v)[(⟨i, hi'⟩ : Fin (k + 2))]
    rw [getElem_toeplitzMulVec]
    apply List.foldl_congr
    intro acc j _
    split
    · rename_i hij
      rw [getD_entry _ _ _ (by simpa using (show i - j.val < k + 2 by omega))]
      simp [Int.mul_comm]
    · rename_i hij
      simp

/-- A passing list certificate identifies the descending Berkowitz vector. -/
theorem checkSteps_eq {K b n : Nat} (A : Matrix Int n n) (cs : List Step) (result : List Int)
    (hw : 2 * ((n + 1) * (b * b) + b) < 2 ^ K)
    (hc : checkSteps K b n (toRows A) cs result = true) :
    result = (berkowitz A).toList := by
  induction n generalizing cs result with
  | zero =>
    cases cs <;> simp [checkSteps, toRows, eqList_iff] at hc
    simpa [berkowitz, berkowitzAux] using hc
  | succ k ih =>
    rw [toRows_border A] at hc
    cases cs with
    | nil => simp [checkSteps] at hc
    | cons c cs =>
      simp only [checkSteps, toRows_block, toRows_heads, Bool.and_eq_true,
        Nat.beq_eq, eqList_iff] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hresult, hlen⟩, hprefix⟩, hb⟩, _⟩, hpacked⟩, hm⟩, hprod⟩, hr⟩ := hc
      rw [hpacked] at hm
      have hwk : 2 * ((k + 1) * (b * b) + b) < 2 ^ K := by
        have := Nat.mul_le_mul_right (b * b) (show k + 1 ≤ k + 1 + 1 by omega)
        omega
      have hwk' : 2 * (k * (b * b) + b) < 2 ^ K := by
        have := Nat.mul_le_mul_right (b * b) (show k ≤ k + 1 by omega)
        omega
      have hm := checkMoments_eq (trailingBlock A k (by omega))
        (berkowitzRow A k (by omega)) (c.column.drop 2) c.vectors
        (berkowitzCol A k (by omega)) hb hwk' hm
      have hdrop : (c.column.drop 2).length = k := by simp [hlen]
      rw [hdrop] at hm
      have ht : c.column = (berkowitzColumn A k (by omega)).toList := by
        rw [column_list]
        calc c.column = c.column.take 2 ++ c.column.drop 2 := (List.take_append_drop 2 _).symm
             _ = _ := by rw [hprefix, hm]; simp; rfl
      have hp := ih (trailingBlock A k (by omega)) _ _ hwk hr
      simp only [berkowitz, aux_trailing] at hp
      rw [hp, ht] at hprod
      simp only [checkProduct, Bool.and_eq_true, Nat.beq_eq, eqList_iff] at hprod
      have hf := convolution_eq_of_check (K := K) (b := b) (n := k + 1)
        (berkowitzAux A k (by omega)).toList (berkowitzColumn A k (by omega)).toList c.product
        (by simp) (by have h := hprod.1.1.1.1.1; simp; omega) (by simp)
        hprod.1.1.1.1.2 hprod.1.1.1.2 hprod.1.1.2 hwk hprod.2
      have hv := hprod.1.2
      rw [← hf, convolution_take] at hv
      rw [hresult, ← hv]
      rfl

/-- Soundness of the complete integer-list checker. -/
theorem berkowitz_eq_of_checkList {n : Nat} (A : Matrix Int n n)
    (w : Witness) (result : List Int)
    (h : checkCharPolyList n (toRows A) w result = true) :
    (berkowitz A).toList = result := by
  simp only [checkCharPolyList, Bool.and_eq_true, Nat.blt_eq] at h
  exact (checkSteps_eq A w.steps result h.1.2 h.2).symm


/-- Interpret a row list as a matrix, padding with zeros. This definition is
used only at the soundness boundary, never by the arithmetic checker. -/
@[expose] def ofLists (n : Nat) (rs : List (List Int)) : Matrix Int n n :=
  Matrix.ofFn fun i j => (rs.getD i []).getD j 0

theorem toRows_ofLists (n : Nat) (rs : List (List Int)) (hn : rs.length = n)
    (hm : ∀ r ∈ rs, r.length = n) : toRows (ofLists n rs) = rs := by
  rw [toRows_ofFn]
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_ofFn, ofLists, Matrix.getElem_ofFn]
    have hi' : i < rs.length := by simpa [hn] using hi
    rw [getD_entry _ _ _ hi']
    apply List.ext_getElem
    · simp [hm _ (List.getElem_mem hi')]
    · intro j hj hj'
      simp only [List.getElem_ofFn]
      exact getD_entry _ _ _ hj'

/-- Soundness with a literal row list, independently of matrix evaluation. -/
theorem charPoly_eq_of_checkList (n : Nat) (rs : List (List Int)) (w : Witness)
    (result : List Int) (h : checkCharPolyList n rs w result = true) :
    charPoly (ofLists n rs) = DensePoly.ofCoeffs result.reverse.toArray := by
  have hc := h
  simp only [checkCharPolyList, Bool.and_eq_true, Nat.beq_eq] at hc
  have he := toRows_ofLists n rs hc.1.1.1 ((rowLengths_iff ..).mp hc.1.1.2)
  rw [← he] at h
  have hb := berkowitz_eq_of_checkList (ofLists n rs) w result h
  unfold charPoly
  congr 1
  rw [← hb]
  rw [← List.reverse_toArray, Vector.toArray_toList, Vector.toArray_reverse]

/-- Compute the moment vectors with the existing matrix multiplication. -/
def momentVectors {k : Nat} (B : Matrix Int k k) : Nat → Vector Int k → List (List Int)
  | 0, _ => []
  | j + 1, w => let v := B * w; v.toList :: momentVectors B j v

/-- Produce the step data from the existing Berkowitz computation. -/
def produceSteps {n : Nat} (A : Matrix Int n n) : (k : Nat) → k ≤ n → List Step
  | 0, _ => []
  | k + 1, hk =>
    { column := (berkowitzColumn A k hk).toList
      vectors := momentVectors (trailingBlock A k (by omega)) (k - 1) (berkowitzCol A k hk)
      coefficients := (berkowitzAux A (k + 1) hk).toList } :: produceSteps A k (by omega)

/-- Supply the full convolutions, including coefficients beyond the Toeplitz output. -/
def addProducts : List Step → List Step
  | [] => []
  | c :: cs =>
    let prev := match cs with | [] => [1] | d :: _ => d.coefficients
    { c with product := convolution prev c.column } :: addProducts cs

/-- Cache the packed columns after selecting the common width. -/
def cacheSteps (K : Nat) : List (List Int) → List Step → List Step
  | _, [] => []
  | rs, c :: cs =>
    let block := tails rs.tail
    { c with packedColumns := packs K (columns block.length block) } :: cacheSteps K block cs

/-- Produce a width sufficient for all carried values and linear combinations. -/
def produce {n : Nat} (A : Matrix Int n n) : Witness :=
  let steps := addProducts (produceSteps A n (Nat.le_refl n))
  let b := steps.foldl (fun b s => max b (max (maxAbs s.column)
    (max (maxRows s.vectors) (max (maxAbs s.coefficients) (maxAbs s.product))))) (maxRows (toRows A))
  let K := ((n + 1) * (b * b) + b).log2 + 2
  { bound := b, width := K, steps := cacheSteps K (toRows A) steps }


end Hex.Matrix.CharPolyKernel
