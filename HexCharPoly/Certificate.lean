/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.CharPoly

public section

/-!
Kernel-checkable local certificates for the Samuelson--Berkowitz recursion on
closed integer matrices.

The `char_poly` frontend in `HexMatrixTactic` discovers every intermediate
vector with compiled code and emits a stepwise certificate; the soundness
theorems here identify a checked certificate with the executable
characteristic polynomial, so the kernel replays scalar, vector, and final
coefficient checks instead of the recursive coefficient computation.
-/

namespace Hex.Matrix

namespace Vector

/-- Kernel-reducible pointwise equality check for fixed-length vectors. -/
@[expose]
def beqEntries {n : Nat} (a b : _root_.Vector Int n) : Bool :=
  decide (a.toList = b.toList)

/-- Soundness of `beqEntries`. -/
theorem eq_of_beqEntries {n : Nat} {a b : _root_.Vector Int n}
    (h : beqEntries a b = true) : a = b := by
  exact _root_.Vector.toList_inj.mp (of_decide_eq_true h)

end Vector

/-- Read one literal-vector entry through a helper convenient for generated
certificate terms. -/
@[expose]
def vectorEntry {k : Nat} (v : _root_.Vector Int k) (i : Nat)
    (hi : i < k) : Int :=
  v[i]'hi

/-- Entry reduction for a selected matrix row. -/
theorem vectorEntry_row {k : Nat} (B : Matrix Int k k)
    (i j : Nat) (hi : i < k) (hj : j < k) :
    vectorEntry (row B ⟨i, hi⟩) j hj =
      B[((⟨i, hi⟩ : Fin k), (⟨j, hj⟩ : Fin k))] := by
  unfold vectorEntry
  change (row B ⟨i, hi⟩)[(⟨j, hj⟩ : Fin k)] = _
  rw [getElem_row, getElem_pair_eq_nested]

/-- Entry reduction for a row of a trailing principal block. -/
theorem vectorEntry_row_trailingBlock {n : Nat} (A : Matrix Int n n)
    (k : Nat) (hk : k ≤ n) (i j : Nat) (hi : i < k) (hj : j < k) :
    vectorEntry (row (trailingBlock A k hk) ⟨i, hi⟩) j hj =
      A[(n - k + i, n - k + j)]'(by omega) := by
  rw [vectorEntry_row, getElem_pair_eq_nested, getElem_trailingBlock]

/-- Entry reduction for the border row of a Berkowitz step. -/
theorem vectorEntry_berkowitzRow {n k : Nat} (A : Matrix Int n n)
    (hk : k + 1 ≤ n) (j : Nat) (hj : j < k) :
    vectorEntry (berkowitzRow A k hk) j hj =
      A[(n - k - 1, n - k + j)]'(by omega) := by
  simp [vectorEntry, berkowitzRow]

/-- Entry reduction for the border column of a Berkowitz step. -/
theorem vectorEntry_berkowitzCol {n k : Nat} (A : Matrix Int n n)
    (hk : k + 1 ≤ n) (i : Nat) (hi : i < k) :
    vectorEntry (berkowitzCol A k hk) i hi =
      A[(n - k + i, n - k - 1)]'(by omega) := by
  simp [vectorEntry, berkowitzCol]

/-- Addition selected from an explicit ring. -/
@[expose]
def addWith (ring : Lean.Grind.CommRing Int) (a b : Int) : Int :=
  @Add.add Int ring.toRing.toSemiring.toAdd a b

/-- Multiplication selected from an explicit ring. -/
@[expose]
def mulWith (ring : Lean.Grind.CommRing Int) (a b : Int) : Int :=
  @Mul.mul Int ring.toRing.toSemiring.toMul a b

/-- The explicit ring's value of `0`. -/
@[expose]
def zeroWith (ring : Lean.Grind.CommRing Int) : Int :=
  @OfNat.ofNat Int 0 (ring.toRing.toSemiring.ofNat 0)

/-- Dot product with operations selected from an explicit ring. -/
@[expose]
def dotProductWith (ring : Lean.Grind.CommRing Int) {k : Nat}
    (u v : _root_.Vector Int k) : Int :=
  @_root_.Vector.dotProduct Int k ring.toRing.toSemiring.toMul
    ring.toRing.toSemiring.toAdd (ring.toRing.toSemiring.ofNat 0) u v

/-- A scalar-by-scalar certificate for a dot-product fold. -/
inductive DotProductCertificate (ring : Lean.Grind.CommRing Int) {k : Nat}
    (u v : _root_.Vector Int k) : List (Fin k) → Int → Int → Prop where
  | nil (acc : Int) : DotProductCertificate ring u v [] acc acc
  | cons {i : Fin k} {is : List (Fin k)} {acc left right next result : Int}
      (left_check : vectorEntry u i.val i.isLt = left)
      (right_check : vectorEntry v i.val i.isLt = right)
      (step_check : addWith ring acc (mulWith ring left right) = next)
      (tail_certificate : DotProductCertificate ring u v is next result) :
      DotProductCertificate ring u v (i :: is) acc result

/-- Soundness of a scalar-by-scalar dot-product certificate. -/
theorem DotProductCertificate.eq_fold
    {ring : Lean.Grind.CommRing Int} {k : Nat}
    {u v : _root_.Vector Int k} {is : List (Fin k)} {acc result : Int}
    (certificate : DotProductCertificate ring u v is acc result) :
    is.foldl (fun total i =>
      addWith ring total (mulWith ring u[i] v[i])) acc = result := by
  induction certificate with
  | nil => rfl
  | cons left_check right_check step_check _ ih =>
      simp only [List.foldl_cons]
      change List.foldl _
        (addWith ring _ (mulWith ring (vectorEntry u _ _) (vectorEntry v _ _))) _ = _
      rw [left_check, right_check, step_check]
      exact ih

/-- A complete scalar certificate identifies a dot product. -/
theorem DotProductCertificate.eq_dotProduct
    {ring : Lean.Grind.CommRing Int} {k : Nat}
    {u v : _root_.Vector Int k} {result : Int}
    (certificate : DotProductCertificate ring u v (List.finRange k)
      (zeroWith ring) result) : dotProductWith ring u v = result := by
  exact certificate.eq_fold

/-- One matrix-vector product entry with operations selected from an explicit
grind commutative-ring structure. -/
@[expose]
def mulVecEntryWith (ring : Lean.Grind.CommRing Int) {k : Nat}
    (B : Matrix Int k k) (w : _root_.Vector Int k) (i : Fin k) : Int :=
  dotProductWith ring (row B i) w

/-- Matrix-vector multiplication with operations selected from an explicit
grind commutative-ring structure. -/
@[expose]
def mulVecWith (ring : Lean.Grind.CommRing Int) {k : Nat}
    (B : Matrix Int k k) (w : _root_.Vector Int k) : _root_.Vector Int k :=
  Hex.Vector.ofFn' fun i => mulVecEntryWith ring B w i

/-- The kernel-reducible multiplication helper agrees with the public matrix
operation. -/
theorem mulVecWith_eq (ring : Lean.Grind.CommRing Int) {k : Nat}
    (B : Matrix Int k k) (w : _root_.Vector Int k) :
    mulVecWith ring B w =
      @Matrix.mulVec Int k k ring.toRing.toSemiring.toMul
        ring.toRing.toSemiring.toAdd (ring.toRing.toSemiring.ofNat 0) B w := by
  apply _root_.Vector.ext
  intro i hi
  unfold mulVecWith Matrix.mulVec mulVecEntryWith dotProductWith
  simp only [Hex.Vector.getElem_ofFn']

/-- A pointwise certificate for one matrix-vector multiplication. -/
inductive MulVecCertificate (ring : Lean.Grind.CommRing Int) {k : Nat}
    (B : Matrix Int k k) (w next : _root_.Vector Int k) : Nat → Prop where
  | zero : MulVecCertificate ring B w next 0
  | step {i : Nat} (hi : i < k) {value : Int}
      (certificate : MulVecCertificate ring B w next i)
      (dot_certificate : DotProductCertificate ring (row B ⟨i, hi⟩) w
        (List.finRange k) (zeroWith ring) value)
      (entry_check : vectorEntry next i hi = value) :
      MulVecCertificate ring B w next (i + 1)

/-- Recover an individual entry from a pointwise multiplication certificate. -/
theorem MulVecCertificate.entry
    {ring : Lean.Grind.CommRing Int} {k count : Nat}
    {B : Matrix Int k k} {w next : _root_.Vector Int k}
    (certificate : MulVecCertificate ring B w next count)
    (i : Fin k) (hi : i.val < count) :
    mulVecEntryWith ring B w i = vectorEntry next i.val i.isLt := by
  induction certificate generalizing i with
  | zero => omega
  | @step j hj value certificate dot_certificate entry_check ih =>
      by_cases h : i.val = j
      · have : i = ⟨j, hj⟩ := Fin.ext h
        subst i
        rw [mulVecEntryWith, dot_certificate.eq_dotProduct, entry_check]
      · exact ih i (by omega)

/-- A complete pointwise certificate identifies the matrix-vector product. -/
theorem MulVecCertificate.eq_mulVec
    {ring : Lean.Grind.CommRing Int} {k : Nat}
    {B : Matrix Int k k} {w next : _root_.Vector Int k}
    (certificate : MulVecCertificate ring B w next k) :
    mulVecWith ring B w = next := by
  apply _root_.Vector.ext
  intro i hi
  unfold mulVecWith
  rw [Hex.Vector.getElem_ofFn']
  exact certificate.entry ⟨i, hi⟩ hi

/-- One Berkowitz moment with operations selected from an explicit ring. -/
@[expose]
def momentWith (ring : Lean.Grind.CommRing Int) {k : Nat}
    (row w : _root_.Vector Int k) : Int :=
  @Neg.neg Int ring.toRing.toNeg (dotProductWith ring row w)

/-- The explicit ring's value of `1`. -/
@[expose]
def oneWith (ring : Lean.Grind.CommRing Int) : Int :=
  @OfNat.ofNat Int 1 (ring.toRing.toSemiring.ofNat 1)

/-- Negation selected from an explicit ring. -/
@[expose]
def negWith (ring : Lean.Grind.CommRing Int) (a : Int) : Int :=
  @Neg.neg Int ring.toRing.toNeg a

/-- A fine-grained certificate for the moment loop.  Each matrix-vector
product is checked separately, avoiding expansion of the recursive loop. -/
inductive MomentsCertificate (ring : Lean.Grind.CommRing Int) {k : Nat}
    (B : Matrix Int k k) (row : _root_.Vector Int k) :
    (count : Nat) → _root_.Vector Int k → List Int → Prop where
  | zero (w : _root_.Vector Int k) : MomentsCertificate ring B row 0 w []
  | one (w : _root_.Vector Int k) (value dot : Int)
      (dot_certificate : DotProductCertificate ring row w (List.finRange k)
        (zeroWith ring) dot)
      (head : negWith ring dot = value) :
      MomentsCertificate ring B row 1 w [value]
  | step {j : Nat} {w next : _root_.Vector Int k} {value : Int}
      {dot : Int} {tail : List Int}
      (dot_certificate : DotProductCertificate ring row w (List.finRange k)
        (zeroWith ring) dot)
      (head : negWith ring dot = value)
      (mul_certificate : MulVecCertificate ring B w next k)
      (tail_certificate : MomentsCertificate ring B row (j + 1) next tail) :
      MomentsCertificate ring B row (j + 2) w (value :: tail)

/-- Soundness of a fine-grained moment certificate. -/
theorem MomentsCertificate.eq_berkowitzMoments
    {ring : Lean.Grind.CommRing Int} {k count : Nat}
    {B : Matrix Int k k} {row w : _root_.Vector Int k} {values : List Int}
    (certificate : MomentsCertificate ring B row count w values) :
    @berkowitzMoments Int ring k B row count w = values := by
  cases certificate with
  | zero => rfl
  | one w value dot dot_certificate head =>
      rw [berkowitzMoments]
      change [momentWith ring row w] = [value]
      unfold momentWith
      rw [dot_certificate.eq_dotProduct]
      change [negWith ring dot] = [value]
      rw [head]
  | @step j w next value dot tail dot_certificate head mul_certificate
      tail_certificate =>
      rw [berkowitzMoments]
      change @Neg.neg Int ring.toRing.toNeg
          (@_root_.Vector.dotProduct Int k ring.toRing.toSemiring.toMul
            ring.toRing.toSemiring.toAdd (ring.toRing.toSemiring.ofNat 0)
            row w) ::
          @berkowitzMoments Int ring k B row (j + 1)
            (@Matrix.mulVec Int k k ring.toRing.toSemiring.toMul
              ring.toRing.toSemiring.toAdd
              (ring.toRing.toSemiring.ofNat 0) B w) =
        value :: tail
      rw [← mulVecWith_eq ring B w]
      change momentWith ring row w ::
          @berkowitzMoments Int ring k B row (j + 1) (mulVecWith ring B w) =
        value :: tail
      unfold momentWith
      rw [dot_certificate.eq_dotProduct]
      change negWith ring dot ::
          @berkowitzMoments Int ring k B row (j + 1) (mulVecWith ring B w) =
        value :: tail
      rw [head, mul_certificate.eq_mulVec,
        tail_certificate.eq_berkowitzMoments]

/-- A moment certificate contains exactly `count` values. -/
theorem MomentsCertificate.length_eq
    {ring : Lean.Grind.CommRing Int} {k count : Nat}
    {B : Matrix Int k k} {row w : _root_.Vector Int k} {values : List Int}
    (certificate : MomentsCertificate ring B row count w values) :
    values.length = count := by
  induction certificate with
  | zero => rfl
  | one => rfl
  | step _ _ _ _ ih => simp [ih]

/-- Rebuild a Berkowitz column from a certified literal moment list. -/
@[expose]
def columnOfMoments (ring : Lean.Grind.CommRing Int) {n : Nat}
    (A : Matrix Int n n) (k : Nat) (hk : k + 1 ≤ n)
    (moments : List Int) : _root_.Vector Int (k + 2) :=
  let s := n - k - 1
  let a := A[((s : Nat), (s : Nat))]'(by simp only [s]; omega)
  let values := moments.toArray
  Hex.Vector.ofFn' fun i =>
    if h0 : i.val = 0 then
      oneWith ring
    else if h1 : i.val = 1 then
      negWith ring a
    else
      values.getD (i.val - 2) 0

/-- A certified moment list reconstructs the actual Berkowitz column. -/
theorem berkowitzColumn_eq_of_moments
    {ring : Lean.Grind.CommRing Int} {n k : Nat} {A : Matrix Int n n}
    {moments : List Int} (hk : k + 1 ≤ n)
    (certificate : MomentsCertificate ring (trailingBlock A k (by omega))
      (@berkowitzRow Int n A k hk) k
      (@berkowitzCol Int n A k hk) moments) :
    @berkowitzColumn Int ring n A k hk = columnOfMoments ring A k hk moments := by
  unfold berkowitzColumn columnOfMoments
  simp only [certificate.eq_berkowitzMoments]
  apply _root_.Vector.ext
  intro i hi
  rw [Hex.Vector.getElem_ofFn', Hex.Vector.getElem_ofFn']
  by_cases h0 : i = 0
  · subst i
    simp [oneWith]
  · by_cases h1 : i = 1
    · simp [h1, negWith]
    · simp only [h0, h1, dite_false]
      have hlt : i - 2 < moments.toArray.size := by
        rw [List.size_toArray, certificate.length_eq]
        omega
      exact Array.getElem_eq_getD (h := hlt) (0 : Int)

/-- A stepwise Berkowitz certificate.  Supplying every intermediate vector
prevents kernel replay from expanding the recursive coefficient computation
repeatedly. -/
inductive BerkowitzCertificate {n : Nat} [ring : Lean.Grind.CommRing Int]
    (A : Matrix Int n n) : (k : Nat) → _root_.Vector Int (k + 1) → Prop where
  | zero : BerkowitzCertificate A 0
      #v[@OfNat.ofNat Int 1 (ring.toRing.toSemiring.ofNat 1)]
  | step {k : Nat} (hk : k + 1 ≤ n)
      {previous : _root_.Vector Int (k + 1)}
      {next : _root_.Vector Int (k + 2)}
      {moments : List Int} {column : _root_.Vector Int (k + 2)}
      (certificate : BerkowitzCertificate A k previous)
      (moments_certificate : MomentsCertificate ring
        (trailingBlock A k (by omega)) (@berkowitzRow Int n A k hk) k
        (@berkowitzCol Int n A k hk) moments)
      (column_check : Vector.beqEntries
        (columnOfMoments ring A k hk moments) column = true)
      (step_check : Vector.beqEntries (toeplitzMulVec column previous) next = true) :
      BerkowitzCertificate A (k + 1) next

/-- A valid stepwise certificate identifies its final vector with the
recursive Berkowitz result. -/
theorem BerkowitzCertificate.eq_berkowitzAux
    {ring : Lean.Grind.CommRing Int} {n k : Nat} {A : Matrix Int n n}
    {v : _root_.Vector Int (k + 1)}
    (certificate : @BerkowitzCertificate n ring A k v) :
    ∀ hk : k ≤ n, @berkowitzAux Int ring n A k hk = v := by
  cases certificate with
  | zero =>
      intro _
      rw [berkowitzAux]
  | @step k hk' previous next moments column certificate moments_certificate
      column_check step_check =>
      intro _
      rw [berkowitzAux, berkowitzStep,
        berkowitzColumn_eq_of_moments hk' moments_certificate,
        Vector.eq_of_beqEntries column_check,
        certificate.eq_berkowitzAux (by omega)]
      exact Vector.eq_of_beqEntries step_check

/-- Kernel-checkable equality endpoint used by the `char_poly` frontend: a
checked stepwise certificate whose final coefficients match `p` proves the
characteristic-polynomial equality. -/
theorem charPoly_eq_of_check {n : Nat} (A : Matrix Int n n)
    (descending : _root_.Vector Int (n + 1)) (p : DensePoly Int)
    (certificate : @BerkowitzCertificate n Lean.Grind.instCommRingInt A n descending)
    (h : DensePoly.beqCoeffs
      (DensePoly.ofCoeffs descending.reverse.toArray) p = true) : charPoly A = p :=
  by
    rw [charPoly, berkowitz, certificate.eq_berkowitzAux (Nat.le_refl n)]
    exact DensePoly.eq_of_beqCoeffs h

end Hex.Matrix
