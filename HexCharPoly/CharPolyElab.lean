/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexCharPoly.CharPoly
public import HexCharPoly.CharPoly
public import Lean

public section

/-!
The `char_poly` result elaborator and tactics for closed integer matrices.

Compiled evaluation is used only to discover coefficients and intermediate
values.  Every emitted result carries scalar, vector, and final coefficient
checks that the kernel replays.
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
  rw [Hex.Vector.getElem_ofFn', _root_.Vector.getElem_ofFn]

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

/-- A characteristic polynomial computed and certified by `char_poly`. -/
structure CharPolyResult {n : Nat} (A : Matrix Int n n) where
  /-- The computed characteristic polynomial, in ascending coefficient order. -/
  poly : DensePoly Int
  /-- The computed polynomial is the characteristic polynomial of the input. -/
  charPoly_eq : charPoly A = poly

/-- Kernel-checkable endpoint used by the `char_poly` elaborator. -/
@[expose]
def CharPolyResult.ofCheck {n : Nat} (A : Matrix Int n n)
    (descending : _root_.Vector Int (n + 1)) (p : DensePoly Int)
    (certificate : @BerkowitzCertificate n Lean.Grind.instCommRingInt A n descending)
    (h : DensePoly.beqCoeffs
      (DensePoly.ofCoeffs descending.reverse.toArray) p = true) : CharPolyResult A where
  poly := p
  charPoly_eq := by
    rw [charPoly, berkowitz, certificate.eq_berkowitzAux (Nat.le_refl n)]
    exact DensePoly.eq_of_beqCoeffs h

/-- Kernel-checkable equality endpoint used by goal-closing `char_poly`. -/
theorem charPoly_eq_of_check {n : Nat} (A : Matrix Int n n)
    (descending : _root_.Vector Int (n + 1)) (p : DensePoly Int)
    (certificate : @BerkowitzCertificate n Lean.Grind.instCommRingInt A n descending)
    (h : DensePoly.beqCoeffs
      (DensePoly.ofCoeffs descending.reverse.toArray) p = true) : charPoly A = p :=
  by
    rw [charPoly, berkowitz, certificate.eq_berkowitzAux (Nat.le_refl n)]
    exact DensePoly.eq_of_beqCoeffs h

end Hex.Matrix

namespace Hex.CharPolyTactic

open Lean Meta Elab

/-- Build a kernel `decide` proof of a proposition.  This is used instead of
raw reflexivity because some current-toolchain reductions available to the
kernel evaluator are not available to ordinary `rfl` unification across
module boundaries. -/
public meta def kernelDecideProof (prop : Expr) : MetaM Expr := do
  try
    mkDecideProof prop
  catch _ =>
    throwError "char_poly: the kernel could not replay the generated Boolean check; Lean's ordinary reduction limits may have been reached"

/-- Prove `DensePoly.beqCoeffs a b = true` by kernel evaluation. -/
public meta def beqCoeffsProof (a b : Expr) : MetaM Expr := do
  let check ← mkAppM ``DensePoly.beqCoeffs #[a, b]
  let prop ← mkEq check (mkConst ``Bool.true)
  kernelDecideProof prop

/-- Literal `Array` expression backed by a literal list. -/
public meta def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  let list := xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty list

/-- Literal list expression. -/
public meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil

/-- Reify a fixed-length integer vector. -/
public meta def reifyIntVector {n : Nat} (v : _root_.Vector Int n) : MetaM Expr := do
  let data := arrayLit (mkConst ``Int) (v.toArray.toList.map toExpr)
  let size := mkNatLit n
  let sizeProof ← mkAppM ``Eq.refl #[size]
  mkAppM ``_root_.Vector.mk #[data, sizeProof]

/-- Reify an integer dense polynomial as `DensePoly.ofCoeffs #[...]`. -/
public meta def reifyZPoly (p : DensePoly Int) : MetaM Expr :=
  mkAppM ``DensePoly.ofCoeffs
    #[arrayLit (mkConst ``Int) (p.toArray.toList.map toExpr)]

/-- Reify the flat data of an integer matrix for kernel certificate replay. -/
public meta def reifyIntMatrix {n m : Nat} (A : Matrix Int n m) : MetaM Expr := do
  let vector ← reifyIntVector A.data
  return mkApp4 (mkConst ``Matrix.mk [Level.zero])
    (mkConst ``Int) (mkNatLit n) (mkNatLit m) vector

private meta unsafe def evalMatrixUnsafe (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix Int n n)) := do
  try
    return .ok (← evalExpr (Matrix Int n n) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalMatrixUnsafe]
private meta opaque evalMatrixCore (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix Int n n))

private meta unsafe def evalPolyUnsafe (ty e : Expr) :
    MetaM (Except String (DensePoly Int)) := do
  try
    return .ok (← evalExpr (DensePoly Int) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalPolyUnsafe]
private meta opaque evalPolyCore (ty e : Expr) :
    MetaM (Except String (DensePoly Int))

/-- A closed, evaluated core matrix with its dependent dimension. -/
public meta structure CoreInput where
  n : Nat
  expr : Expr
  value : Matrix Int n n

/-- Reject free variables and unresolved metavariables before compiled
evaluation. -/
public meta def checkClosed (what : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasExprMVar then
    throwError "char_poly: the {what}{indentExpr e}\nmust be a closed term (no local hypotheses or metavariables)"

/-- Classify and evaluate an already elaborated `Hex.Matrix Int n n`.  A
non-Hex type returns `none`, allowing another elaborator for the same syntax
kind to try it. -/
public meta def coreInput? (e : Expr) : MetaM (Option CoreInput) := do
  let e ← instantiateMVars e
  let ty ← whnfR (← inferType e)
  let_expr Matrix R rows cols := ty | return none
  unless (← whnfR R).isConstOf ``Int do
    throwError "char_poly: unsupported coefficient type{indentExpr R}\nOnly Int matrices are currently supported"
  let some n ← getNatValue? rows |
    throwError "char_poly: the row dimension must reduce to a concrete natural number{indentExpr rows}"
  let some m ← getNatValue? cols |
    throwError "char_poly: the column dimension must reduce to a concrete natural number{indentExpr cols}"
  unless n == m do
    throwError "char_poly: expected a square matrix, but got dimensions {n} × {m}"
  checkClosed "matrix" e
  match ← evalMatrixCore n ty e with
  | .error msg =>
      throwError "char_poly: failed to evaluate the matrix with compiled code{indentExpr e}\n{msg}"
  | .ok value => return some ⟨n, e, value⟩

/-- Require a compiled matrix value to be definitionally visible to the
kernel through its original expression. -/
public meta def checkMatrixTransparent (input : CoreInput) : MetaM Unit := do
  let literal ← reifyIntMatrix input.value
  unless ← withTransparency .all <| isDefEq literal input.expr do
    throwError "char_poly: the matrix{indentExpr input.expr}\nevaluates to{indentExpr literal}\nbut is not definitionally transparent to the elaborator (an imported definition without `@[expose]`?); the kernel could not replay the characteristic-polynomial check"

/-- Compute and reify the characteristic polynomial after checking the input
transparency contract. -/
public meta def computedPoly (input : CoreInput) : MetaM (DensePoly Int × Expr) := do
  checkMatrixTransparent input
  let p := Matrix.charPoly input.value
  return (p, ← reifyZPoly p)

/-- Reified data and proof for one depth of a stepwise certificate. -/
public meta structure CertificateExpr (k : Nat) where
  value : _root_.Vector Int (k + 1)
  literal : Expr
  proof : Expr

private meta structure MomentsExpr (count : Nat) where
  values : List Int
  literal : Expr
  proof : Expr

private meta abbrev EntryProof (k : Nat) :=
  (i : Fin k) → (hiExpr : Expr) → MetaM Expr

private meta abbrev MatrixEntryProof (k : Nat) :=
  (i : Fin k) → (hiExpr : Expr) → EntryProof k

private meta def directEntryProof {k : Nat} (v : _root_.Vector Int k)
    (vExpr : Expr) : EntryProof k := fun i hiExpr => do
  let source := mkAppN (mkConst ``Matrix.vectorEntry)
    #[mkNatLit k, vExpr, mkNatLit i.val, hiExpr]
  kernelDecideProof (← mkEq source (toExpr v[i]))

private meta def finishEntryProof (lemma : Expr) (value : Int) : MetaM Expr := do
  let some (_, _, rhs) := (← inferType lemma).eq? |
    throwError "char_poly: internal entry-reduction lemma is not an equality"
  let checked ← kernelDecideProof (← mkEq rhs (toExpr value))
  mkAppM ``Eq.trans #[lemma, checked]

private meta structure DotExpr (k : Nat) where
  value : Int
  indices : Expr
  proof : Expr

private meta def buildDotFold {k : Nat} (ring : Expr)
    (u : _root_.Vector Int k) (uExpr : Expr)
    (v : _root_.Vector Int k) (vExpr : Expr)
    (uEntry vEntry : EntryProof k) :
    (indices : List (Fin k)) → (acc : Int) → Expr → MetaM (DotExpr k)
  | [], acc, accExpr => do
      let finType := mkApp (mkConst ``Fin) (mkNatLit k)
      let indicesExpr := listLit finType []
      let proof := mkAppN (mkConst ``Matrix.DotProductCertificate.nil)
        #[ring, mkNatLit k, uExpr, vExpr, accExpr]
      return ⟨acc, indicesExpr, proof⟩
  | i :: indices, acc, accExpr => do
      let hiProof ← kernelDecideProof
        (← mkAppM ``LT.lt #[mkNatLit i.val, mkNatLit k])
      let fin := mkApp3 (mkConst ``Fin.mk)
        (mkNatLit k) (mkNatLit i.val) hiProof
      let left := u[i]
      let right := v[i]
      let leftExpr := toExpr left
      let rightExpr := toExpr right
      let leftProof ← uEntry i hiProof
      let rightProof ← vEntry i hiProof
      let next := acc + left * right
      let nextExpr := toExpr next
      let product := mkApp3 (mkConst ``Matrix.mulWith)
        ring leftExpr rightExpr
      let sum := mkApp3 (mkConst ``Matrix.addWith) ring accExpr product
      let stepProof ← kernelDecideProof (← mkEq sum nextExpr)
      let tail ← buildDotFold ring u uExpr v vExpr uEntry vEntry
        indices next nextExpr
      let finType := mkApp (mkConst ``Fin) (mkNatLit k)
      let indicesExpr := mkApp3 (mkConst ``List.cons [Level.zero])
        finType fin tail.indices
      let proof := mkAppN (mkConst ``Matrix.DotProductCertificate.cons)
        #[ring, mkNatLit k, uExpr, vExpr, fin, tail.indices, accExpr,
          leftExpr, rightExpr, nextExpr, toExpr tail.value, leftProof,
          rightProof, stepProof, tail.proof]
      return ⟨tail.value, indicesExpr, proof⟩

private meta def buildDotCertificate {k : Nat} (ring : Expr)
    (u : _root_.Vector Int k) (uExpr : Expr)
    (v : _root_.Vector Int k) (vExpr : Expr)
    (uEntry vEntry : EntryProof k) : MetaM (DotExpr k) := do
  let zeroExpr := mkApp (mkConst ``Matrix.zeroWith) ring
  buildDotFold ring u uExpr v vExpr uEntry vEntry
    (List.finRange k) 0 zeroExpr

private meta def buildMulVecCertificate {k : Nat} (ring : Expr)
    (B : Matrix Int k k) (matrixExpr : Expr)
    (matrixEntry : MatrixEntryProof k)
    (w : _root_.Vector Int k) (wExpr nextExpr : Expr)
    (wEntry : EntryProof k) : MetaM Expr := do
  let mut proof := mkAppN (mkConst ``Matrix.MulVecCertificate.zero)
    #[ring, mkNatLit k, matrixExpr, wExpr, nextExpr]
  for i in [0:k] do
    if hi : i < k then
      let hiProp ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit k]
      let hiProof ← kernelDecideProof hiProp
      let fin := mkApp3 (mkConst ``Fin.mk)
        (mkNatLit k) (mkNatLit i) hiProof
      let row := Matrix.row B ⟨i, hi⟩
      let rowExpr := mkAppN (mkConst ``Matrix.row [Level.zero])
        #[mkConst ``Int, mkNatLit k, mkNatLit k, matrixExpr, fin]
      let dot ← buildDotCertificate ring row rowExpr w wExpr
        (matrixEntry ⟨i, hi⟩ hiProof) wEntry
      let target := mkAppN (mkConst ``Matrix.vectorEntry)
        #[mkNatLit k, nextExpr, mkNatLit i, hiProof]
      let entryProof ← kernelDecideProof (← mkEq target (toExpr dot.value))
      proof := mkAppN (mkConst ``Matrix.MulVecCertificate.step)
        #[ring, mkNatLit k, matrixExpr, wExpr, nextExpr, mkNatLit i,
          hiProof, toExpr dot.value, proof, dot.proof, entryProof]
    else
      throwError "char_poly: internal matrix-vector certificate index escaped its dimension"
  return proof

private meta def buildMoments {k : Nat} (ring : Expr)
    (B : Matrix Int k k) (matrixExpr : Expr)
    (matrixEntry : MatrixEntryProof k)
    (row : _root_.Vector Int k) (rowExpr : Expr) (rowEntry : EntryProof k) :
    (count : Nat) → (w : _root_.Vector Int k) → Expr → EntryProof k →
      MetaM (MomentsExpr count)
  | 0, _w, wExpr, _wEntry => do
      let literal := listLit (mkConst ``Int) []
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.zero)
        #[ring, mkNatLit k, matrixExpr, rowExpr, wExpr]
      return ⟨[], literal, proof⟩
  | 1, w, wExpr, wEntry => do
      let dot ← buildDotCertificate ring row rowExpr w wExpr rowEntry wEntry
      let value := -dot.value
      let valueExpr := toExpr value
      let negated := mkApp2 (mkConst ``Matrix.negWith) ring (toExpr dot.value)
      let headProof ← kernelDecideProof (← mkEq negated valueExpr)
      let literal := listLit (mkConst ``Int) [valueExpr]
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.one)
        #[ring, mkNatLit k, matrixExpr, rowExpr, wExpr, valueExpr,
          toExpr dot.value, dot.proof, headProof]
      return ⟨[value], literal, proof⟩
  | j + 2, w, wExpr, wEntry => do
      let dot ← buildDotCertificate ring row rowExpr w wExpr rowEntry wEntry
      let value := -dot.value
      let valueExpr := toExpr value
      let negated := mkApp2 (mkConst ``Matrix.negWith) ring (toExpr dot.value)
      let headProof ← kernelDecideProof (← mkEq negated valueExpr)
      let next := B * w
      let nextExpr ← reifyIntVector next
      let mulCertificate ← buildMulVecCertificate ring B matrixExpr matrixEntry
        w wExpr nextExpr wEntry
      let nextEntry := directEntryProof next nextExpr
      let tail ← buildMoments ring B matrixExpr matrixEntry row rowExpr rowEntry
        (j + 1) next nextExpr nextEntry
      let literal := mkApp3 (mkConst ``List.cons [Level.zero])
        (mkConst ``Int) valueExpr tail.literal
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.step)
        #[ring, mkNatLit k, matrixExpr, rowExpr, mkNatLit j, wExpr,
          nextExpr, valueExpr, toExpr dot.value, tail.literal, dot.proof,
          headProof, mulCertificate, tail.proof]
      return ⟨value :: tail.values, literal, proof⟩

private meta def buildCertificate (input : CoreInput) (ring : Expr) :
    (k : Nat) → k ≤ input.n → MetaM (CertificateExpr k)
  | 0, _ => do
      let proof := mkApp3 (mkConst ``Matrix.BerkowitzCertificate.zero)
        (mkNatLit input.n) ring input.expr
      let type ← inferType proof
      let literal := type.getAppArgs.back!
      return ⟨#v[1], literal, proof⟩
  | k + 1, hk => do
      let previous ← buildCertificate input ring k (by omega)
      let leProp ← mkAppM ``LE.le #[mkNatLit (k + 1), mkNatLit input.n]
      let leProof ← kernelDecideProof leProp
      let block := Matrix.trailingBlock input.value k (by omega)
      let row := @Matrix.berkowitzRow Int input.n input.value k hk
      let col := @Matrix.berkowitzCol Int input.n input.value k hk
      let blockLeProof ← kernelDecideProof
        (← mkAppM ``LE.le #[mkNatLit k, mkNatLit input.n])
      let blockExpr := mkAppN (mkConst ``Matrix.trailingBlock [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k,
          blockLeProof]
      let rowExpr := mkAppN (mkConst ``Matrix.berkowitzRow [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k, leProof]
      let colExpr := mkAppN (mkConst ``Matrix.berkowitzCol [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k, leProof]
      let matrixEntry : MatrixEntryProof k := fun i hiExpr j hjExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_row_trailingBlock
          #[input.expr, mkNatLit k, blockLeProof, mkNatLit i.val,
            mkNatLit j.val, hiExpr, hjExpr]
        finishEntryProof lemma block[(i, j)]
      let rowEntry : EntryProof k := fun j hjExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_berkowitzRow
          #[input.expr, leProof, mkNatLit j.val, hjExpr]
        finishEntryProof lemma row[j]
      let colEntry : EntryProof k := fun i hiExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_berkowitzCol
          #[input.expr, leProof, mkNatLit i.val, hiExpr]
        finishEntryProof lemma col[i]
      let moments ← buildMoments ring block blockExpr matrixEntry row rowExpr
        rowEntry k col colExpr colEntry
      let column := @Matrix.berkowitzColumn Int Lean.Grind.instCommRingInt
        input.n input.value k hk
      let columnLiteral ← reifyIntVector column
      let columnSource := mkAppN (mkConst ``Matrix.columnOfMoments)
        #[ring, mkNatLit input.n, input.expr, mkNatLit k, leProof, moments.literal]
      let columnCheck ← mkAppM ``Matrix.Vector.beqEntries
        #[columnSource, columnLiteral]
      let columnProp ← mkEq columnCheck (mkConst ``Bool.true)
      let columnProof ← kernelDecideProof columnProp
      let next := Matrix.toeplitzMulVec column previous.value
      let nextLiteral ← reifyIntVector next
      let step := mkAppN (mkConst ``Matrix.toeplitzMulVec [Level.zero])
        #[mkConst ``Int, ring, mkNatLit k, columnLiteral, previous.literal]
      let stepCheck ← mkAppM ``Matrix.Vector.beqEntries #[step, nextLiteral]
      let stepProp ← mkEq stepCheck (mkConst ``Bool.true)
      let stepProof ← kernelDecideProof stepProp
      let proof := mkAppN (mkConst ``Matrix.BerkowitzCertificate.step)
        #[mkNatLit input.n, ring, input.expr, mkNatLit k, leProof,
          previous.literal, nextLiteral, moments.literal, columnLiteral,
          previous.proof, moments.proof, columnProof, stepProof]
      return ⟨next, nextLiteral, proof⟩

/-- Build the complete stepwise certificate for an input matrix using the
supplied commutative-ring instance expression. -/
public meta def certificateExpr (input : CoreInput) (ring : Expr) :
    MetaM (CertificateExpr input.n) :=
  buildCertificate input ring input.n (Nat.le_refl input.n)

/-- `DensePoly.ofCoeffs descending.reverse.toArray` as an expression. -/
public meta def polyOfDescending (descending : Expr) : MetaM Expr := do
  let reverse ← mkAppM ``_root_.Vector.reverse #[descending]
  let coefficients ← mkAppM ``_root_.Vector.toArray #[reverse]
  mkAppM ``DensePoly.ofCoeffs #[coefficients]

/-- Elaborate a matrix argument.  A raw `#m[...]` literal is given an integer
coefficient expectation so its numerals do not default to `Nat`. -/
public meta def elabCoreArgument? (t : Syntax) : Term.TermElabM (Option CoreInput) := do
  let e ←
    if t.getKind == ``Matrix.matrixLiteral then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let expected := mkApp3 (mkConst ``Matrix [Level.zero]) (mkConst ``Int) n n
      Term.elabTerm t (some expected)
    else
      Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  coreInput? e

/-- Emit the certified result for a core matrix. -/
public meta def resultForCore (input : CoreInput) : MetaM Expr := do
  let (_, p) ← computedPoly input
  let matrixLiteral ← reifyIntMatrix input.value
  let certificateInput := { input with expr := matrixLiteral }
  let certificate ← certificateExpr certificateInput
    (mkConst ``Lean.Grind.instCommRingInt)
  let source ← polyOfDescending certificate.literal
  let check ← beqCoeffsProof source p
  try
    mkAppM ``Matrix.CharPolyResult.ofCheck
      #[input.expr, certificate.literal, p, certificate.proof, check]
  catch _ =>
    throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the characteristic-polynomial check; the input is too opaque or Lean's ordinary reduction limits were reached"

/-- Evaluate and check a core dense-polynomial RHS, returning an informative
mismatch before asking the kernel to replay the equality. -/
private meta def checkCoreRhs (computed : DensePoly Int) (rhs : Expr) : MetaM Unit := do
  checkClosed "polynomial" rhs
  let ty ← inferType rhs
  match ← evalPolyCore ty rhs with
  | .error msg =>
      throwError "char_poly: failed to evaluate the polynomial in the goal{indentExpr rhs}\n{msg}"
  | .ok supplied =>
      unless DensePoly.beqCoeffs computed supplied do
        throwError "char_poly: the supplied polynomial has coefficients {supplied.toArray.toList}, but the computed characteristic polynomial has coefficients {computed.toArray.toList}"
      let literal ← reifyZPoly supplied
      unless ← withTransparency .all <| isDefEq literal rhs do
        throwError "char_poly: the polynomial{indentExpr rhs}\nevaluates to{indentExpr literal}\nbut is not definitionally transparent enough for kernel replay"

/-- Emit a proof of a direct core characteristic-polynomial equality. -/
private meta def proveCoreEquality (input : CoreInput) (rhs : Expr)
    (reverse : Bool) : MetaM Expr := do
  let (computed, _) ← computedPoly input
  checkCoreRhs computed rhs
  let matrixLiteral ← reifyIntMatrix input.value
  let certificateInput := { input with expr := matrixLiteral }
  let certificate ← certificateExpr certificateInput
    (mkConst ``Lean.Grind.instCommRingInt)
  let source ← polyOfDescending certificate.literal
  let check ← beqCoeffsProof source rhs
  let proof ← try
      mkAppM ``Matrix.charPoly_eq_of_check
        #[input.expr, certificate.literal, rhs, certificate.proof, check]
    catch _ =>
      throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the equality; Lean's ordinary reduction limits may have been reached"
  if reverse then mkEqSymm proof else return proof

/-- Find a core `charPoly` application on one side of an equality. -/
private meta def coreGoal? (target : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let some (_, lhs, rhs) := target.eq? | return none
  if lhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (lhs.getAppArgs.back!, rhs, false)
  if rhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (rhs.getAppArgs.back!, lhs, true)
  return none

/-- The result-producing term syntax. -/
syntax (name := charPolyTerm) "char_poly" term:max : term

/-- Expected-type-driven proof syntax used by bare `char_poly`. -/
syntax (name := charPolyProofTerm) "char_poly" : term

@[term_elab charPolyTerm] public meta def elabCharPoly : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(char_poly $t) =>
        let some input ← elabCoreArgument? t | Elab.throwUnsupportedSyntax
        let result ← resultForCore input
        Term.ensureHasType expectedType? result
    | _ => Elab.throwUnsupportedSyntax

@[term_elab charPolyProofTerm] public meta def elabCharPolyProof : Term.TermElab :=
  fun _stx expectedType? => do
    let some expectedType := expectedType? |
      throwError "char_poly: bare term syntax needs an expected characteristic-polynomial equality"
    let target ← instantiateMVars expectedType
    let some (matrix, rhs, reverse) ← coreGoal? target |
      Elab.throwUnsupportedSyntax
    let some input ← coreInput? matrix | Elab.throwUnsupportedSyntax
    let proof ← proveCoreEquality input rhs reverse
    Term.ensureHasType expectedType? proof

/-- Introduce the fields of either supported result type as a `poly` let and
a `charPoly_eq` hypothesis. -/
private meta def introResult (e : Expr) : Tactic.TacticM Unit := do
  let ty ← whnf (← inferType e)
  let fn := ty.getAppFn
  let fields? : Option (Name × Name) :=
    if fn.isConstOf ``Matrix.CharPolyResult then
      some (``Matrix.CharPolyResult.poly, ``Matrix.CharPolyResult.charPoly_eq)
    else if fn.isConstOf `HexCharPolyMathlib.CharPolyResult then
      some (`HexCharPolyMathlib.CharPolyResult.poly,
        `HexCharPolyMathlib.CharPolyResult.charPoly_eq)
    else none
  let some (polyName, equalityName) := fields? |
    throwError "char_poly: internal error: unrecognized result type{indentExpr ty}"
  let polyE ← mkAppM polyName #[e]
  let equalityE ← mkAppM equalityName #[e]
  let polyTy ← inferType polyE
  Tactic.liftMetaTactic fun goal => do
    let (polyFVar, goal) ← (← goal.define `poly polyTy polyE).intro1P
    goal.withContext do
      let equalityTy := (← inferType equalityE).replace fun x =>
        if x == polyE then some (mkFVar polyFVar) else none
      let (_, goal) ← (← goal.assert `charPoly_eq equalityTy equalityE).intro1P
      return [goal]

/-- Tactic form which introduces the certified result fields. -/
syntax (name := charPolyTac) "char_poly" term:max : tactic

@[tactic charPolyTac] public meta def evalCharPolyTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| char_poly $t) => do
        let term ← `(char_poly $t)
        let e ← Tactic.withMainContext do
          Term.elabTerm term none
        introResult e
    | _ => Elab.throwUnsupportedSyntax

/-- Bare tactic form: close a direct characteristic-polynomial equality. -/
macro "char_poly" : tactic => `(tactic| exact char_poly)

end Hex.CharPolyTactic
