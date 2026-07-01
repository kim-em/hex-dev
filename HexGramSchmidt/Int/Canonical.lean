/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int.Scaled
import all HexGramSchmidt.Int.Scaled

public section

namespace Hex
namespace GramSchmidt.Int
/-! ### Gram row-span invariant for no-pivot Bareiss -/

/-- Row-vector interpretation of the trailing block during a no-pivot Bareiss
pass over a Gram matrix.  Each active trailing row carries an explicit integer
coefficient vector `coeff i` such that the represented row is
`Matrix.vecMul (coeff i) b`, supported at coordinates `≤ i.val`, and
each matrix entry in that trailing row is its inner product against the
corresponding original row. -/
structure BareissGramRowInvariant (b : Matrix Int n m)
    (state : Matrix.BareissState n) where
  coeff : Fin n → Vector Int n
  coeff_supp : ∀ i k : Fin n, state.step ≤ i.val → i.val < k.val →
    (coeff i)[k] = 0
  entry_eq_dot : ∀ i j : Fin n, state.step ≤ i.val →
    state.matrix[i][j] =
      (Matrix.vecMul (coeff i) b).dotProduct (b.row j)

/-- The initial no-pivot Gram state satisfies the row-coefficient invariant
with each row represented by the standard basis vector `eᵢ`. -/
@[expose]
def bareissGramRowInvariant_initial (b : Matrix Int n m) :
    BareissGramRowInvariant b
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
  refine
    { coeff := fun i => Vector.ofFn fun k : Fin n => if i = k then 1 else 0
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k _hi hik
    by_cases h : i = k
    · subst k
      omega
    · simp [h]
  · intro i j _hi
    have hsingle :
        Matrix.vecMul (Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0) b =
          b.row i :=
      Matrix.IsRowReduced.vecMul_single (M := b) i
    rw [hsingle]
    simp [Matrix.noPivotInitialState, Matrix.gramMatrix, Matrix.ofFn, Vector.dotProduct]

/-- `foldl_sum_bareiss_row_update` pulls a Bareiss left row-update through a folded sum for later dot-product identities. -/
private theorem foldl_sum_bareiss_row_update
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + ((x * u a - y * v a) * w a))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + u a * w a) accU -
        y * xs.foldl (fun acc a => acc + v a * w a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + ((x * u a - y * v a) * w a) =
            x * (accU + u a * w a) - y * (accV + v a * w a) := by
        grind
      rw [hstep]
      exact ih (accU + u a * w a) (accV + v a * w a)

/-- `dot_bareiss_row_update_left` expands the dot product of a Bareiss-updated left vector as the corresponding linear combination of dots. -/
private theorem dot_bareiss_row_update_left
    (x y : Int) (u v w : Vector Int m) :
    (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]).dotProduct w =
      x * u.dotProduct w - y * v.dotProduct w := by
  unfold Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

/-- `foldl_sum_bareiss_row_update_right` pulls a Bareiss right row-update through a folded sum for the symmetric dot-product identity. -/
private theorem foldl_sum_bareiss_row_update_right
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + (w a * (x * u a - y * v a)))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + w a * u a) accU -
        y * xs.foldl (fun acc a => acc + w a * v a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + (w a * (x * u a - y * v a)) =
            x * (accU + w a * u a) - y * (accV + w a * v a) := by
        grind
      rw [hstep]
      exact ih (accU + w a * u a) (accV + w a * v a)

/-- `dot_bareiss_row_update_right` expands the dot product with a Bareiss-updated right vector as the corresponding linear combination of dots. -/
private theorem dot_bareiss_row_update_right
    (x y : Int) (w u v : Vector Int m) :
    w.dotProduct (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]) =
      x * w.dotProduct u - y * w.dotProduct v := by
  unfold Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update_right
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

/-- `vecMul_bareiss_coeff_update` shows that row combinations respect the Bareiss coefficient update used by the Gram-row invariant. -/
private theorem vecMul_bareiss_coeff_update
    (M : Matrix Int n m) (x y : Int) (c d : Vector Int n) :
    Matrix.vecMul (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]) M =
      Vector.ofFn fun j : Fin m =>
        x * (Matrix.vecMul c M)[j] - y * (Matrix.vecMul d M)[j] := by
  apply Vector.ext
  intro j hj
  let jf : Fin m := ⟨j, hj⟩
  show
      (Matrix.vecMul (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]) M)[jf] =
        (Vector.ofFn fun j : Fin m =>
          x * (Matrix.vecMul c M)[j] - y * (Matrix.vecMul d M)[j])[jf]
  unfold Matrix.vecMul
  have h_rhs :
      (Vector.ofFn fun j : Fin m => x * (M.transpose * c)[j] - y * (M.transpose * d)[j])[jf] =
        x * (M.transpose * c)[jf] - y * (M.transpose * d)[jf] := by
    simp
  rw [h_rhs]
  repeat rw [Matrix.getElem_mulVec]
  exact dot_bareiss_row_update_right x y ((Matrix.transpose M).row jf) c d

/-- `exactDiv_eq_of_eq_mul_right` recovers the right quotient when the exact-division numerator is a quotient times the nonzero denominator. -/
private theorem exactDiv_eq_of_eq_mul_right
    {num denom q : Int} (hdenom : denom ≠ 0) (hnum : num = q * denom) :
  Matrix.exactDiv num denom = q := by
  have hnum' : num = denom * q := by
    grind
  have hdvd : denom ∣ num := by
    refine ⟨q, ?_⟩
    exact hnum'
  rw [Matrix.exactDiv_eq_divExact hdvd, Int.divExact_eq_ediv hdvd]
  exact Int.ediv_eq_of_eq_mul_left hdenom hnum

/-- `vector_exactDiv_eq_of_eq_mul_right` applies exact-division quotient recovery pointwise to coefficient vectors. -/
private theorem vector_exactDiv_eq_of_eq_mul_right
    {denom : Int} (hdenom : denom ≠ 0) (num q : Fin n → Int)
    (hnum : ∀ a : Fin n, num a = q a * denom) :
    (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) =
      Vector.ofFn q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simp [exactDiv_eq_of_eq_mul_right hdenom (hnum af), af]

/-- `vecMul_exactDiv_eq_of_eq_mul_right` replaces exact-divided coefficients by their quotient vector inside a row combination. -/
private theorem vecMul_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom) :
    Matrix.vecMul (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) M =
      Matrix.vecMul (Vector.ofFn q) M := by
  rw [vector_exactDiv_eq_of_eq_mul_right hdenom num q hnum]

/-- `dot_vecMul_exactDiv_eq_of_eq_mul_right` carries exact-division quotient recovery through a row combination and final dot product. -/
private theorem dot_vecMul_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom)
    (w : Vector Int m) :
    Vector.dotProduct
        (Matrix.vecMul (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) M)
        w =
      (Matrix.vecMul (Vector.ofFn q) M).dotProduct w := by
  rw [vecMul_exactDiv_eq_of_eq_mul_right M hdenom num q hnum]

/-- Project the explicit coefficient witness for the row at index `i`. -/
private def bareissGramRowInvariantCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) : Vector Int n :=
  hinv.coeff i

/-- `bareissGramRowInvariantCoeff_support` exposes the support vanishing condition for the projected Gram-row coefficient witness. -/
private theorem bareissGramRowInvariantCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n)
    (hi : state.step ≤ i.val) :
    ∀ k : Fin n, i.val < k.val →
      (bareissGramRowInvariantCoeff hinv i)[k] = 0 :=
  fun k hik => hinv.coeff_supp i k hi hik

/-- `bareissGramRowInvariantCoeff_row` identifies the projected Gram-row coefficient witness with the invariant's stored coefficient row. -/
private theorem bareissGramRowInvariantCoeff_row
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) :
    Matrix.vecMul (bareissGramRowInvariantCoeff hinv i) b =
      Matrix.vecMul (hinv.coeff i) b := rfl

/-- Coefficient witness produced by one regular Bareiss step on the row at
index `i`.  The functional shape mirrors the row update on the matrix side. -/
@[expose]
def bareissGramRowInvariantStepCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) :
    Vector Int n :=
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  Vector.ofFn fun a : Fin n =>
    Matrix.exactDiv
      (state.matrix[(k, k)] * (hinv.coeff i)[a] -
        state.matrix[(i, k)] * (hinv.coeff k)[a])
      state.prevPivot

/-- Coefficient-level exact-division provenance for one regular Gram-row
Bareiss step.  The quotient vector is kept separate from
`bareissGramRowInvariantStepCoeff` so later row-entry proofs can consume the
integer divisibility witness before projecting back to the existing exact-div
coefficient API. -/
structure BareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) where
  q : Fin n → Int
  coeff_num_eq_mul :
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    ∀ a : Fin n,
      state.matrix[(k, k)] * (hinv.coeff i)[a] -
        state.matrix[(i, k)] * (hinv.coeff k)[a] =
          q a * state.prevPivot

private theorem bareissGramRegularStepQuotient_stepCoeff_get
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) (a : Fin n) :
    (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = hq.q a := by
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  exact exactDiv_eq_of_eq_mul_right hprev (hq.coeff_num_eq_mul a)

private theorem bareissGramRegularStepQuotient_stepCoeff_eq
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    bareissGramRowInvariantStepCoeff hinv hnext i hi = Vector.ofFn hq.q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simpa [af] using
    bareissGramRegularStepQuotient_stepCoeff_get
      (hinv := hinv) (hnext := hnext) (i := i) (hi := hi) hprev hq af

private theorem vecMul_bareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b =
      Matrix.vecMul (Vector.ofFn hq.q) b := by
  rw [bareissGramRegularStepQuotient_stepCoeff_eq hprev hq]

theorem bareissGramRowInvariantStepCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (hi : state.step + 1 ≤ i.val) :
    ∀ a : Fin n, i.val < a.val →
      (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = 0 := by
  intro a hia
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have h_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ state.step) hi
  have h_k : state.step ≤ k.val := Nat.le_refl _
  have hci : (hinv.coeff i)[a] = 0 := hinv.coeff_supp i a h_i hia
  have hk_lt_i : k.val < i.val := by
    dsimp [k]
    omega
  have hka : k.val < a.val := Nat.lt_trans hk_lt_i hia
  have hck : (hinv.coeff k)[a] = 0 := hinv.coeff_supp k a h_k hka
  have hciNat : (hinv.coeff i)[a.val] = 0 := by simpa using hci
  have hckNat :
      (hinv.coeff
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩ : Fin n))[a.val] = 0 := by
    simpa [k] using hck
  simp [hciNat, hckNat, Matrix.exactDiv]

/-! ### Canonical coefficient vector and canonicity predicate -/

/-- Canonical row-coefficient vector for the initial no-pivot Gram trajectory.

Base case: each row carries the standard basis vector `e_i`. Inductive step
(regular branch, active row): apply the fraction-free Bareiss row update via
`exactDiv`. Processed rows, singular branches, and done branches preserve the
previous vector unchanged — mirroring the row-invariant evolution in
`bareissGramRowInvariant_noPivotLoop_initialAux`.

Defined as a pure function of `b` and `fuel` (no `BareissGramRowInvariant`
argument), so the canonical coefficient is fixed by the matrix and step
count alone. Non-canonical row-coefficient witnesses are ruled out by the
`IsCanonicalAt` predicate consumed by `StepWitness`. -/
@[expose]
def bareissGramCanonicalCoeff (b : Matrix Int n m) :
    Nat → Fin n → Vector Int n
  | 0, i => Vector.ofFn fun k : Fin n => if i = k then 1 else 0
  | fuel + 1, i =>
    let state := Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
    if hnext : state.step + 1 < n then
      if state.matrix[(state.step, state.step)] = 0 then
        bareissGramCanonicalCoeff b fuel i
      else if state.step + 1 ≤ i.val then
        let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
        Vector.ofFn fun a : Fin n =>
          Matrix.exactDiv
            (state.matrix[(k, k)] * (bareissGramCanonicalCoeff b fuel i)[a] -
              state.matrix[(i, k)] * (bareissGramCanonicalCoeff b fuel k)[a])
            state.prevPivot
      else
        bareissGramCanonicalCoeff b fuel i
    else
      bareissGramCanonicalCoeff b fuel i

/-- The canonical coefficient at `fuel = 0` is the standard basis vector. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_zero
    (b : Matrix Int n m) (i : Fin n) :
    bareissGramCanonicalCoeff b 0 i =
      Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0 := rfl

/-- Recursion equation: regular-branch active-row case. With the branch
hypotheses in context, `simp [*]`/`simp_all` rewrites `bareissGramCanonicalCoeff`
at `fuel + 1` to its explicit Bareiss exact-division update. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_regular
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      (let state := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))
       let k : Fin n :=
         ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
       Vector.ofFn fun a : Fin n =>
         Matrix.exactDiv
           (state.matrix[k][k] * (bareissGramCanonicalCoeff b fuel i)[a] -
             state.matrix[i][k] * (bareissGramCanonicalCoeff b fuel k)[a])
           state.prevPivot) := by
  simp [bareissGramCanonicalCoeff, dif_pos hnext, if_pos hi]
  intro hc
  exact absurd hc hp

/-- Recursion equation: regular-branch processed-row case. An already-processed
row (`i ≤ step`) keeps its previous coefficient vector, so the canonical
coefficient at `fuel + 1` collapses to the one at `fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_processed
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hi : ¬ (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp [bareissGramCanonicalCoeff, dif_pos hnext, if_neg hi]

/-- Recursion equation: singular branch (zero diagonal). A zero pivot skips the
update, so the canonical coefficient at `fuel + 1` collapses to the one at
`fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_singular
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] = 0) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp [bareissGramCanonicalCoeff, dif_pos hnext]
  intro hc
  exact absurd hp hc

/-- Recursion equation: done branch (no further work possible). Once the loop can
take no further step (`¬ step + 1 < n`), the canonical coefficient at `fuel + 1`
collapses to the one at `fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_done
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hDone : ¬ (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp only [bareissGramCanonicalCoeff, dif_neg hDone]

/-- A `BareissGramRowInvariant` on `noPivotLoop fuel (noPivotInitialState …)`
is *canonical at `fuel`* when every row's coefficient vector matches
`bareissGramCanonicalCoeff`. This is the soundness gate consumed by
`StepWitness`: non-canonical witnesses (which can shift coefficients by a
kernel vector while keeping `entry_eq_dot` satisfied) cannot invoke the
witness's quotient identity.

The SPEC counterexample at rows `(1,1), (1,0), (-1,-1)` (#6505) produces two
distinct `BareissGramRowInvariant` instances at the same loop state whose
coefficient vectors differ by the kernel vector. Both satisfy `entry_eq_dot`,
but only one (the canonical one) yields an integer Bareiss-step quotient. -/
@[expose]
def IsCanonicalAt (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)))) : Prop :=
  ∀ i : Fin n, hinv.coeff i = bareissGramCanonicalCoeff b fuel i

/-- The base-case row invariant at `fuel = 0` carries the standard basis vectors
and is therefore canonical. -/
theorem isCanonicalAt_initial (b : Matrix Int n m) :
    IsCanonicalAt b 0 (bareissGramRowInvariant_initial b) := by
  intro i
  rfl

/-- Transport along an equation of `BareissState`s preserves the `coeff` field
of a `BareissGramRowInvariant`. The field's type `Fin n → Vector Int n` does
not depend on the state index, so transport is the identity at that
projection. Used to discharge canonicity proofs after transporting an explicit
intermediate state back to the `noPivotLoop fuel initial` form. -/
theorem bareissGramRowInvariant_coeff_transport
    {b : Matrix Int n m} {st1 st2 : Matrix.BareissState n}
    (h : st1 = st2) (x : BareissGramRowInvariant b st2) (i : Fin n) :
    (h ▸ x).coeff i = x.coeff i := by
  cases h
  rfl

/-- Right-scalar linearity of the dot product against a `vecMul` whose
coefficient vector is multiplied pointwise by a constant on the right.  Used
to factor the Bareiss exact-division denominator out of a quotient-backed row
combination. -/
private theorem dot_vecMul_mul_right_int
    (b : Matrix Int n m) (f : Fin n → Int) (s : Int) (w : Vector Int m) :
    Vector.dotProduct
        (Matrix.vecMul (Vector.ofFn fun a : Fin n => f a * s) b) w =
      (Matrix.vecMul (Vector.ofFn f) b).dotProduct w * s := by
  have h_eq_input :
      (Vector.ofFn fun a : Fin n => f a * s) =
        Vector.ofFn fun a : Fin n =>
          s * (Vector.ofFn f)[a] - 0 * (Vector.ofFn f)[a] := by
    apply Vector.ext
    intro a ha
    simp only [Vector.getElem_ofFn]
    grind
  rw [h_eq_input, vecMul_bareiss_coeff_update b s 0 (Vector.ofFn f) (Vector.ofFn f)]
  rw [dot_bareiss_row_update_left s 0
    (Matrix.vecMul (Vector.ofFn f) b)
    (Matrix.vecMul (Vector.ofFn f) b) w]
  grind

/-- Row-entry algebra for one regular Gram-row Bareiss step.  Consuming the
quotient-coefficient package `BareissGramRegularStepQuotient` together with a
nonzero `prevPivot` and the already-processed-column zero entries gives the
exact row-entry relation for `Matrix.stepMatrix` at row `i` and any column
`j`.  Covers the three column regimes: `j.val < state.step` (already-cleared
column, both sides zero), `j.val = state.step` (pivot column below the pivot,
both sides zero), and `state.step < j.val` (trailing block, `exactDiv` of the
Bareiss numerator). -/
private theorem bareissGramRegularStep_entry_eq_dot
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi)
    (h_processed : ∀ i' : Fin n, state.step ≤ i'.val →
      ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0)
    (j : Fin n) :
    (Matrix.stepMatrix state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot)[i][j] =
      Vector.dotProduct
        (Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b)
        (b.row j) := by
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have hk_val : k.val = state.step := rfl
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_lt_i : state.step < i.val := hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  let lhsNum : Int :=
    state.matrix[k][k] * state.matrix[i][j] - state.matrix[i][k] * state.matrix[k][j]
  have hLHS_num : lhsNum =
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := rfl
  -- Claim A: the dot product of the "numerator-side" row combination is lhsNum.
  have h_dot_num :
      Vector.dotProduct
          (Matrix.vecMul (Vector.ofFn fun a : Fin n =>
              state.matrix[k][k] * (hinv.coeff i)[a] -
                state.matrix[i][k] * (hinv.coeff k)[a]) b)
          (b.row j) = lhsNum := by
    rw [vecMul_bareiss_coeff_update b
      state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
    rw [dot_bareiss_row_update_left
      state.matrix[k][k] state.matrix[i][k]
      (Matrix.vecMul (hinv.coeff i) b)
      (Matrix.vecMul (hinv.coeff k) b)
      (b.row j)]
    rw [← hinv.entry_eq_dot i j h_step_le_i,
        ← hinv.entry_eq_dot k j h_step_le_k]
  -- Claim B: the dot product of the step coefficient row combination equals
  -- `exactDiv lhsNum prevPivot`.
  have h_dot_step :
      Vector.dotProduct
          (Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b)
          (b.row j) = Matrix.exactDiv lhsNum state.prevPivot := by
    rw [vecMul_bareissGramRegularStepQuotient hprev hq]
    refine (exactDiv_eq_of_eq_mul_right hprev ?_).symm
    have h_dot_mul :=
      dot_vecMul_mul_right_int b hq.q state.prevPivot (b.row j)
    rw [← h_dot_mul]
    have h_q_eq_num :
        (Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot) =
          (Vector.ofFn fun a : Fin n =>
            state.matrix[k][k] * (hinv.coeff i)[a] -
              state.matrix[i][k] * (hinv.coeff k)[a]) := by
      apply Vector.ext
      intro a ha
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
      exact (hq.coeff_num_eq_mul ⟨a, ha⟩).symm
    rw [h_q_eq_num]
    exact h_dot_num.symm
  -- Case split on `j.val` against `state.step`.
  by_cases hjk : state.step < j.val
  · -- Trailing block: stepMatrix is the Bareiss exactDiv update.
    rw [Matrix.stepMatrix_update_eq state.matrix state.step
      state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjk]
    rw [h_dot_step]
    rfl
  · by_cases hjeq : j.val = state.step
    · -- Pivot column, below the pivot: stepMatrix entry is 0, and `lhsNum = 0`.
      rw [Matrix.stepMatrix_pivot_col_below state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjeq]
      rw [h_dot_step]
      have h_j_eq_k : j = k := Fin.ext (by rw [hjeq, hk_val])
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_j_eq_k]; grind
      rw [h_lhs_num_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)
    · -- Already-processed column: stepMatrix carries over, both sides zero.
      have hj_lt : j.val < state.step :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hjk) hjeq
      have h_not_trail : ¬ (state.step < i.val ∧ state.step < j.val) := by
        intro ⟨_, h2⟩; exact absurd h2 (Nat.not_lt_of_le (Nat.le_of_lt hj_lt))
      have h_not_col : ¬ (state.step < i.val ∧ j.val = state.step) := by
        intro ⟨_, h2⟩; exact hjeq h2
      rw [Matrix.stepMatrix_eq_of_not_update state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_not_trail h_not_col]
      have h_i_j_zero : state.matrix[i][j] = 0 := h_processed i h_step_le_i j hj_lt
      have h_k_j_zero : state.matrix[k][j] = 0 := h_processed k h_step_le_k j hj_lt
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_i_j_zero, h_k_j_zero]; grind
      rw [h_dot_step, h_lhs_num_zero, h_i_j_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)

/-- One regular no-pivot Bareiss step preserves the Gram row-coefficient
invariant, provided the later loop proof supplies the exact-division entry
relation for the fraction-free updated row combinations. -/
@[expose]
def bareissGramRowInvariant_regular_step
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hnext : state.step + 1 < n)
    (_hp : state.matrix[state.step][state.step] ≠ 0)
    (hinv : BareissGramRowInvariant b state)
    (hentry :
      ∀ i j : Fin n, (hi : state.step + 1 ≤ i.val) →
        (Matrix.stepMatrix state.matrix state.step
            state.matrix[state.step][state.step] state.prevPivot)[i][j] =
          Vector.dotProduct
            (Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b)
            (b.row j)) :
    BareissGramRowInvariant b
      { step := state.step + 1
        matrix := Matrix.stepMatrix state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } := by
  refine
    { coeff := fun i =>
        if hi : state.step + 1 ≤ i.val then
          bareissGramRowInvariantStepCoeff hinv hnext i hi
        else
          hinv.coeff i
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k hi hik
    have hi' : state.step + 1 ≤ i.val := hi
    simp [hi', bareissGramRowInvariantStepCoeff_support hinv hnext i hi' k hik]
  · intro i j hi
    have hi' : state.step + 1 ≤ i.val := hi
    simpa [hi'] using hentry i j hi'

/-- The coefficient vectors produced by `bareissGramRowInvariant_regular_step`
from a canonical input invariant match `bareissGramCanonicalCoeff` at the
next-step fuel index. Used to propagate canonicity through one regular Bareiss
step inside `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
theorem bareissGramRowInvariant_regular_step_coeff_canonical
    (b : Matrix Int n m) (elapsed : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b elapsed hinv)
    (hnext :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hentry :
      ∀ i j : Fin n,
        (hi : (Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) →
        (Matrix.stepMatrix
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (Matrix.noPivotLoop elapsed
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
              (Matrix.noPivotLoop elapsed
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step]
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot)[i][j] =
          Vector.dotProduct
            (Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b)
            (b.row j))
    (i : Fin n) :
    (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
      bareissGramCanonicalCoeff b (elapsed + 1) i := by
  -- The regular_step constructor produces `if step+1 ≤ i.val then stepCoeff else hinv.coeff i`.
  by_cases hi : (Matrix.noPivotLoop elapsed
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val
  · have hLHS :
        (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
          bareissGramRowInvariantStepCoeff hinv hnext i hi := by
      show (if hi : _ then _ else _) = _
      rw [dif_pos hi]
    rw [hLHS, bareissGramCanonicalCoeff_succ_regular b elapsed i hnext hp hi]
    show Vector.ofFn (fun a : Fin n =>
        Matrix.exactDiv
          (_ * (hinv.coeff i)[a] - _ * (hinv.coeff _)[a])
          _) = _
    rw [h_canon i,
        h_canon ⟨(Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step,
          Nat.lt_trans (Nat.lt_succ_self _) hnext⟩]
    simp only [Hex.Matrix.getElem_pair_eq_nested]
  · have hLHS :
        (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
          hinv.coeff i := by
      show (if hi : _ then _ else _) = _
      rw [dif_neg hi]
    rw [hLHS, bareissGramCanonicalCoeff_succ_processed b elapsed i hnext hp hi]
    exact h_canon i

/-- If the initial no-pivot Gram pass reaches column `s` without recording a
singular step, its state step is exactly `s`.  This keeps the later singular
pivot argument from unfolding the loop just to align the searched column. -/
private theorem noPivotLoop_initial_gram_step_eq
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s := by
  have h_room :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + s + 1 ≤ n := by
    simp [Matrix.noPivotInitialState]
    omega
  have h_step :=
    Matrix.noPivotLoop_step_eq_add_of_singularStep_none s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_room h_prefix_none
  simpa [Matrix.noPivotInitialState] using h_step

/-- On a nonsingular initial no-pivot Gram trajectory, any current state that is
ready for a regular next step has a nonzero previous pivot. -/
private theorem noPivotLoop_initial_gram_prevPivot_ne_zero
    (b : Matrix Int n m) (fuel : Nat)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (_hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0) :
    (Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot ≠ 0 := by
  apply noPivotLoop_prevPivot_ne_zero
  · simp [Matrix.noPivotInitialState]
  · exact h_prefix_none

/-- Package a proved zero suffix in the current Gram pivot column into the
executable row-pivot search failure expected by `Matrix.pivotLoop`. -/
private theorem noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_column_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    Matrix.findPivot?
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n) (s + 1) = none := by
  have _h_step :=
    noPivotLoop_initial_gram_step_eq b s hs h_prefix_none
  exact Matrix.findPivot?_eq_none_of_zero _ _ _ h_column_zero

/-- After running `noPivotLoop fuel` from a state with `singularStep = none`, if
the result also has `singularStep = none`, then every column strictly between
the initial step and the final step is zero below the pivot in the final
matrix. Each such column was processed by a regular Bareiss step that cleared
its sub-diagonal entries, and no later iteration touches them. -/
private theorem noPivotLoop_matrix_processed_col_eq_zero {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (Matrix.noPivotLoop fuel state).singularStep = none →
      ∀ (k : Nat), state.step ≤ k →
        k < (Matrix.noPivotLoop fuel state).step →
        ∀ (kFin : Fin n), kFin.val = k →
        ∀ (i : Fin n), k < i.val →
          (Matrix.noPivotLoop fuel state).matrix[i][kFin] = 0 := by
  induction fuel with
  | zero =>
      intros state _h_result k hk_ge hk_lt _kFin _hkFin i _hki
      simp [Matrix.noPivotLoop_zero_fuel] at hk_lt
      omega
  | succ f ih =>
      intros state h_result_none k hk_ge hk_lt kFin hkFin i hki
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch contradicts h_result_none.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_result_none
          simp at h_result_none
        · -- Regular branch.
          let next : Matrix.BareissState n :=
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          have h_eq_next : Matrix.noPivotLoop (f + 1) state =
              Matrix.noPivotLoop f next :=
            Matrix.noPivotLoop_regular_branch f state hDone hp
          rw [h_eq_next] at h_result_none hk_lt ⊢
          by_cases hk_eq : k = state.step
          · -- k just got processed: column k was zeroed by stepMatrix.
            have hi_lt : state.step < i.val := hk_eq ▸ hki
            have hkFin_eq : kFin.val = state.step := hk_eq ▸ hkFin
            have h_next_zero : next.matrix[i][kFin] = 0 :=
              Matrix.stepMatrix_pivot_col_below state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot i kFin hi_lt hkFin_eq
            have h_fixed : kFin.val < next.step := by
              change kFin.val < state.step + 1
              omega
            have h_eq :=
              Matrix.noPivotLoop_matrix_entry_of_row_le_or_col_lt f next i kFin
                (Or.inr h_fixed)
            rw [h_eq]
            exact h_next_zero
          · -- k was processed at a later step inside `next`.
            have hk_ge_next : next.step ≤ k := by
              change state.step + 1 ≤ k
              omega
            exact ih next h_result_none k hk_ge_next hk_lt kFin hkFin i hki
      · -- Done branch: state.step unchanged, so hk_lt collapses.
        have h_eq_state : Matrix.noPivotLoop (f + 1) state = state :=
          Matrix.noPivotLoop_done f state hDone
        rw [h_eq_state] at h_result_none hk_lt ⊢
        omega

/-- Initial no-pivot Gram trajectory specialization of the regular row-entry
algebra.  The quotient package supplies the coefficient-side divisibility
provenance; the initial trajectory supplies nonzero `prevPivot` and the
already-processed column zeros needed by the one-step algebra. -/
private theorem bareissGramInitialRegularStep_entry_eq_dot
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    (Matrix.stepMatrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step]
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot)[i][j] =
      Vector.dotProduct
        (Matrix.vecMul (bareissGramRowInvariantStepCoeff hinv hnext i hi) b)
        (b.row j) := by
  let state :=
    Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
  have hprev : state.prevPivot ≠ 0 :=
    noPivotLoop_initial_gram_prevPivot_ne_zero
      b fuel h_prefix_none hnext hp
  have h_processed :
      ∀ i' : Fin n, state.step ≤ i'.val →
        ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0 := by
    intro i' hi' j' hj'
    exact noPivotLoop_matrix_processed_col_eq_zero fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
      j'.val (by simp [Matrix.noPivotInitialState]) hj' j' rfl i'
      (Nat.lt_of_lt_of_le hj' hi')
  exact bareissGramRegularStep_entry_eq_dot hprev hq h_processed j

/-- Per-step quotient package for the initial no-pivot Gram trajectory,
restricted to *canonical* row-coefficient witnesses via `IsCanonicalAt`.

`StepWitness.Cell` is an alias for `BareissGramRegularStepQuotient` whose
canonicity gate (`h_canon`) prevents non-canonical `BareissGramRowInvariant`
witnesses — which can shift coefficients by a kernel vector while still
satisfying `entry_eq_dot` — from supplying integer quotients. The kernel-shift
counterexample (SPEC #6505: rows `(1,1), (1,0), (-1,-1)` at row 2 step 1)
shows the restriction is necessary: distinct non-canonical witnesses produce
numerators differing by `1`, which is not divisible by `prevPivot = 2`. -/
abbrev StepWitness.Cell
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (_h_canon : IsCanonicalAt b fuel hinv)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    Type :=
  BareissGramRegularStepQuotient hinv hnext i hi

/-- Quotient provenance for the initial no-pivot Gram trajectory, restricted
to canonical `BareissGramRowInvariant` witnesses via `IsCanonicalAt`. The
provider supplies, at every reachable regular Bareiss step, an integer
quotient `q : Fin n → Int` realising the Bareiss-row-update divisibility on
the canonical coefficient vectors.

Concrete providers are constructed in `HexGramSchmidtMathlib`, where the
Bareiss-Desnanot proof infrastructure on PSD Gram minors is available; the
Mathlib-free layer only consumes this abstraction. -/
abbrev StepWitness (b : Matrix Int n m) : Type :=
  ∀ (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b fuel hinv)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val),
      StepWitness.Cell b fuel hinv h_canon hnext i hi

/-- Canonical row-coefficients are unchanged once the no-pivot Bareiss loop
has reached the boundary `state.step + 1 = n`. Used to propagate canonicity
through the done branch of `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
private theorem bareissGramCanonicalCoeff_eq_of_done
    {n m : Nat} (b : Matrix Int n m) (elapsed j : Nat) (i : Fin n)
    (hDone :
      ¬ (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n) :
    bareissGramCanonicalCoeff b (elapsed + j) i =
      bareissGramCanonicalCoeff b elapsed i := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h_state_eq :
          Matrix.noPivotLoop (elapsed + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
        rw [noPivotLoop_add elapsed j]
        exact noPivotLoop_id_at_done j _ hDone
      have hDone' :
          ¬ (Matrix.noPivotLoop (elapsed + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
        rw [h_state_eq]; exact hDone
      rw [show elapsed + (j + 1) = (elapsed + j) + 1 from by omega,
          bareissGramCanonicalCoeff_succ_done b (elapsed + j) i hDone']
      exact ih

/-- State-equation variant of `bareissGramCanonicalCoeff_succ_singular`: when
the no-pivot Bareiss state at `fuel` is propositionally equal to some `s`, the
singular hypothesis on `s` propagates to the canonical-coefficient identity at
`fuel + 1`. Used by `bareissGramCanonicalCoeff_eq_of_singular` to apply the
succ-singular equation at the singular fixed-point without rewriting through
dependent matrix-access proofs. -/
private theorem bareissGramCanonicalCoeff_succ_singular_of_state_eq
    {n m : Nat} (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    {s : Matrix.BareissState n}
    (h_state : Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) = s)
    (hDone : s.step + 1 < n)
    (hp : s.matrix[s.step][s.step] = 0) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  subst h_state
  exact bareissGramCanonicalCoeff_succ_singular b fuel i hDone hp

/-- Canonical row-coefficients are unchanged by extending the no-pivot Bareiss
loop past a singular step. Used to propagate canonicity through the singular
branch of `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
private theorem bareissGramCanonicalCoeff_eq_of_singular
    {n m : Nat} (b : Matrix Int n m) (elapsed j : Nat) (i : Fin n)
    (hDone :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] = 0) :
    bareissGramCanonicalCoeff b (elapsed + 1 + j) i =
      bareissGramCanonicalCoeff b elapsed i := by
  induction j with
  | zero =>
      exact bareissGramCanonicalCoeff_succ_singular b elapsed i hDone hp
  | succ j ih =>
      have h_one :
          Matrix.noPivotLoop (elapsed + 1)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          { (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) with
            singularStep := some (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step } := by
        rw [noPivotLoop_add elapsed 1]
        exact Matrix.noPivotLoop_singular_branch 0 _ hDone hp
      have h_state_eq :
          Matrix.noPivotLoop (elapsed + 1 + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          { (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) with
            singularStep := some (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step } := by
        rw [noPivotLoop_add (elapsed + 1) j, h_one]
        exact noPivotLoop_id_at_singular_fixedpoint j _ hDone hp rfl
      rw [show elapsed + 1 + (j + 1) = (elapsed + 1 + j) + 1 from by omega,
          bareissGramCanonicalCoeff_succ_singular_of_state_eq
            b (elapsed + 1 + j) i h_state_eq hDone hp]
      exact ih

end GramSchmidt.Int
end Hex
