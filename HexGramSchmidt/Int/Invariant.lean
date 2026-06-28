module

public import HexGramSchmidt.Int.Canonical
import all HexGramSchmidt.Int.Canonical

public section

namespace Hex
namespace GramSchmidt.Int
/-- Initial no-pivot Gram specialization indexed by elapsed fuel.  The regular
branch no longer asks callers for a row-entry equation; it obtains the
reachable row-entry relation from `bareissGramInitialRegularStep_entry_eq_dot`
using the supplied quotient provenance.

Threads `IsCanonicalAt` through the recursion so that the canonicity gate of
`StepWitness` can be discharged at every regular step. The return type packages
the row invariant together with the proof that its coefficients match
`bareissGramCanonicalCoeff` at the elapsed-plus-fuel index. -/
private def bareissGramRowInvariant_noPivotLoop_initialAux
    (b : Matrix Int n m) (elapsed fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b elapsed hinv)
    (h_prefix_none :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hquot : StepWitness b) :
    { hinv' : BareissGramRowInvariant b
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)))) //
      ∀ i : Fin n,
        hinv'.coeff i = bareissGramCanonicalCoeff b (elapsed + fuel) i } := by
  induction fuel generalizing elapsed with
  | zero =>
      exact ⟨hinv, h_canon⟩
  | succ fuel ih =>
      let state :=
        Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch fuel state hDone hp]
          refine ⟨{ coeff := hinv.coeff
                    coeff_supp := ?_
                    entry_eq_dot := ?_ }, ?_⟩
          · simpa using hinv.coeff_supp
          · simpa using hinv.entry_eq_dot
          · intro i
            show hinv.coeff i = bareissGramCanonicalCoeff b (elapsed + (fuel + 1)) i
            rw [h_canon i,
                show elapsed + (fuel + 1) = elapsed + 1 + fuel from by omega]
            exact (bareissGramCanonicalCoeff_eq_of_singular
              b elapsed fuel i hDone hp).symm
        · rw [Matrix.noPivotLoop_regular_branch fuel state hDone hp]
          have hstep :
              Matrix.noPivotLoop (elapsed + 1)
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
                ({ step := state.step + 1
                   matrix := Matrix.stepMatrix state.matrix state.step
                     state.matrix[state.step][state.step] state.prevPivot
                   prevPivot := state.matrix[state.step][state.step]
                   rowSwaps := state.rowSwaps
                   singularStep := none } : Matrix.BareissState n) := by
            rw [noPivotLoop_add elapsed 1
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))]
            rw [Matrix.noPivotLoop_regular_branch 0 state hDone hp]
            simp [Matrix.noPivotLoop_zero_fuel]
          have hentry := fun i j hi =>
            bareissGramInitialRegularStep_entry_eq_dot
              (b := b) elapsed hinv h_prefix_none hDone hp i j hi
              (hquot elapsed hinv h_canon h_prefix_none hDone hp i hi)
          let hinv_next := bareissGramRowInvariant_regular_step hDone hp hinv hentry
          have h_canon_next_pre :
              ∀ i : Fin n,
                hinv_next.coeff i = bareissGramCanonicalCoeff b (elapsed + 1) i := fun i =>
            bareissGramRowInvariant_regular_step_coeff_canonical
              b elapsed hinv h_canon hDone hp hentry i
          rw [← hstep]
          have h_canon_next :
              IsCanonicalAt b (elapsed + 1) (hstep ▸ hinv_next) := by
            intro i
            show (hstep ▸ hinv_next).coeff i = bareissGramCanonicalCoeff b (elapsed + 1) i
            rw [bareissGramRowInvariant_coeff_transport hstep hinv_next i]
            exact h_canon_next_pre i
          have h_prefix_next :
              (Matrix.noPivotLoop (elapsed + 1)
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
            rw [hstep]
          let ih_result :=
            ih (elapsed := elapsed + 1) (hstep ▸ hinv_next) h_canon_next h_prefix_next
          refine ⟨ih_result.1, ?_⟩
          intro i
          rw [show elapsed + (fuel + 1) = (elapsed + 1) + fuel from by omega]
          exact ih_result.2 i
      · rw [Matrix.noPivotLoop_done fuel state hDone]
        refine ⟨hinv, ?_⟩
        intro i
        rw [h_canon i]
        exact (bareissGramCanonicalCoeff_eq_of_done b elapsed (fuel + 1) i hDone).symm

/-- Initial-state specialization of the row invariant for the no-pivot pass
over a Gram matrix.  Callers supply only quotient provenance for reachable
regular branches; the row-entry equation is derived internally. -/
private def bareissGramRowInvariant_noPivotLoop_initial
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b) :
    BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState (Matrix.gramMatrix b))) :=
  (bareissGramRowInvariant_noPivotLoop_initialAux
    (b := b) 0 fuel (bareissGramRowInvariant_initial b)
    (isCanonicalAt_initial b) rfl hquot).1

/-- The produced row invariant from the initial no-pivot Gram trajectory is
canonical: its coefficients match `bareissGramCanonicalCoeff` at every fuel
index. This is the canonicity gate consumed by `StepWitness.Cell`. -/
private theorem bareissGramRowInvariant_noPivotLoop_initial_canonical
    (b : Matrix Int n m) (fuel : Nat) (hquot : StepWitness b) :
    IsCanonicalAt b fuel
      (bareissGramRowInvariant_noPivotLoop_initial b fuel hquot) := by
  intro i
  simpa using (bareissGramRowInvariant_noPivotLoop_initialAux
    (b := b) 0 fuel (bareissGramRowInvariant_initial b)
    (isCanonicalAt_initial b) rfl hquot).2 i

/-- Matrix-level Bareiss-step divisibility on the initial no-pivot Gram
trajectory: the numerator of one fraction-free row update is divisible by the
previous pivot. The witness comes from the canonical-`StepWitness` quotient
package applied at the reachable regular step, with the matrix-level numerator
recovered by taking the dot product of the coefficient-level identity against
the input row `b.row j`. -/
private theorem noPivotLoop_initial_gram_bareiss_step_dvd
    (b : Matrix Int n m) (hquot : StepWitness b)
    (fuel : Nat)
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
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    let state := Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    state.prevPivot ∣
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := by
  intro state k
  let hinv := bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  let h_canon := bareissGramRowInvariant_noPivotLoop_initial_canonical b fuel hquot
  have hq := hquot fuel hinv h_canon h_prefix_none hnext hp i hi
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  refine ⟨Matrix.dot (Matrix.rowCombination b (Vector.ofFn hq.q)) (b.row j), ?_⟩
  rw [hinv.entry_eq_dot i j h_step_le_i, hinv.entry_eq_dot k j h_step_le_k]
  rw [← dot_bareiss_row_update_left state.matrix[k][k] state.matrix[i][k]
        (Matrix.rowCombination b (hinv.coeff i))
        (Matrix.rowCombination b (hinv.coeff k))
        (b.row j)]
  rw [← rowCombination_bareiss_coeff_update b
        state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
  have h_q_eq_num :
      (Vector.ofFn fun a : Fin n =>
        state.matrix[k][k] * (hinv.coeff i)[a] -
          state.matrix[i][k] * (hinv.coeff k)[a]) =
        Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot := by
    apply Vector.ext
    intro a ha
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    exact hq.coeff_num_eq_mul ⟨a, ha⟩
  rw [h_q_eq_num]
  rw [dot_rowCombination_mul_right_int b hq.q state.prevPivot (b.row j)]
  exact Int.mul_comm _ _

/-- Row-vector consumer for an initial no-pivot Gram pass.  A single supported
integer row combination represents the active row `i` against every original
input row, so downstream singular-column arguments do not need to inspect
`BareissGramRowInvariant` or supply the generic regular-branch row-entry
equation. -/
private theorem noPivotLoop_initial_gram_exists_rowVec
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.rowCombination b c) ∧
        ∀ j : Fin n,
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
            Matrix.dot v (b.row j) := by
  let hinv :=
    bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  refine ⟨Matrix.rowCombination b (hinv.coeff i), ?_, ?_⟩
  · exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩
  · intro j
    exact hinv.entry_eq_dot i j hi

/-- `int_mul_self_nonneg`: the square `x * x` of an integer is nonnegative,
the base nonnegativity fact for the integer-vector self-dot bounds below. -/
private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using
    (Lean.Grind.OrderedRing.sq_nonneg (a := x))

/-- `int_mul_self_eq_zero_of_nonpos`: an integer whose square is nonpositive is
zero, the per-component step turning a vanishing self-dot into a zero entry. -/
private theorem int_mul_self_eq_zero_of_nonpos (x : Int) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := int_mul_self_nonneg x
  have hsquare : x * x = 0 := Int.le_antisymm h hnonneg
  rcases Int.mul_eq_zero.mp hsquare with h0 | h0 <;> exact h0

/-- `foldl_int_dot_self_start_le`: the running self-dot fold over `xs` never
drops below its nonnegative starting accumulator, since each added square is
nonnegative; the monotonicity used to pin the accumulator at zero. -/
private theorem foldl_int_dot_self_start_le (xs : List (Fin m)) (v : Vector Int m)
    (acc : Int) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := int_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Int.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

/-- `foldl_int_dot_self_eq_zero_of_mem`: if the self-dot fold over `xs` from a
nonnegative accumulator vanishes, then every entry indexed by `xs` is zero,
the per-index extraction behind finite-dimensional positive-definiteness. -/
private theorem foldl_int_dot_self_eq_zero_of_mem (xs : List (Fin m))
    (v : Vector Int m) (acc : Int) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := int_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero : acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          foldl_int_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply int_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

/-- `int_dot_self_eq_zero_get`: from a vanishing self-dot `Matrix.dot v v = 0`
each component `v[i]` is zero, specialising the fold lemma to the full index
list and the running form of `Matrix.dot`. -/
private theorem int_dot_self_eq_zero_get (v : Vector Int m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by simp
  exact foldl_int_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

/-- If `v : Vector Int m` has zero self-dot product, then any other integer
vector dots it to zero from the left as well. -/
private theorem int_dot_eq_zero_of_dot_self_zero_left (u v : Vector Int m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot v u = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [int_dot_self_eq_zero_get v hzero i]
      have hzero_mul : (0 : Int) * u[i] = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih

/-- `foldl_dot_comm_int_local`: folding `u[i] * v[i]` over `xs` equals folding
`v[i] * u[i]` from an equal starting accumulator, the fold-level symmetry
underlying commutativity of the integer dot product. -/
private theorem foldl_dot_comm_int_local {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. (Local form for use
inside this file before the existing `dot_comm_int` declaration.) -/
private theorem int_dot_comm_local {n' : Nat} (u v : Vector Int n') :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_int_local (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Pointwise function equality for foldl-style sums lifts to a foldl equality. -/
private theorem foldl_add_pointwise_eq_int {α : Type v}
    (xs : List α) (f g : α → Int) (acc : Int)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

/-- Entry-level formula for `rowCombination` over integers: the `j`th entry is
the sum over `k` of `b[k][j] * c[k]`. -/
private theorem rowCombination_getElem_int
    {n m : Nat} (b : Matrix Int n m) (c : Vector Int n) (j : Fin m) :
    (Matrix.rowCombination b c)[j] =
      (List.finRange n).foldl (fun acc k => acc + b[k][j] * c[k]) 0 := by
  show (Matrix.transpose b * c)[j] = _
  rw [Matrix.mulVec_getElem]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_add_pointwise_eq_int
  intro k _hk
  simp [Matrix.transpose, Matrix.col, Matrix.row]

/-- Distribute a constant `x : Int` through a foldl-style sum body. -/
private theorem foldl_mul_distrib_int {α : Type v}
    (xs : List α) (f : α → Int) (x acc : Int) :
    x * xs.foldl (fun acc y => acc + f y) acc =
      xs.foldl (fun acc y => acc + x * f y) (x * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + f y)]
      have : x * (acc + f y) = x * acc + x * f y := by grind
      rw [this]

/-- Expansion of the dot product against `rowCombination` over integers: the
second argument's row combination distributes outside the sum, giving the
Σ-over-rows form. Proved via the `Hex.Matrix.foldl_det_sum_swap` Fubini
identity. -/
private theorem dot_rowCombination_right_eq
    {n m : Nat} (b : Matrix Int n m) (u : Vector Int m) (c : Vector Int n) :
    Matrix.dot u (Matrix.rowCombination b c) =
      (List.finRange n).foldl
        (fun acc k => acc + c[k] * Matrix.dot u (b.row k)) 0 := by
  -- Step 1: rewrite each (rowComb b c)[j] entry using rowCombination_getElem_int.
  have h_lhs :
      Matrix.dot u (Matrix.rowCombination b c) =
        (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    rw [rowCombination_getElem_int (b := b) (c := c) j]
  rw [h_lhs]
  -- Step 2: distribute u[j] over the inner sum so the body has shape (acc + f j k).
  have h_distrib :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 =
        (List.finRange m).foldl
          (fun accj j => accj +
            (List.finRange n).foldl
              (fun acck k => acck + u[j] * (b[k][j] * c[k])) 0) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have h_mul := foldl_mul_distrib_int (List.finRange n)
      (fun k : Fin n => b[k][j] * c[k]) u[j] 0
    have h_zero : u[j] * (0 : Int) = 0 := by grind
    rw [h_zero] at h_mul
    exact h_mul
  rw [h_distrib]
  -- Step 3: apply Fubini sum-swap.
  have h_swap :=
    Matrix.foldl_det_sum_swap (R := Int)
      (xs := List.finRange m) (ys := List.finRange n)
      (fun (j : Fin m) (k : Fin n) => u[j] * (b[k][j] * c[k]))
  rw [h_swap]
  -- Step 4: reshape each inner sum to match c[k] * dot u (b.row k).
  apply foldl_add_pointwise_eq_int
  intro k _hk
  -- We want:
  --   (List.finRange m).foldl (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0
  --     = c[k] * Matrix.dot u (b.row k)
  -- Rearrange body so c[k] is the multiplier: u[j] * (b[k][j] * c[k])
  --     = c[k] * (u[j] * b[k][j]).
  have h_body :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0 =
        (List.finRange m).foldl
          (fun accj j => accj + c[k] * (u[j] * b[k][j])) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have : u[j] * (b[k][j] * c[k]) = c[k] * (u[j] * b[k][j]) := by grind
    exact this
  rw [h_body]
  -- Pull c[k] out of the foldl using foldl_mul_distrib_int (in reverse).
  have h_pull := foldl_mul_distrib_int (List.finRange m)
    (fun j : Fin m => u[j] * b[k][j]) c[k] 0
  have h_zero : c[k] * (0 : Int) = 0 := by grind
  rw [h_zero] at h_pull
  rw [← h_pull]
  -- Goal: c[k] * (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0
  --      = c[k] * Matrix.dot u (b.row k)
  -- Rewrite Matrix.dot definitionally to the foldl form using row entry equality.
  have h_dot_eq :
      Matrix.dot u (b.row k) =
        (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    simp [Matrix.row]
  rw [h_dot_eq]

/-- A foldl-style sum whose every term is zero starting from a zero accumulator
collapses to zero. -/
private theorem foldl_add_zero {α : Type v}
    (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) (0 : Int) = 0 := by
  have h_aux : ∀ (xs : List α) (acc : Int),
      (∀ x ∈ xs, f x = 0) →
        xs.foldl (fun acc x => acc + f x) acc = acc := by
    intro xs
    induction xs with
    | nil => intros acc _h; rfl
    | cons y rest ih =>
        intros acc h_terms
        simp only [List.foldl_cons]
        have hy : f y = 0 := h_terms y (by simp)
        have hxs : ∀ x ∈ rest, f x = 0 :=
          fun x hx => h_terms x (List.mem_cons_of_mem _ hx)
        rw [hy]
        have h_add : acc + (0 : Int) = acc := by grind
        rw [h_add]
        exact ih (acc) hxs
  exact h_aux xs 0 h

/-- Gram zero-pivot column suffix: if the no-pivot Bareiss pass over the Gram
matrix runs `s` steps without recording a singular step but the pivot entry
`matrix[s][s]` is zero, then every later row's entry in column `s` is zero
too. This is the `h_column_zero` premise consumed by
`noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero` to discharge the
executable `findPivot? = none` form needed by the row-pivoted Bareiss loop on
the Gram trajectory.

The argument: by the closed row-vector consumer, the represented pivot row has
integer support on indices `≤ s` and inner product zero against `b.row k` for
every `k.val ≤ s` (those matrix entries are either the zero pivot itself or
zeros left by earlier regular elimination steps). Linearity of dot against
`rowCombination` over the supported indices then gives `Matrix.dot v v = 0`,
and integer positive definiteness forces every dot against `v` to be zero.
Trailing-block symmetry transports
`state.matrix[sFin][i] = Matrix.dot v (b.row i) = 0` across the diagonal to
`state.matrix[i][sFin] = 0`. -/
private theorem leadingPrefix_gram_zero_pivot_column_zero
    {n m : Nat} (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hquot : StepWitness b)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_zero :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    ∀ i : Fin n, s + 1 ≤ i.val →
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0 := by
  intro i hi
  let sFin : Fin n := ⟨s, Nat.lt_of_succ_lt hs⟩
  -- Final state of the loop and its `step = s` alignment.
  have h_step :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s :=
    noPivotLoop_initial_gram_step_eq b s hs h_prefix_none
  have h_state_step_le_sFin :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ sFin.val := by
    rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- The row-vector consumer aligns `matrix[sFin][j]` with
  -- `Matrix.dot v (b.row j)` for all columns `j`.
  obtain ⟨v, ⟨c, h_coeff_supp_above, hv_def⟩, h_dot_eq_matrix⟩ :=
    noPivotLoop_initial_gram_exists_rowVec b s hquot sFin h_state_step_le_sFin
  -- The represented row is orthogonal to `b.row k` for every `k.val ≤ s`:
  -- on `k.val = s`, the hypothesis `h_zero` gives a zero pivot dot, and on
  -- `k.val < s` the column was cleared by an earlier regular Bareiss step.
  have h_dot_zero_le : ∀ k : Fin n, k.val ≤ s →
      Matrix.dot v (b.row k) = 0 := by
    intro k hks
    rw [← h_dot_eq_matrix k]
    by_cases hk_eq : k.val = s
    · have h_k_eq_sFin : k = sFin := Fin.ext hk_eq
      rw [h_k_eq_sFin]
      exact h_zero
    · -- k.val < s, use column-zero helper at fuel = s, k as kFin, sFin as i.
      have hk_lt : k.val < s := Nat.lt_of_le_of_ne hks hk_eq
      have h_init_step_le :
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ k.val := by
        show 0 ≤ k.val
        exact Nat.zero_le _
      have h_k_lt_result :
          k.val < (Matrix.noPivotLoop s
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [h_step]
        exact hk_lt
      have h_k_lt_sFin : k.val < sFin.val := hk_lt
      exact noPivotLoop_matrix_processed_col_eq_zero s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
        k.val h_init_step_le h_k_lt_result k rfl sFin h_k_lt_sFin
  -- `Matrix.dot v v = 0`: every term in the rowCombination expansion is zero.
  have h_dot_self_zero : Matrix.dot v v = 0 := by
    have h_expand_aux :
        Matrix.dot v (Matrix.rowCombination b c) =
          (List.finRange n).foldl
            (fun acc k => acc + c[k] * Matrix.dot v (b.row k))
            0 :=
      dot_rowCombination_right_eq b v c
    rw [← hv_def] at h_expand_aux
    rw [h_expand_aux]
    apply foldl_add_zero
    intro k _hk
    by_cases hks : k.val ≤ s
    · -- second factor is zero
      rw [h_dot_zero_le k hks]
      grind
    · -- first factor is zero
      have hk_gt : sFin.val < k.val := by show s < k.val; omega
      rw [h_coeff_supp_above k hk_gt]
      grind
  -- Transport across symmetry: `matrix[i][sFin] = matrix[sFin][i]`.
  have h_init_sym :
      ∀ a c : Fin n,
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ a.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ c.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[a][c] =
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[c][a] := by
    intros a c _ha _hc
    show (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a]
    rw [Matrix.gramMatrix_getElem, Matrix.gramMatrix_getElem]
    exact int_dot_comm_local (Matrix.row b a) (Matrix.row b c)
  have h_symm :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][sFin] =
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[sFin][i] := by
    apply noPivotLoop_matrix_symm_preserve s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init_sym i sFin
    · rw [h_step]; omega
    · rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- Now matrix[sFin][i] = dot v (b.row i) = 0 via integer positive definiteness.
  rw [h_symm, h_dot_eq_matrix i]
  exact int_dot_eq_zero_of_dot_self_zero_left (b.row i) v h_dot_self_zero

/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. -/
private theorem matrix_diag_at_fin_eq {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl

/-- If the `a`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. -/
private theorem noPivotLoop_extends_singularStep
    {n : Nat} (state : Matrix.BareissState n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a : (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  have hDone : (Matrix.noPivotLoop a state).step + 1 < n := by
    rw [h_step_a]; exact hk
  have hp_zero :
      (Matrix.noPivotLoop a state).matrix[
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (matrix_diag_at_fin_eq (Matrix.noPivotLoop a state).matrix h_fin).trans h_zero_a
  have h_sing_step : (Matrix.noPivotLoop a state).singularStep =
      some (Matrix.noPivotLoop a state).step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b
    (Matrix.noPivotLoop a state) hDone hp_zero h_sing_step

/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. -/
private theorem noPivotLoop_prefix_state_at_singular
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  have h_init_sing : (Matrix.noPivotInitialState M).singularStep = none := rfl
  have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel
      (Matrix.noPivotInitialState M) h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  rcases noPivotLoop_singular_inv (n := n) s
      (Matrix.noPivotInitialState M) h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · have hS_step : (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s := by
      have h_room :
          (Matrix.noPivotInitialState M).step + s + 1 ≤ n := by
        rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s (Matrix.noPivotInitialState M) h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    rcases noPivotLoop_singular_inv (n := n) fuel
        (Matrix.noPivotInitialState M) h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq :
          Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) := by
        congr 1; omega
      have h_split :
          Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) := by
        rw [← h_full_eq,
          Matrix.noPivotLoop_add s (fuel - s) (Matrix.noPivotInitialState M)]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))
          (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step]; exact Nat.le_refl _)
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
            (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (matrix_diag_at_fin_eq
            (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix h_fin).symm.trans
          h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s
        (Matrix.noPivotInitialState M) h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
          Matrix.noPivotLoop s (Matrix.noPivotInitialState M) :=
      noPivotLoop_extends_singularStep (Matrix.noPivotInitialState M) s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega

/-- If the row-pivoted Bareiss loop is in a state where, after `a` regular
no-pivot iterations, the next pivot is zero and the column has no replacement,
the loop records the resulting step as singular regardless of any remaining
fuel beyond the triggering iteration. The partial-pass result is passed
explicitly as `result` to keep Fin-index proof terms uniform across the
induction. -/
private theorem pivotLoop_singularStep_some
    {n : Nat} :
    ∀ (a : Nat) (fuel : Nat) (state : Matrix.BareissState n)
      (result : Matrix.BareissState n)
      (_h_partial : Matrix.noPivotLoop a state = result),
      state.singularStep = none →
      a + 1 ≤ fuel →
      result.singularStep = none →
      (h_step_lt : result.step + 1 < n) →
      result.matrix[(⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)][
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)] = 0 →
      Matrix.findPivot? result.matrix
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n) (result.step + 1) = none →
      (Matrix.pivotLoop fuel state).singularStep = some result.step := by
  intro a
  induction a with
  | zero =>
      intro fuel state result h_partial _h_init_sing hfuel _h_part_none hStepLt hp_zero
          h_find_none
      -- noPivotLoop 0 state = state.
      have h_state_eq : state = result := by
        rw [show state = Matrix.noPivotLoop 0 state from rfl, h_partial]
      subst h_state_eq
      rcases fuel with _ | fuel'
      · omega
      exact (Matrix.pivotLoop_singular_branch_no_pivot fuel' state hStepLt hp_zero h_find_none
        ▸ rfl)
  | succ a' ih =>
      intro fuel state result h_partial h_init_sing hfuel h_part_none hStepLt hp_zero
          h_find_none
      have hDone_state : state.step + 1 < n := by
        have hmono := noPivotLoop_step_monotone (a' + 1) state
        rw [h_partial] at hmono
        omega
      by_cases hp0_state : state.matrix[state.step][state.step] = 0
      · -- Singular first iteration contradicts result.singularStep = none.
        exfalso
        have h_sing_branch :
            Matrix.noPivotLoop (a' + 1) state =
              { state with singularStep := some state.step } :=
          Matrix.noPivotLoop_singular_branch a' state hDone_state hp0_state
        rw [h_sing_branch] at h_partial
        rw [← h_partial] at h_part_none
        simp at h_part_none
      · -- Regular first iteration: recurse on the updated state.
        have h_unfold_noPiv : Matrix.noPivotLoop (a' + 1) state =
            Matrix.noPivotLoop a'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.noPivotLoop_regular_branch a' state hDone_state hp0_state
        rcases fuel with _ | fuel'
        · omega
        have h_fuel' : a' + 1 ≤ fuel' := by omega
        have h_unfold_piv : Matrix.pivotLoop (fuel' + 1) state =
            Matrix.pivotLoop fuel'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.pivotLoop_regular_branch_no_swap fuel' state hDone_state hp0_state
        rw [h_unfold_piv]
        have h_next_partial :
            Matrix.noPivotLoop a'
              ({ step := state.step + 1
                 matrix := Matrix.stepMatrix state.matrix state.step
                   state.matrix[state.step][state.step] state.prevPivot
                 prevPivot := state.matrix[state.step][state.step]
                 rowSwaps := state.rowSwaps
                 singularStep := none } : Matrix.BareissState n) = result := by
          rw [← h_unfold_noPiv]; exact h_partial
        exact ih fuel'
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          result h_next_partial rfl h_fuel' h_part_none hStepLt hp_zero h_find_none

/-- Singular branch of the Gram leading-prefix Bareiss identification: if the
no-pivot Bareiss pass over the full Gram matrix records a singular step at index
`s` strictly before slot `r + 1`, the public row-pivoted Bareiss determinant of
the `(r + 1)` leading Gram prefix is `Nat.zero`. The proof translates the
column-zero suffix from the closed row invariant on the full trajectory to the
leading prefix via the no-pivot sync lemma, then derives `findPivot? = none` on
the prefix, so the row-pivoted Bareiss loop records the same singular step. -/
private theorem leadingPrefix_gram_bareiss_toNat_eq_zero
    {n m : Nat} (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (hquot : StepWitness b)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    (Matrix.bareiss
      (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr))).toNat = 0 := by
  let GM := Matrix.gramMatrix b
  let initGM := Matrix.noPivotInitialState GM
  let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
  let LP := Matrix.leadingPrefix GM (r + 1) hK
  let initLP := Matrix.noPivotInitialState LP
  -- Step 1: s < r via noPivotLoop_singularStep_lt.
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r initGM rfl s h_sing
    change s < initGM.step + r at h
    have : initGM.step = 0 := rfl
    omega
  have hs1n : s + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hsr) hr
  have hsn : s < n := Nat.lt_of_succ_lt hs1n
  -- Step 2: extract partial state at s iterations.
  have hsucc_n : s + 1 ≤ n := Nat.le_of_lt hs1n
  obtain ⟨h_full_none, h_full_step, h_full_zero⟩ :=
    noPivotLoop_prefix_state_at_singular GM r s hsucc_n h_sing
  -- Step 3: column-zero on FULL via leadingPrefix_gram_zero_pivot_column_zero.
  have h_full_col_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s initGM).matrix[i][(⟨s, hsn⟩ : Fin n)] = 0 :=
    leadingPrefix_gram_zero_pivot_column_zero
      (b := b) s hs1n hquot h_full_none h_full_zero
  -- Step 4: sync — leadingPrefix (noPivotLoop s initGM).matrix (r+1) = (noPivotLoop s initLP).matrix.
  have h_sync :=
    noPivotLoop_sync_leadingPrefix_aux (n := n) (K := r + 1) hK s
      initGM initLP rfl rfl rfl rfl
      (by
        show Matrix.leadingPrefix initGM.matrix (r + 1) hK = initLP.matrix
        rfl)
      (show s + initGM.step < r + 1 by
        change s + 0 < r + 1; omega)
  obtain ⟨h_step_sync, _h_prev_sync, _h_rows_sync, h_sing_sync, h_mat_sync⟩ := h_sync
  -- Useful Fin bound.
  have hs_lt_r1 : s < r + 1 := Nat.lt_succ_of_lt hsr
  -- Step 5: translate column-zero to LP.
  have h_LP_col_zero :
      ∀ i' : Fin (r + 1), s + 1 ≤ i'.val →
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    intro i' hi'
    let iN : Fin n := ⟨i'.val, Nat.lt_of_lt_of_le i'.isLt hK⟩
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK i'
      (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have hi_iN : s + 1 ≤ iN.val := hi'
    have h_col_zero_iN := h_full_col_zero iN hi_iN
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[iN][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[iN][(⟨s, hsn⟩ : Fin n)] :=
      congrArg (fun (j : Fin n) => (Matrix.noPivotLoop s initGM).matrix[iN][j])
        (Fin.ext (rfl : (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n).val =
                        (⟨s, hsn⟩ : Fin n).val))
    exact h_entry_eq.trans h_col_zero_iN
  -- Step 6: findPivot? = none on LP.
  have h_LP_step : (Matrix.noPivotLoop s initLP).step = s := by
    rw [← h_step_sync]; exact h_full_step
  have h_LP_sing : (Matrix.noPivotLoop s initLP).singularStep = none := by
    rw [← h_sing_sync]; exact h_full_none
  have h_LP_zero_diag :
      (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
        (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK
      (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have h_idx_eq :
        (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n) =
          (⟨s, hsn⟩ : Fin n) := Fin.ext rfl
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
      matrix_diag_at_fin_eq _ h_idx_eq
    exact h_entry_eq.trans h_full_zero
  have h_LP_find_none :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (s + 1) = none :=
    Matrix.findPivot?_eq_none_of_zero _ _ _ h_LP_col_zero
  -- Step 7: pivotLoop on LP records singular at s.
  have h_LP_step_lt : (Matrix.noPivotLoop s initLP).step + 1 < r + 1 := by
    rw [h_LP_step]; omega
  have h_idx_at_LP_step :
      (⟨(Matrix.noPivotLoop s initLP).step,
        Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1)) =
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) :=
    Fin.ext h_LP_step
  have h_LP_zero_at_result :
      (Matrix.noPivotLoop s initLP).matrix[
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))][
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))] = 0 :=
    (matrix_diag_at_fin_eq (n := r + 1)
      (Matrix.noPivotLoop s initLP).matrix h_idx_at_LP_step).trans h_LP_zero_diag
  have h_LP_find_at_result :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
        ((Matrix.noPivotLoop s initLP).step + 1) = none := by
    have h_step_plus_eq : (Matrix.noPivotLoop s initLP).step + 1 = s + 1 := by
      rw [h_LP_step]
    have h_step1 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨(Matrix.noPivotLoop s initLP).step,
              Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) :=
      congrArg
        (fun (i : Fin (r + 1)) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix i
            ((Matrix.noPivotLoop s initLP).step + 1))
        h_idx_at_LP_step
    have h_step2 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            (s + 1) :=
      congrArg
        (fun (st : Nat) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1)) st)
        h_step_plus_eq
    exact (h_step1.trans h_step2).trans h_LP_find_none
  have h_pivot_sing : (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step :=
    pivotLoop_singularStep_some
      s (r + 1) initLP (Matrix.noPivotLoop s initLP)
      rfl rfl (by omega) h_LP_sing h_LP_step_lt
      h_LP_zero_at_result h_LP_find_at_result
  -- Step 8: bareiss LP = 0 via singular branch of BareissData.det.
  have h_bareissData_sing :
      (Matrix.bareissData LP).singularStep =
        some (Matrix.noPivotLoop s initLP).step := by
    rw [Matrix.bareissData_eq_finish_pivotLoop]
    show (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step
    exact h_pivot_sing
  have h_bareiss_zero : Matrix.bareiss LP = 0 := by
    rw [Matrix.bareiss_eq_bareissData_det]
    unfold Matrix.BareissData.det
    rw [h_bareissData_sing]
  show (Matrix.bareiss LP).toNat = 0
  rw [h_bareiss_zero]
  rfl

/-- If the array loop's `state.step` is past the matrix extent, one outer
iteration returns the input state unchanged. -/
private theorem scaledCoeffArrayLoop_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n (fuel + 1) state = state := by
  simp [scaledCoeffArrayLoop, hDone]

/-- The array loop is idempotent once `state.step ≥ n`. -/
private theorem scaledCoeffArrayLoop_id_at_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ f => exact scaledCoeffArrayLoop_done f state hDone

/-- Singular branch of one array-loop iteration: a zero pivot strictly before
the last column halts the loop, writing the scaled column at the current step
but leaving the matrix and step untouched. -/
private theorem scaledCoeffArrayLoop_singular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step = 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- Last-column branch of one array-loop iteration: when `state.step = n - 1`,
the loop writes the final scaled column and advances `step` to `n` without
applying a Bareiss step. -/
private theorem scaledCoeffArrayLoop_last_step (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : ¬ state.step + 1 < n) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with
        step := state.step + 1
        coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext]

/-- Regular branch of one array-loop iteration: a nonzero pivot strictly before
the last column applies one row-mutating Bareiss update, advances
`step`, records the new `prevPivot`, and recurses on the remaining fuel. -/
private theorem scaledCoeffArrayLoop_regular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- The matrix-side view of a row-storage entry: `getArrayEntry` on the array
matches the matrix-level `[i][j]` lookup under `rowsToMatrix`. -/
private theorem getArrayEntry_eq_rowsToMatrix
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  simp [rowsToMatrix, Matrix.ofFn]

/-- If the array loop is currently at column `j`, the coefficient entry below
the diagonal in that column records the pre-elimination matrix entry for that
same step. In the regular branch, later recursive iterations preserve column
`j` because the next state has advanced past it. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_current_col_written
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hstep : state.step = j) (hji : j < i) (hin : i < n)
    (h_coeffs_size : state.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i j =
      getArrayEntry state.matrix i j := by
  have hArrayStep : state.step < n := by omega
  have hrow : i < state.coeffs.size := by
    rw [h_coeffs_size]
    exact hin
  have hcol : j < state.coeffs[i]!.size := by
    rw [h_coeffs_rows_size i hin]
    exact Nat.lt_trans hji hin
  by_cases hNext : state.step + 1 < n
  · by_cases hp : getArrayEntry state.matrix state.step state.step = 0
    · rw [scaledCoeffArrayLoop_singular_branch fuel state hArrayStep hNext hp]
      rw [hstep]
      exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
        hji hin hrow hcol
    · rw [scaledCoeffArrayLoop_regular_branch fuel state hArrayStep hNext hp]
      let next : ScaledCoeffArrayState :=
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step }
      change getArrayEntry (scaledCoeffArrayLoop n fuel next).coeffs i j =
        getArrayEntry state.matrix i j
      rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step]
      · show getArrayEntry (writeScaledColumn state.coeffs state.matrix n state.step) i j =
          getArrayEntry state.matrix i j
        rw [hstep]
        exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
          hji hin hrow hcol
      · show j < next.step
        simp [next, hstep]
  · rw [scaledCoeffArrayLoop_last_step fuel state hArrayStep hNext]
    rw [hstep]
    exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
      hji hin hrow hcol

/-- Size preservation: the inner `coeffs` array of the scaled-coefficient
array loop keeps its outer-array length. -/
private theorem scaledCoeffArrayLoop_coeffs_size
    (fuel : Nat) (state : ScaledCoeffArrayState) :
    (scaledCoeffArrayLoop n fuel state).coeffs.size = state.coeffs.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold scaledCoeffArrayLoop
      by_cases h_step : state.step < n
      · simp only [h_step, ↓reduceIte]
        by_cases h_next : state.step + 1 < n
        · simp only [h_next, ↓reduceIte]
          by_cases h_pivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [h_pivot, ↓reduceIte]
            exact writeScaledColumn_size _ _ _ _
          · simp only [h_pivot, ↓reduceIte]
            rw [ih]
            exact writeScaledColumn_size _ _ _ _
        · simp only [h_next, ↓reduceIte]
          exact writeScaledColumn_size _ _ _ _
      · simp only [h_step, ↓reduceIte]

end GramSchmidt.Int
end Hex
