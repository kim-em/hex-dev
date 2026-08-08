/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Block
public import HexMatrix.Pad
public import HexMatrix.Region
public import HexMatrix.Winograd

public section

/-!
Strassen-Winograd matrix multiplication.

`mulStrassen` is the recursive, ring-level multiplication entry point. It computes a
2×2 block product with **seven** recursive block multiplications (`P₁…P₇`) and
**fifteen** block additions/subtractions (`S₁…S₄`, `T₁…T₄`, `U₁…U₇`), following
Winograd's memory-efficient schedule, giving `Θ(n^{log₂ 7})` coefficient
multiplications.

The cutoff below which the recursion falls back to a base kernel, and the base
kernel itself, live in the data-only `StrassenConfig`. A config is `Valid` when
its base kernel agrees with the reference `mul`; the default config
`strassenDefault` uses the naive `mulImpl` and `strassenDefault_valid` proves it
valid. The correctness theorem `mulStrassen_eq_mul` proves the whole recursion
equal to `mul` for every valid config, composing the three wave-1 lemmas: the
Winograd schedule identity (`Winograd.c11…c22`), the block decomposition
(`fromBlocks_mul_fromBlocks`), and the padding lemma
(`takeCols_takeRows_mul_pad`).

`mulStrassen` needs subtraction on `R` (Winograd subtracts blocks), so it is
*defined* over `[Mul R] [Add R] [Sub R] [OfNat R 0]` and *proved* correct over
`[Lean.Grind.Ring R]`, which additionally supplies the ring laws. Because `mul`
lacks `[Sub R]`, `mulStrassen` cannot be a type-preserving `@[csimp]` replacement
of `mul`; it is a separate entry point that callers opt into.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-! # View-to-matrix abstraction

The Strassen recursion runs over `Submatrix` views (`HexMatrix/Submatrix.lean`).
These lemmas relate a view's `toMatrix` materialization to the corresponding
`Matrix`-level `pad`/`toBlocks` operation, so the view recursion reduces to the
existing `mulStrassen_eq_mul` decomposition. -/

/-- Materializing a widened view is `Matrix.pad` of the materialized source. -/
theorem toMatrix_pad_view [OfNat R 0] (A : Submatrix R n m) (n' m' : Nat)
    (hn : n ≤ n') (hm : m ≤ m') :
    (A.pad n' m' hn hm).toMatrix = pad A.toMatrix n' m' := by
  apply ext_getElem
  intro i j
  rw [Submatrix.getElem_toMatrix, Submatrix.entry_pad, getElem_pad]
  by_cases h : i.val < n ∧ j.val < m
  · rw [dif_pos h, dif_pos h, getElem_pair_eq_nested, Submatrix.getElem_toMatrix]
  · rw [dif_neg h, dif_neg h]

/-- Materializing the top-left quadrant view is `Matrix.toBlocks₁₁` of the
materialized parent. -/
theorem toMatrix_toBlocks₁₁ [OfNat R 0] {h w : Nat} (A : Submatrix R (h + h) (w + w)) :
    (Submatrix.toBlocks₁₁ A).toMatrix = toBlocks₁₁ A.toMatrix := by
  apply ext_getElem
  intro i j
  rw [Submatrix.getElem_toMatrix, getElem_toBlocks₁₁, Submatrix.getElem_toMatrix]
  unfold Submatrix.toBlocks₁₁
  unfold Submatrix.entry
  simp only [Fin.val_castAdd]
  have hi : A.r0 + i.val < A.r0 + h := by omega
  have hj : A.c0 + j.val < A.c0 + w := by omega
  simp only [Nat.lt_min, hi, hj, and_true]

/-- Materializing the top-right quadrant view is `Matrix.toBlocks₁₂` of the parent. -/
theorem toMatrix_toBlocks₁₂ [OfNat R 0] {h w : Nat} (A : Submatrix R (h + h) (w + w)) :
    (Submatrix.toBlocks₁₂ A).toMatrix = toBlocks₁₂ A.toMatrix := by
  apply ext_getElem
  intro i j
  rw [Submatrix.getElem_toMatrix, getElem_toBlocks₁₂, Submatrix.getElem_toMatrix,
    Submatrix.entry, Submatrix.entry]
  simp only [Submatrix.toBlocks₁₂, Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc]
  all_goals (have hi := i.isLt; have hj := j.isLt; split <;> split <;> (first | rfl | (exfalso; omega)))

/-- Materializing the bottom-left quadrant view is `Matrix.toBlocks₂₁` of the parent. -/
theorem toMatrix_toBlocks₂₁ [OfNat R 0] {h w : Nat} (A : Submatrix R (h + h) (w + w)) :
    (Submatrix.toBlocks₂₁ A).toMatrix = toBlocks₂₁ A.toMatrix := by
  apply ext_getElem
  intro i j
  rw [Submatrix.getElem_toMatrix, getElem_toBlocks₂₁, Submatrix.getElem_toMatrix,
    Submatrix.entry, Submatrix.entry]
  simp only [Submatrix.toBlocks₂₁, Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc]
  all_goals (have hi := i.isLt; have hj := j.isLt; split <;> split <;> (first | rfl | (exfalso; omega)))

/-- Materializing the bottom-right quadrant view is `Matrix.toBlocks₂₂` of the parent. -/
theorem toMatrix_toBlocks₂₂ [OfNat R 0] {h w : Nat} (A : Submatrix R (h + h) (w + w)) :
    (Submatrix.toBlocks₂₂ A).toMatrix = toBlocks₂₂ A.toMatrix := by
  apply ext_getElem
  intro i j
  rw [Submatrix.getElem_toMatrix, getElem_toBlocks₂₂, Submatrix.getElem_toMatrix,
    Submatrix.entry, Submatrix.entry]
  simp only [Submatrix.toBlocks₂₂, Fin.val_natAdd, Nat.add_assoc]
  all_goals (have hi := i.isLt; have hj := j.isLt; split <;> split <;> (first | rfl | (exfalso; omega)))

/-- Configuration for `mulStrassen`: the recursion `cutoff` below which a block is
handed to the base kernel, and the pluggable `baseMul` base kernel itself. Data
only — `baseMul` is a bare function and the record carries no algebraic instances,
so a caller can supply a hand-tuned small-matrix kernel without touching the
recursion. -/
structure StrassenConfig (R : Type u) where
  /-- The recursion stops splitting and calls `baseMul` once any of the three
  dimensions is below this cutoff. -/
  cutoff : Nat
  /-- The base kernel run on small blocks. Polymorphic over the dimensions because
  the recursion reaches its base case at a range of (possibly rectangular) shapes. -/
  baseMul : {n m k : Nat} → Matrix R n m → Matrix R m k → Matrix R n k

/-- A configuration is **valid** when its base kernel agrees with the reference
`mul` on every input. The correctness theorem `mulStrassen_eq_mul` is stated under
this hypothesis, keeping the proof out of the `StrassenConfig` data record. -/
@[expose]
def StrassenConfig.Valid [Mul R] [Add R] [OfNat R 0] (cfg : StrassenConfig R) : Prop :=
  ∀ {n m k} (X : Matrix R n m) (Y : Matrix R m k), cfg.baseMul X Y = mul X Y

/-- The default configuration: naive `mulImpl` as the base kernel and a **measured**
cutoff of `96`.

Measured by the Strassen bench driver (`bench/HexMatrix/Bench.lean`) on `Int`
coefficients with GMP arithmetic, sweeping the cutoff `τ` against dimension `n`
on host `chungus2` (AMD EPYC 9455), Lean toolchain `4.32.0-rc1`. An extra
Strassen level below a `64×64` block loses to the naive base kernel, while a
`128×128` block splits profitably. Any cutoff in `(64, 128]` therefore recurses
down to a `64×64` naive leaf; that leaf class wins from the first splitting
dimension (`n = 128`) and stays within ~4% of the `128×128`-leaf class at
`n = 512` (which edges ahead there), so `96` is shipped as its representative,
extending Strassen to non-power-of-two blocks in `[96, 128)` as well. The value
has been re-measured twice: on the flat row-major backing with materialized
quadrants and again on the
`Submatrix`-view recursion, both within noise of the original sweep (the
quadrant copies the views remove are `O(n²)` per level against the `O(n^2.81)`
multiply work, so they never dominated at benched sizes) — the crossover
stayed put and `96` stands. -/
@[expose]
def strassenDefault [Mul R] [Add R] [OfNat R 0] : StrassenConfig R where
  cutoff := 96
  baseMul := mulImpl

/-- The default configuration is valid: its base kernel `mulImpl` equals `mul` by
`mul_eq_mulImpl`. -/
theorem strassenDefault_valid [Mul R] [Add R] [OfNat R 0] :
    (strassenDefault (R := R)).Valid := by
  intro n m k X Y
  show mulImpl X Y = mul X Y
  rw [mul_eq_mulImpl]

/-- The internal Strassen-Winograd recursion over copy-free `Submatrix` **views**.
Recurses on the runtime dimensions following the Winograd schedule.

Base case: when any of `n`, `m`, `k` is `≤ 1` or below `cfg.cutoff`, materialize
the current view blocks (`toMatrix`) and call `cfg.baseMul` — the only leaf
allocation. The `≤ 1` disjuncts are config-independent, so `cutoff = 0` cannot
defeat termination.

Recursive step: widen each operand view to even dimensions (`h + h`, `w + w`,
`d + d` with `h := (n+1)/2` etc.) — a zero-fill reshape with no copy — split into
2×2 quadrant **views** (offset arithmetic — small view records, no buffer copies),
materialize only the fifteen
`Sᵢ`/`Tᵢ`/`Uᵢ` operand sums and the seven recursive products, assemble with
`fromBlocks`, and crop back to `n × k`. Termination is well-founded on `n + m + k`:
the recursion fires only when `n, m, k ≥ 2`, and each halved dimension is then
strictly smaller. -/
@[expose]
def mulStrassenView {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n m k : Nat} (A : Submatrix R n m) (B : Submatrix R m k) :
    Matrix R n k :=
  if n ≤ 1 ∨ m ≤ 1 ∨ k ≤ 1 ∨ n < cfg.cutoff ∨ m < cfg.cutoff ∨ k < cfg.cutoff then
    cfg.baseMul A.toMatrix B.toMatrix
  else
    let h := (n + 1) / 2
    let w := (m + 1) / 2
    let d := (k + 1) / 2
    let Ap := A.pad (h + h) (w + w) (by omega) (by omega)
    let Bp := B.pad (w + w) (d + d) (by omega) (by omega)
    let A₁₁ := Ap.toBlocks₁₁
    let A₁₂ := Ap.toBlocks₁₂
    let A₂₁ := Ap.toBlocks₂₁
    let A₂₂ := Ap.toBlocks₂₂
    let B₁₁ := Bp.toBlocks₁₁
    let B₁₂ := Bp.toBlocks₁₂
    let B₂₁ := Bp.toBlocks₂₁
    let B₂₂ := Bp.toBlocks₂₂
    let S₁ := A₂₁.add A₂₂
    let S₂ := S₁.sub A₁₁
    let S₃ := A₁₁.sub A₂₁
    let S₄ := A₁₂.sub S₂
    let T₁ := B₁₂.sub B₁₁
    let T₂ := B₂₂.sub T₁
    let T₃ := B₂₂.sub B₁₂
    let T₄ := T₂.sub B₂₁
    let P₁ := mulStrassenView cfg A₁₁ B₁₁
    let P₂ := mulStrassenView cfg A₁₂ B₂₁
    let P₃ := mulStrassenView cfg S₄ B₂₂
    let P₄ := mulStrassenView cfg A₂₂ T₄
    let P₅ := mulStrassenView cfg S₁ T₁
    let P₆ := mulStrassenView cfg S₂ T₂
    let P₇ := mulStrassenView cfg S₃ T₃
    let U₁ := P₁ + P₂
    let U₂ := P₁ + P₆
    let U₃ := U₂ + P₇
    let U₄ := U₂ + P₅
    let U₅ := U₄ + P₃
    let U₆ := U₃ - P₄
    let U₇ := U₃ + P₅
    takeCols (takeRows (fromBlocks U₁ U₅ U₆ U₇) n (by omega)) k (by omega)
  termination_by n + m + k
  decreasing_by all_goals (simp_wf; omega)

/-! # Two-buffer square schedule -/

/-- Transport both matrix dimensions along equalities. -/
@[expose]
def castDims {R : Type u} {n m n' m' : Nat} (hn : n = n') (hm : m = m')
    (A : Matrix R n m) : Matrix R n' m' :=
  hn ▸ hm ▸ A

/-- `castDims hn hm` is injective. -/
private theorem castDims_inj {R : Type u} {n m n' m' : Nat} (hn : n = n') (hm : m = m')
    {A B : Matrix R n m} (h : castDims hn hm A = castDims hn hm B) : A = B := by
  subst n'
  subst m'
  exact h

/-- Transporting a materialized region changes only its index types. -/
private theorem castDims_toMatrix {R : Type u} {n m n' m' N M : Nat}
    (hn : n = n') (hm : m = m') (D : Region N M n m) (D' : Region N M n' m')
    (hr : D.r0 = D'.r0) (hc : D.c0 = D'.c0) (A : Matrix R N M) :
    castDims hn hm (D.toMatrix A) = D'.toMatrix A := by
  subst n'
  subst m'
  have hD : D = D' := by
    cases D with
    | mk dr dc drl dcl =>
      cases D' with
      | mk er ec erl ecl =>
        simp only at hr hc
        subst er
        subst ec
        rfl
  subst D'
  rfl

/-- Cropping a matrix to its full dimensions and transporting the result is the
original matrix. -/
private theorem castDims_crop {R : Type u} {n h : Nat} (hn : n = h + h)
    (A : Matrix R (h + h) (h + h)) :
    castDims hn hn
      (takeCols (takeRows A n (by omega)) n (by omega)) = A := by
  subst n
  apply Matrix.ext_getElem
  intro i j
  simp only [castDims, getElem_takeCols, getElem_takeRows]

/-- Write a square Strassen result into a backing-free region of one owned output
matrix.  Even recursive nodes use the Boyer–Dumas–Pernet–Zhou schedule: `X` and
`Y` are the only half-size matrix buffers, while products and `Uᵢ` values are
written directly into the four output quadrants.  Base and odd nodes retain the
reference view recursion as a shape-safe fallback. -/
@[expose]
def mulStrassenInto {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n N M : Nat} (A B : Submatrix R n n)
    (C : Matrix R N M) (D : Region N M n n) : Matrix R N M :=
  -- Keep the six repeated disjuncts: this is syntactically `mulStrassenView`'s
  -- `n = m = k` guard, which makes the equality proof reduce without algebra.
  if n ≤ 1 ∨ n ≤ 1 ∨ n ≤ 1 ∨ n < cfg.cutoff ∨ n < cfg.cutoff ∨ n < cfg.cutoff then
    let P := cfg.baseMul A.toMatrix B.toMatrix
    D.overwrite C fun i j => P[(i, j)]
  else
    let h := (n + 1) / 2
    if heven : n = h + h then
      let Ap := A.pad (h + h) (h + h) (by omega) (by omega)
      let Bp := B.pad (h + h) (h + h) (by omega) (by omega)
      let A₁₁ := Ap.toBlocks₁₁
      let A₁₂ := Ap.toBlocks₁₂
      let A₂₁ := Ap.toBlocks₂₁
      let A₂₂ := Ap.toBlocks₂₂
      let B₁₁ := Bp.toBlocks₁₁
      let B₁₂ := Bp.toBlocks₁₂
      let B₂₁ := Bp.toBlocks₂₁
      let B₂₂ := Bp.toBlocks₂₂
      let Dp : Region N M (h + h) (h + h) :=
        { r0 := D.r0, c0 := D.c0
          rows_le := by have := D.rows_le; omega
          cols_le := by have := D.cols_le; omega }
      let C₁₁ := Dp.toBlocks₁₁
      let C₁₂ := Dp.toBlocks₁₂
      let C₂₁ := Dp.toBlocks₂₁
      let C₂₂ := Dp.toBlocks₂₂
      have h₁₁₁₂ : Region.Disjoint C₁₁ C₁₂ := Region.disjoint₁₁₁₂ Dp
      have h₁₁₂₁ : Region.Disjoint C₁₁ C₂₁ := Region.disjoint₁₁₂₁ Dp
      have h₁₁₂₂ : Region.Disjoint C₁₁ C₂₂ := Region.disjoint₁₁₂₂ Dp
      have h₁₂₂₁ : Region.Disjoint C₁₂ C₂₁ := Region.disjoint₁₂₂₁ Dp
      have h₁₂₂₂ : Region.Disjoint C₁₂ C₂₂ := Region.disjoint₁₂₂₂ Dp
      have h₂₁₂₂ : Region.Disjoint C₂₁ C₂₂ := Region.disjoint₂₁₂₂ Dp
      -- Table 1 of BDPZ (ISSAC 2009), with products accumulated in `C`.
      let X : Matrix R h h := Matrix.ofFn fun i j => A₁₁.entry i j - A₂₁.entry i j
      let Y : Matrix R h h := Matrix.ofFn fun i j => B₂₂.entry i j - B₁₂.entry i j
      let C := mulStrassenInto cfg (Submatrix.ofMatrix X) (Submatrix.ofMatrix Y) C C₂₁
      let X := Matrix.ofFn fun i j => A₂₁.entry i j + A₂₂.entry i j
      let Y := Matrix.ofFn fun i j => B₁₂.entry i j - B₁₁.entry i j
      let C := mulStrassenInto cfg (Submatrix.ofMatrix X) (Submatrix.ofMatrix Y) C C₂₂
      let X := (Region.full h h).accumulateWith X (fun i j => A₁₁.entry i j)
        (fun x a => x - a)
      let Y := (Region.full h h).accumulateWith Y (fun i j => B₂₂.entry i j)
        (fun y b => b - y)
      let C := mulStrassenInto cfg (Submatrix.ofMatrix X) (Submatrix.ofMatrix Y) C C₁₂
      let X := (Region.full h h).accumulateWith X (fun i j => A₁₂.entry i j)
        (fun x a => a - x)
      let C := mulStrassenInto cfg (Submatrix.ofMatrix X) B₂₂ C C₁₁
      let X := mulStrassenInto cfg A₁₁ B₁₁ X (Region.full h h)
      let C := C₁₂.accumulateExternal C X (fun p₆ p₁ => p₁ + p₆)
      let C := C₂₁.accumulate C₁₂ (Region.disjoint_comm.mp h₁₂₂₁) C
        (fun p₇ u₂ => u₂ + p₇)
      let C := C₁₂.accumulate C₂₂ h₁₂₂₂ C (fun u₂ p₅ => u₂ + p₅)
      let C := C₂₂.accumulate C₂₁ (Region.disjoint_comm.mp h₂₁₂₂) C
        (fun p₅ u₃ => u₃ + p₅)
      let C := C₁₂.accumulate C₁₁ (Region.disjoint_comm.mp h₁₁₁₂) C
        (fun u₄ p₃ => u₄ + p₃)
      let Y := (Region.full h h).accumulateWith Y (fun i j => B₂₁.entry i j)
        (fun y b => y - b)
      let C := mulStrassenInto cfg A₂₂ (Submatrix.ofMatrix Y) C C₁₁
      let C := C₂₁.accumulate C₁₁ (Region.disjoint_comm.mp h₁₁₂₁) C
        (fun u₃ p₄ => u₃ - p₄)
      let C := mulStrassenInto cfg A₁₂ B₂₁ C C₁₁
      C₁₁.accumulateExternal C X (fun p₂ p₁ => p₁ + p₂)
    else
      let P := mulStrassenView cfg A B
      D.overwrite C fun i j => P[(i, j)]
  termination_by n
  decreasing_by all_goals (simp_wf; omega)

set_option maxHeartbeats 1000000 in
/-- The region writer returns the reference result in its destination and
preserves every disjoint region. -/
theorem mulStrassenInto_spec {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n N M : Nat} (A B : Submatrix R n n)
    (C : Matrix R N M) (D : Region N M n n) :
    Region.toMatrix D (mulStrassenInto cfg A B C D) = mulStrassenView cfg A B ∧
      ∀ {rows cols} (E : Region N M rows cols), Region.Disjoint D E →
        Region.toMatrix E (mulStrassenInto cfg A B C D) = Region.toMatrix E C := by
  fun_induction mulStrassenInto cfg A B C D with
  | case1 n N M A B C D hbase P =>
    constructor
    · apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Region.get_overwrite]
      rw [mulStrassenView]
      simp only [hbase, ↓reduceIte]
      rw [getElem_pair_eq_nested]
    · intro rows cols E hDE
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Region.getElem_toMatrix,
        Region.get_overwrite_disjoint D E hDE]
  | case2 n N M A B C0 D hbase h heven Ap Bp
      A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ Dp C₁₁ C₁₂ C₂₁ C₂₂
      h₁₁₁₂ h₁₁₂₁ h₁₁₂₂ h₁₂₂₁ h₁₂₂₂ h₂₁₂₂
      X4 Y3 C11 X3 Y2 C10 X2 Y1 C9 X1 C8 X C7 C6 C5 C4 C3 Y C2 C1 C
      hP7 _ hP5 _ hP6 _ hP3 hP1 _ _ hP4 _ hP2 =>
    have eS2 : Submatrix.ofMatrix X2 = (A₂₁.add A₂₂).sub A₁₁ := by
      rw [Submatrix.sub]
      congr 1
      apply Matrix.ext_getElem
      intro i j
      rw [← getElem_pair_eq_nested]
      rw [← Region.get_full X2 i j]
      rw [Region.get_accumulateWith, Region.get_full, Matrix.getElem_ofFn]
      simp only [X3, Matrix.getElem_ofFn, Submatrix.entry_ofMatrix, Submatrix.add]
      rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
    have eT2 : Submatrix.ofMatrix Y1 = B₂₂.sub (B₁₂.sub B₁₁) := by
      rw [Submatrix.sub]
      congr 1
      apply Matrix.ext_getElem
      intro i j
      rw [← getElem_pair_eq_nested]
      rw [← Region.get_full Y1 i j]
      rw [Region.get_accumulateWith, Region.get_full, Matrix.getElem_ofFn]
      simp only [Y2, Matrix.getElem_ofFn, Submatrix.entry_ofMatrix, Submatrix.sub]
      rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
    have eS4 : Submatrix.ofMatrix X1 = A₁₂.sub ((A₂₁.add A₂₂).sub A₁₁) := by
      rw [Submatrix.sub]
      congr 1
      apply Matrix.ext_getElem
      intro i j
      rw [← getElem_pair_eq_nested]
      rw [← Region.get_full X1 i j]
      rw [Region.get_accumulateWith, Matrix.getElem_ofFn]
      rw [Region.get_of_toMatrix_eq (Region.full h h) X2
        (Matrix.ofFn fun i j => (A₂₁.entry i j + A₂₂.entry i j) - A₁₁.entry i j)]
      · simp only [Matrix.getElem_ofFn, Submatrix.entry_ofMatrix, Submatrix.sub,
          Submatrix.add]
        rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
      · apply Matrix.ext_getElem
        intro i j
        rw [Region.getElem_toMatrix, Region.get_accumulateWith, Region.get_full]
        simp only [X3]
        rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
        rw [Matrix.getElem_ofFn]
    have eT4 : Submatrix.ofMatrix Y =
        (B₂₂.sub (B₁₂.sub B₁₁)).sub B₂₁ := by
      rw [Submatrix.sub]
      congr 1
      apply Matrix.ext_getElem
      intro i j
      rw [← getElem_pair_eq_nested]
      rw [← Region.get_full Y i j]
      rw [Region.get_accumulateWith, Matrix.getElem_ofFn]
      rw [Region.get_of_toMatrix_eq (Region.full h h) Y1
        (Matrix.ofFn fun i j => B₂₂.entry i j -
          (B₁₂.entry i j - B₁₁.entry i j))]
      · simp only [Matrix.getElem_ofFn, Submatrix.entry_ofMatrix, Submatrix.sub]
        rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
      · apply Matrix.ext_getElem
        intro i j
        rw [Region.getElem_toMatrix, Region.get_accumulateWith, Region.get_full]
        simp only [Y2]
        rw [getElem_pair_eq_nested, Matrix.getElem_ofFn]
        rw [Matrix.getElem_ofFn]
    have eS3 : Submatrix.ofMatrix X4 = A₁₁.sub A₂₁ := by rfl
    have eT3 : Submatrix.ofMatrix Y3 = B₂₂.sub B₁₂ := by rfl
    have eS1 : Submatrix.ofMatrix X3 = A₂₁.add A₂₂ := by rfl
    have eT1 : Submatrix.ofMatrix Y2 = B₁₂.sub B₁₁ := by rfl
    let P1 := mulStrassenView cfg A₁₁ B₁₁
    let P2 := mulStrassenView cfg A₁₂ B₂₁
    let P3 := mulStrassenView cfg (A₁₂.sub ((A₂₁.add A₂₂).sub A₁₁)) B₂₂
    let P4 := mulStrassenView cfg A₂₂
      ((B₂₂.sub (B₁₂.sub B₁₁)).sub B₂₁)
    let P5 := mulStrassenView cfg (A₂₁.add A₂₂) (B₁₂.sub B₁₁)
    let P6 := mulStrassenView cfg ((A₂₁.add A₂₂).sub A₁₁)
      (B₂₂.sub (B₁₂.sub B₁₁))
    let P7 := mulStrassenView cfg (A₁₁.sub A₂₁) (B₂₂.sub B₁₂)
    have gP7 (i j : Fin h) : C₂₁.get C11 i j = P7[(i, j)] :=
      Region.get_of_toMatrix_eq C₂₁ C11 _ (by simpa only [eS3, eT3, C11] using hP7.1) i j
    have gP5 (i j : Fin h) : C₂₂.get C10 i j = P5[(i, j)] :=
      Region.get_of_toMatrix_eq C₂₂ C10 _ (by simpa only [eS1, eT1, C10] using hP5.1) i j
    have gP6 (i j : Fin h) : C₁₂.get C9 i j = P6[(i, j)] :=
      Region.get_of_toMatrix_eq C₁₂ C9 _ (by simpa only [eS2, eT2, C9] using hP6.1) i j
    have gP3 (i j : Fin h) : C₁₁.get C8 i j = P3[(i, j)] :=
      Region.get_of_toMatrix_eq C₁₁ C8 _ (by simpa only [eS4, C8] using hP3.1) i j
    have gP1 (i j : Fin h) : X[(i, j)] = P1[(i, j)] := by
      rw [← Region.get_full X i j]
      exact Region.get_of_toMatrix_eq (Region.full h h) X _ hP1.1 i j
    have gP4 (i j : Fin h) : C₁₁.get C2 i j = P4[(i, j)] :=
      Region.get_of_toMatrix_eq C₁₁ C2 _ (by simpa only [eT4, C2] using hP4.1) i j
    have gP2 (i j : Fin h) : C₁₁.get C i j = P2[(i, j)] :=
      Region.get_of_toMatrix_eq C₁₁ C _ (by simpa only [C] using hP2.1) i j
    have gU2 (i j : Fin h) : C₁₂.get C7 i j = P1[(i, j)] + P6[(i, j)] := by
      rw [Region.get_accumulateExternal, gP1]
      rw [Region.get_eq_of_toMatrix_eq C₁₂ C8 C9
        (by simpa only [C8] using hP3.2 C₁₂ h₁₁₁₂)]
      rw [gP6]
    have gP7C7 (i j : Fin h) : C₂₁.get C7 i j = P7[(i, j)] := by
      rw [Region.get_accumulateExternal_disjoint C₁₂ C₂₁ h₁₂₂₁]
      rw [Region.get_eq_of_toMatrix_eq C₂₁ C8 C9
        (by simpa only [C8] using hP3.2 C₂₁ h₁₁₂₁)]
      rw [Region.get_eq_of_toMatrix_eq C₂₁ C9 C10
        (by simpa only [C9] using hP6.2 C₂₁ h₁₂₂₁)]
      rw [Region.get_eq_of_toMatrix_eq C₂₁ C10 C11
        (by simpa only [C10] using hP5.2 C₂₁ (Region.disjoint_comm.mp h₂₁₂₂))]
      exact gP7 i j
    have gU3 (i j : Fin h) : C₂₁.get C6 i j =
        (P1[(i, j)] + P6[(i, j)]) + P7[(i, j)] := by
      rw [Region.get_accumulate, gU2, gP7C7]
    have gP5C6 (i j : Fin h) : C₂₂.get C6 i j = P5[(i, j)] := by
      rw [Region.get_accumulate_disjoint C₂₁ C₁₂ _ C₂₂ h₂₁₂₂]
      rw [Region.get_accumulateExternal_disjoint C₁₂ C₂₂ h₁₂₂₂]
      rw [Region.get_eq_of_toMatrix_eq C₂₂ C8 C9
        (by simpa only [C8] using hP3.2 C₂₂ h₁₁₂₂)]
      rw [Region.get_eq_of_toMatrix_eq C₂₂ C9 C10
        (by simpa only [C9] using hP6.2 C₂₂ h₁₂₂₂)]
      exact gP5 i j
    have gU4 (i j : Fin h) : C₁₂.get C5 i j =
        (P1[(i, j)] + P6[(i, j)]) + P5[(i, j)] := by
      rw [Region.get_accumulate]
      rw [Region.get_accumulate_disjoint C₂₁ C₁₂ _ C₁₂
        (Region.disjoint_comm.mp h₁₂₂₁), gU2, gP5C6]
    have gU7 (i j : Fin h) : C₂₂.get C4 i j =
        ((P1[(i, j)] + P6[(i, j)]) + P7[(i, j)]) + P5[(i, j)] := by
      rw [Region.get_accumulate]
      rw [Region.get_accumulate_disjoint C₁₂ C₂₂ _ C₂₂ h₁₂₂₂,
        gP5C6]
      rw [Region.get_accumulate_disjoint C₁₂ C₂₂ _ C₂₁ h₁₂₂₁,
        gU3]
    have gP3C4 (i j : Fin h) : C₁₁.get C4 i j = P3[(i, j)] := by
      rw [Region.get_accumulate_disjoint C₂₂ C₂₁ _ C₁₁
        (Region.disjoint_comm.mp h₁₁₂₂)]
      rw [Region.get_accumulate_disjoint C₁₂ C₂₂ _ C₁₁
        (Region.disjoint_comm.mp h₁₁₁₂)]
      rw [Region.get_accumulate_disjoint C₂₁ C₁₂ _ C₁₁
        (Region.disjoint_comm.mp h₁₁₂₁)]
      rw [Region.get_accumulateExternal_disjoint C₁₂ C₁₁
        (Region.disjoint_comm.mp h₁₁₁₂)]
      exact gP3 i j
    have gU5 (i j : Fin h) : C₁₂.get C3 i j =
        ((P1[(i, j)] + P6[(i, j)]) + P5[(i, j)]) + P3[(i, j)] := by
      rw [Region.get_accumulate, gP3C4]
      rw [Region.get_accumulate_disjoint C₂₂ C₂₁ _ C₁₂
        (Region.disjoint_comm.mp h₁₂₂₂), gU4]
    have e11 : C₁₁.toMatrix (C₁₁.accumulateExternal C X fun p2 p1 => p1 + p2) =
        P1 + P2 := by
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Region.get_accumulateExternal, Matrix.getElem_add,
        gP1, gP2]
      simp only [getElem_pair_eq_nested]
    have e21 : C₂₁.toMatrix (C₁₁.accumulateExternal C X fun p2 p1 => p1 + p2) =
        (P1 + P6 + P7) - P4 := by
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Matrix.getElem_sub, Matrix.getElem_add, Matrix.getElem_add]
      rw [Region.get_accumulateExternal_disjoint C₁₁ C₂₁ h₁₁₂₁]
      rw [Region.get_eq_of_toMatrix_eq C₂₁ C C1
        (by simpa only [C] using hP2.2 C₂₁ h₁₁₂₁)]
      rw [Region.get_accumulate, gP4]
      rw [Region.get_eq_of_toMatrix_eq C₂₁ C2 C3
        (by simpa only [C2] using hP4.2 C₂₁ h₁₁₂₁)]
      rw [Region.get_accumulate_disjoint C₁₂ C₁₁ _ C₂₁ h₁₂₂₁]
      rw [Region.get_accumulate_disjoint C₂₂ C₂₁ _ C₂₁
        (Region.disjoint_comm.mp h₂₁₂₂)]
      rw [Region.get_accumulate_disjoint C₁₂ C₂₂ _ C₂₁ h₁₂₂₁]
      rw [gU3]
      simp only [getElem_pair_eq_nested]
    have e12 : C₁₂.toMatrix (C₁₁.accumulateExternal C X fun p2 p1 => p1 + p2) =
        (P1 + P6 + P5) + P3 := by
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Matrix.getElem_add, Matrix.getElem_add, Matrix.getElem_add]
      rw [Region.get_accumulateExternal_disjoint C₁₁ C₁₂ h₁₁₁₂]
      rw [Region.get_eq_of_toMatrix_eq C₁₂ C C1
        (by simpa only [C] using hP2.2 C₁₂ h₁₁₁₂)]
      rw [Region.get_accumulate_disjoint C₂₁ C₁₁ _ C₁₂
        (Region.disjoint_comm.mp h₁₂₂₁)]
      rw [Region.get_eq_of_toMatrix_eq C₁₂ C2 C3
        (by simpa only [C2] using hP4.2 C₁₂ h₁₁₁₂)]
      rw [gU5]
      simp only [getElem_pair_eq_nested]
    have e22 : C₂₂.toMatrix (C₁₁.accumulateExternal C X fun p2 p1 => p1 + p2) =
        (P1 + P6 + P7) + P5 := by
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Matrix.getElem_add, Matrix.getElem_add, Matrix.getElem_add]
      rw [Region.get_accumulateExternal_disjoint C₁₁ C₂₂ h₁₁₂₂]
      rw [Region.get_eq_of_toMatrix_eq C₂₂ C C1
        (by simpa only [C] using hP2.2 C₂₂ h₁₁₂₂)]
      rw [Region.get_accumulate_disjoint C₂₁ C₁₁ _ C₂₂ h₂₁₂₂]
      rw [Region.get_eq_of_toMatrix_eq C₂₂ C2 C3
        (by simpa only [C2] using hP4.2 C₂₂ h₁₁₂₂)]
      rw [Region.get_accumulate_disjoint C₁₂ C₁₁ _ C₂₂ h₁₂₂₂]
      rw [gU7]
      simp only [getElem_pair_eq_nested]
    let Cout := C₁₁.accumulateExternal C X fun p2 p1 => p1 + p2
    have assembled : Dp.toMatrix Cout =
        fromBlocks (P1 + P2) ((P1 + P6 + P5) + P3)
          ((P1 + P6 + P7) - P4) ((P1 + P6 + P7) + P5) := by
      rw [← Matrix.fromBlocks_toBlocks (Dp.toMatrix Cout)]
      rw [← Region.toMatrix_toBlocks₁₁ Dp Cout,
        ← Region.toMatrix_toBlocks₁₂ Dp Cout,
        ← Region.toMatrix_toBlocks₂₁ Dp Cout,
        ← Region.toMatrix_toBlocks₂₂ Dp Cout]
      simp only [Cout]
      rw [e11, e12, e21, e22]
    have reference : castDims heven heven (mulStrassenView cfg A B) =
        fromBlocks (P1 + P2) ((P1 + P6 + P5) + P3)
          ((P1 + P6 + P7) - P4) ((P1 + P6 + P7) + P5) := by
      rw [mulStrassenView]
      simp only [hbase, ↓reduceIte]
      rw [castDims_crop]
    constructor
    · apply castDims_inj heven heven
      rw [castDims_toMatrix heven heven D Dp rfl rfl, assembled, reference]
    · intro rows cols E hDE
      have hDpE : Region.Disjoint Dp E := by
        simp only [Region.Disjoint, Dp] at hDE ⊢
        omega
      have h11E : Region.Disjoint C₁₁ E := by
        simpa only [C₁₁] using Region.disjoint_toBlocks₁₁ Dp E hDpE
      have h12E : Region.Disjoint C₁₂ E := by
        simpa only [C₁₂] using Region.disjoint_toBlocks₁₂ Dp E hDpE
      have h21E : Region.Disjoint C₂₁ E := by
        simpa only [C₂₁] using Region.disjoint_toBlocks₂₁ Dp E hDpE
      have h22E : Region.Disjoint C₂₂ E := by
        simpa only [C₂₂] using Region.disjoint_toBlocks₂₂ Dp E hDpE
      calc
        E.toMatrix Cout = E.toMatrix C := by
          simpa only [Cout] using
            Region.toMatrix_accumulateExternal_disjoint C₁₁ E h11E C X
              (fun p2 p1 => p1 + p2)
        _ = E.toMatrix C1 := by simpa only [C] using hP2.2 E h11E
        _ = E.toMatrix C2 := by
          simpa only [C1] using
            Region.toMatrix_accumulate_disjoint C₂₁ C₁₁
              (Region.disjoint_comm.mp h₁₁₂₁) E h21E C2 (fun u3 p4 => u3 - p4)
        _ = E.toMatrix C3 := by simpa only [C2] using hP4.2 E h11E
        _ = E.toMatrix C4 := by
          simpa only [C3] using
            Region.toMatrix_accumulate_disjoint C₁₂ C₁₁
              (Region.disjoint_comm.mp h₁₁₁₂) E h12E C4 (fun u4 p3 => u4 + p3)
        _ = E.toMatrix C5 := by
          simpa only [C4] using
            Region.toMatrix_accumulate_disjoint C₂₂ C₂₁
              (Region.disjoint_comm.mp h₂₁₂₂) E h22E C5 (fun p5 u3 => u3 + p5)
        _ = E.toMatrix C6 := by
          simpa only [C5] using
            Region.toMatrix_accumulate_disjoint C₁₂ C₂₂ h₁₂₂₂ E h12E C6
              (fun u2 p5 => u2 + p5)
        _ = E.toMatrix C7 := by
          simpa only [C6] using
            Region.toMatrix_accumulate_disjoint C₂₁ C₁₂
              (Region.disjoint_comm.mp h₁₂₂₁) E h21E C7 (fun p7 u2 => u2 + p7)
        _ = E.toMatrix C8 := by
          simpa only [C7] using
            Region.toMatrix_accumulateExternal_disjoint C₁₂ E h12E C8 X
              (fun p6 p1 => p1 + p6)
        _ = E.toMatrix C9 := by simpa only [C8] using hP3.2 E h11E
        _ = E.toMatrix C10 := by simpa only [C9] using hP6.2 E h12E
        _ = E.toMatrix C11 := by simpa only [C10] using hP5.2 E h22E
        _ = E.toMatrix C0 := by simpa only [C11] using hP7.2 E h21E
  | case3 n N M A B C D hbase h hOdd P =>
    constructor
    · apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Region.get_overwrite]
      rw [getElem_pair_eq_nested]
    · intro rows cols E hDE
      apply Matrix.ext_getElem
      intro i j
      rw [Region.getElem_toMatrix, Region.getElem_toMatrix,
        Region.get_overwrite_disjoint D E hDE]

/-- **Strassen-Winograd multiplication.** The public entry point wraps the operands
as full-matrix `Submatrix` views and runs the view recursion `mulStrassenView`;
the quadrant splitting inside never materializes or copies a quadrant buffer —
only O(1) view records. -/
@[expose]
def mulStrassen {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n m k : Nat} (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  mulStrassenView cfg (Submatrix.ofMatrix M) (Submatrix.ofMatrix N)

/-- Storage-scheduled implementation of `mulStrassen`.  Square inputs run the
two-buffer writer; all other shapes retain the reference view recursion. -/
@[expose]
def mulStrassenImpl {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n m k : Nat} (A : Matrix R n m) (B : Matrix R m k) :
    Matrix R n k :=
  if hnm : n = m then
    if hmk : m = k then
      if n ≤ 1 ∨ n < cfg.cutoff then
        mulStrassenView cfg (Submatrix.ofMatrix A) (Submatrix.ofMatrix B)
      else
        let A' : Matrix R n n := castDims rfl hnm.symm A
        let B' : Matrix R n n := castDims hnm.symm (hmk.symm.trans hnm.symm) B
        let C : Matrix R n n := Matrix.ofFn fun _ _ => 0
        castDims rfl (hnm.trans hmk)
          (mulStrassenInto cfg (Submatrix.ofMatrix A') (Submatrix.ofMatrix B') C
            (Region.full n n))
    else
      mulStrassenView cfg (Submatrix.ofMatrix A) (Submatrix.ofMatrix B)
  else
    mulStrassenView cfg (Submatrix.ofMatrix A) (Submatrix.ofMatrix B)

/-- The storage-scheduled implementation is extensionally equal to the reference
entry point.  This transfers the implementation without changing
`mulStrassen`'s statement or its ring-level correctness theorem. -/
@[csimp] theorem mulStrassen_eq_impl : @mulStrassen = @mulStrassenImpl := by
  funext R _ _ _ _ cfg n m k A B
  simp only [mulStrassenImpl]
  split
  · rename_i hnm
    split
    · rename_i hmk
      subst m
      subst k
      split
      · rfl
      · simp only [castDims, mulStrassen]
        simpa only [Region.toMatrix_full] using
          (mulStrassenInto_spec cfg (Submatrix.ofMatrix A) (Submatrix.ofMatrix B)
            (Matrix.ofFn fun _ _ => 0) (Region.full n n)).1.symm
    · rfl
  · rfl

/-- The view recursion computes the same matrix as the reference `mul` of the
materialized operands, for every valid configuration. Proved by functional
induction over `mulStrassenView`, reducing each quadrant view to its `toBlocks`
materialization (`toMatrix_toBlocks…`, `toMatrix_pad_view`) and composing the
three wave-1 lemmas exactly as the `Matrix`-level recursion did. -/
theorem mulStrassenView_eq_mul [Lean.Grind.Ring R]
    (cfg : StrassenConfig R) (hcfg : cfg.Valid)
    (A : Submatrix R n m) (B : Submatrix R m k) :
    mulStrassenView cfg A B = mul A.toMatrix B.toMatrix := by
  fun_induction mulStrassenView cfg A B with
  | case1 n m k A B hbase => exact hcfg A.toMatrix B.toMatrix
  | case2 n m k A B hbase h w d Ap Bp
      A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂
      S₁ S₂ S₃ S₄ T₁ T₂ T₃ T₄
      P₁ P₂ P₃ P₄ P₅ P₆ P₇
      U₁ U₂ U₃ U₄ U₅ U₆ U₇
      hP₁ hP₂ hP₃ hP₄ hP₅ hP₆ hP₇ =>
    let win : Winograd A₁₁.toMatrix A₁₂.toMatrix A₂₁.toMatrix A₂₂.toMatrix
        B₁₁.toMatrix B₁₂.toMatrix B₂₁.toMatrix B₂₂.toMatrix :=
      { S₁ := S₁.toMatrix, S₂ := S₂.toMatrix, S₃ := S₃.toMatrix, S₄ := S₄.toMatrix,
        T₁ := T₁.toMatrix, T₂ := T₂.toMatrix, T₃ := T₃.toMatrix, T₄ := T₄.toMatrix,
        P₁, P₂, P₃, P₄, P₅, P₆, P₇,
        U₁, U₂, U₃, U₄, U₅, U₆, U₇,
        hS₁ := Submatrix.toMatrix_add A₂₁ A₂₂, hS₂ := Submatrix.toMatrix_sub S₁ A₁₁,
        hS₃ := Submatrix.toMatrix_sub A₁₁ A₂₁, hS₄ := Submatrix.toMatrix_sub A₁₂ S₂,
        hT₁ := Submatrix.toMatrix_sub B₁₂ B₁₁, hT₂ := Submatrix.toMatrix_sub B₂₂ T₁,
        hT₃ := Submatrix.toMatrix_sub B₂₂ B₁₂, hT₄ := Submatrix.toMatrix_sub T₂ B₂₁,
        hP₁, hP₂, hP₃, hP₄, hP₅, hP₆, hP₇,
        hU₁ := rfl, hU₂ := rfl, hU₃ := rfl, hU₄ := rfl,
        hU₅ := rfl, hU₆ := rfl, hU₇ := rfl }
    have e11 : U₁ = A₁₁.toMatrix * B₁₁.toMatrix + A₁₂.toMatrix * B₂₁.toMatrix := win.c11
    have e12 : U₅ = A₁₁.toMatrix * B₁₂.toMatrix + A₁₂.toMatrix * B₂₂.toMatrix := win.c12
    have e21 : U₆ = A₂₁.toMatrix * B₁₁.toMatrix + A₂₂.toMatrix * B₂₁.toMatrix := win.c21
    have e22 : U₇ = A₂₁.toMatrix * B₁₂.toMatrix + A₂₂.toMatrix * B₂₂.toMatrix := win.c22
    have hAb : fromBlocks A₁₁.toMatrix A₁₂.toMatrix A₂₁.toMatrix A₂₂.toMatrix = Ap.toMatrix := by
      show fromBlocks (Ap.toBlocks₁₁).toMatrix (Ap.toBlocks₁₂).toMatrix
        (Ap.toBlocks₂₁).toMatrix (Ap.toBlocks₂₂).toMatrix = Ap.toMatrix
      rw [toMatrix_toBlocks₁₁, toMatrix_toBlocks₁₂, toMatrix_toBlocks₂₁, toMatrix_toBlocks₂₂,
        fromBlocks_toBlocks]
    have hBb : fromBlocks B₁₁.toMatrix B₁₂.toMatrix B₂₁.toMatrix B₂₂.toMatrix = Bp.toMatrix := by
      show fromBlocks (Bp.toBlocks₁₁).toMatrix (Bp.toBlocks₁₂).toMatrix
        (Bp.toBlocks₂₁).toMatrix (Bp.toBlocks₂₂).toMatrix = Bp.toMatrix
      rw [toMatrix_toBlocks₁₁, toMatrix_toBlocks₁₂, toMatrix_toBlocks₂₁, toMatrix_toBlocks₂₂,
        fromBlocks_toBlocks]
    have hApM : Ap.toMatrix = pad A.toMatrix (h + h) (w + w) :=
      toMatrix_pad_view A (h + h) (w + w) (by omega) (by omega)
    have hBpM : Bp.toMatrix = pad B.toMatrix (w + w) (d + d) :=
      toMatrix_pad_view B (w + w) (d + d) (by omega) (by omega)
    rw [e11, e12, e21, e22, ← fromBlocks_mul_fromBlocks, hAb, hBb, hApM, hBpM]
    exact takeCols_takeRows_mul_pad A.toMatrix B.toMatrix (h + h) (w + w) (d + d)
      (by omega) (by omega) (by omega)

/-- **Correctness of Strassen-Winograd multiplication.** For every valid
configuration, `mulStrassen` computes the same matrix as the reference `mul`. -/
theorem mulStrassen_eq_mul [Lean.Grind.Ring R]
    (cfg : StrassenConfig R) (hcfg : cfg.Valid)
    (M : Matrix R n m) (N : Matrix R m k) :
    mulStrassen cfg M N = mul M N := by
  show mulStrassenView cfg (Submatrix.ofMatrix M) (Submatrix.ofMatrix N) = mul M N
  rw [mulStrassenView_eq_mul cfg hcfg, Submatrix.toMatrix_ofMatrix, Submatrix.toMatrix_ofMatrix]

end Matrix

end Hex
