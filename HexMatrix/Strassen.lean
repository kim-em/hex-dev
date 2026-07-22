/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Block
public import HexMatrix.Pad
public import HexMatrix.Winograd

public section

/-!
Strassen-Winograd matrix multiplication.

`mulStrassen` is the recursive, ring-level multiplication entry point specified in
`HexMatrix/SPEC/hex-matrix.md` § "Strassen-Winograd multiplication". It computes a
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
of `mul`; it is a separate entry point that callers opt into (SPEC §
"Coefficient-ring requirement").
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-! ### View-to-matrix abstraction

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
  rw [Submatrix.getElem_toMatrix, getElem_toBlocks₁₁, Submatrix.getElem_toMatrix,
    Submatrix.entry, Submatrix.entry]
  simp only [Submatrix.toBlocks₁₁, Fin.val_castAdd]
  all_goals (have hi := i.isLt; have hj := j.isLt; split <;> split <;> (first | rfl | (exfalso; omega)))

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
has been re-measured twice per `HexMatrix/SPEC/hex-matrix.md` § "Benchmarks":
on the flat row-major backing with materialized quadrants and again on the
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
Recurses on the runtime dimensions following the Winograd schedule from
`HexMatrix/SPEC/hex-matrix.md`.

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

/-- **Strassen-Winograd multiplication.** The public entry point wraps the operands
as full-matrix `Submatrix` views and runs the view recursion `mulStrassenView`;
the quadrant splitting inside never materializes or copies a quadrant buffer —
only O(1) view records (see that def and `HexMatrix/SPEC/hex-matrix.md`
§ "Avoiding sub-block copies"). -/
@[expose]
def mulStrassen {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n m k : Nat} (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  mulStrassenView cfg (Submatrix.ofMatrix M) (Submatrix.ofMatrix N)

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
