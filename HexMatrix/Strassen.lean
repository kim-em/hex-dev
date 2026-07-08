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
def StrassenConfig.Valid [Mul R] [Add R] [OfNat R 0] (cfg : StrassenConfig R) : Prop :=
  ∀ {n m k} (X : Matrix R n m) (Y : Matrix R m k), cfg.baseMul X Y = mul X Y

/-- The default configuration: naive `mulImpl` as the base kernel and a cutoff of
`64`.

The cutoff is **provisional**. Per `HexMatrix/SPEC/hex-matrix.md` § "Benchmarks"
the real crossover is a measured constant, established by the wave-3 Strassen
bench driver on this project's coefficient types; `64` is a placeholder until that
measurement lands. -/
@[expose]
def strassenDefault [Mul R] [Add R] [OfNat R 0] : StrassenConfig R where
  cutoff := 64
  baseMul := mulImpl

/-- The default configuration is valid: its base kernel `mulImpl` equals `mul` by
`mul_eq_mulImpl`. -/
theorem strassenDefault_valid [Mul R] [Add R] [OfNat R 0] :
    (strassenDefault (R := R)).Valid := by
  intro n m k X Y
  show mulImpl X Y = mul X Y
  rw [mul_eq_mulImpl]

/-- **Strassen-Winograd multiplication.** Recurses on the runtime dimensions,
following the Winograd schedule from `HexMatrix/SPEC/hex-matrix.md`.

Base case: when any of `n`, `m`, `k` is `≤ 1` or below `cfg.cutoff`, materialize
the current blocks and call `cfg.baseMul`. The `≤ 1` disjuncts are
config-independent, so `cutoff = 0` cannot defeat termination.

Recursive step: pad each operand up to even dimensions (`h + h`, `w + w`,
`d + d` with `h := (n+1)/2` etc.), split into 2×2 blocks with no dimension cast,
run the fifteen-addition Winograd schedule with seven recursive products, assemble
with `fromBlocks`, and crop back to `n × k`. Termination is well-founded on
`n + m + k`: the recursion fires only when `n, m, k ≥ 2`, and each halved
dimension is then strictly smaller. -/
@[expose]
def mulStrassen {R : Type u} [Mul R] [Add R] [Sub R] [OfNat R 0]
    (cfg : StrassenConfig R) {n m k : Nat} (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  if n ≤ 1 ∨ m ≤ 1 ∨ k ≤ 1 ∨ n < cfg.cutoff ∨ m < cfg.cutoff ∨ k < cfg.cutoff then
    cfg.baseMul M N
  else
    let h := (n + 1) / 2
    let w := (m + 1) / 2
    let d := (k + 1) / 2
    let Mp := pad M (h + h) (w + w)
    let Np := pad N (w + w) (d + d)
    let A₁₁ := toBlocks₁₁ Mp
    let A₁₂ := toBlocks₁₂ Mp
    let A₂₁ := toBlocks₂₁ Mp
    let A₂₂ := toBlocks₂₂ Mp
    let B₁₁ := toBlocks₁₁ Np
    let B₁₂ := toBlocks₁₂ Np
    let B₂₁ := toBlocks₂₁ Np
    let B₂₂ := toBlocks₂₂ Np
    let S₁ := A₂₁ + A₂₂
    let S₂ := S₁ - A₁₁
    let S₃ := A₁₁ - A₂₁
    let S₄ := A₁₂ - S₂
    let T₁ := B₁₂ - B₁₁
    let T₂ := B₂₂ - T₁
    let T₃ := B₂₂ - B₁₂
    let T₄ := T₂ - B₂₁
    let P₁ := mulStrassen cfg A₁₁ B₁₁
    let P₂ := mulStrassen cfg A₁₂ B₂₁
    let P₃ := mulStrassen cfg S₄ B₂₂
    let P₄ := mulStrassen cfg A₂₂ T₄
    let P₅ := mulStrassen cfg S₁ T₁
    let P₆ := mulStrassen cfg S₂ T₂
    let P₇ := mulStrassen cfg S₃ T₃
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

/-- **Correctness of Strassen-Winograd multiplication.** For every valid
configuration, `mulStrassen` computes the same matrix as the reference `mul`. -/
theorem mulStrassen_eq_mul [Lean.Grind.Ring R]
    (cfg : StrassenConfig R) (hcfg : cfg.Valid)
    (M : Matrix R n m) (N : Matrix R m k) :
    mulStrassen cfg M N = mul M N := by
  fun_induction mulStrassen cfg M N with
  | case1 n m k M N hbase => exact hcfg M N
  | case2 n m k M N hbase h w d Mp Np
      A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂
      S₁ S₂ S₃ S₄ T₁ T₂ T₃ T₄
      P₁ P₂ P₃ P₄ P₅ P₆ P₇
      U₁ U₂ U₃ U₄ U₅ U₆ U₇
      hP₁ hP₂ hP₃ hP₄ hP₅ hP₆ hP₇ =>
    let win : Winograd A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ :=
      { S₁, S₂, S₃, S₄, T₁, T₂, T₃, T₄, P₁, P₂, P₃, P₄, P₅, P₆, P₇,
        U₁, U₂, U₃, U₄, U₅, U₆, U₇,
        hS₁ := rfl, hS₂ := rfl, hS₃ := rfl, hS₄ := rfl,
        hT₁ := rfl, hT₂ := rfl, hT₃ := rfl, hT₄ := rfl,
        hP₁, hP₂, hP₃, hP₄, hP₅, hP₆, hP₇,
        hU₁ := rfl, hU₂ := rfl, hU₃ := rfl, hU₄ := rfl,
        hU₅ := rfl, hU₆ := rfl, hU₇ := rfl }
    have e11 : U₁ = A₁₁ * B₁₁ + A₁₂ * B₂₁ := win.c11
    have e12 : U₅ = A₁₁ * B₁₂ + A₁₂ * B₂₂ := win.c12
    have e21 : U₆ = A₂₁ * B₁₁ + A₂₂ * B₂₁ := win.c21
    have e22 : U₇ = A₂₁ * B₁₂ + A₂₂ * B₂₂ := win.c22
    have hAb : fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ = Mp := fromBlocks_toBlocks Mp
    have hBb : fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ = Np := fromBlocks_toBlocks Np
    rw [e11, e12, e21, e22, ← fromBlocks_mul_fromBlocks, hAb, hBb]
    exact takeCols_takeRows_mul_pad M N (h + h) (w + w) (d + d) (by omega) (by omega) (by omega)

end Matrix

end Hex
