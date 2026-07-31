/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.ExternalReducer
public import HexLLL.Native

public section

/-!
The public LLL reduction. `lll` first certifies a candidate from the optional
external reducer and otherwise runs the exact `lllNative`. Both satisfy the
same `(δ, 11/20)` contract. `lll.firstShortVector` / `lll.shortVectors`
expose the reduced rows for downstream consumers.
-/

namespace Hex

open Hex.Internal

/-- Top-level LLL entry point. It first tries certified external reduction:
if `ExternalReducer.externalReducerAvailable ()` is true and the candidate passes
`certCheck B B' U V δ (11/20)`, the certified `B'` is returned; otherwise
{name}`Hex.lllNative` runs. Both paths satisfy the identical post-condition
(`isLLLReduced (lll …) δ (11/20)`, same lattice, the public short-vector bound),
so the choice is invisible to callers and to proofs. `δ` defaults to the
classical LLL parameter `3/4`, so a call can be as short as `lll b`. -/
@[expose]
def lll (b : Matrix Int n m) (δ : Rat := 3/4)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Matrix Int n m :=
  match ExternalReducer.certifiedReduction b δ with
  | some B' => B'
  | none => lllNative b δ (one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn

/-- Install an external LLL reducer from the shared library at
`path` for the rest of this process, returning whether the load succeeded.

The library must export `lean_fplll_lll_reduce` (the fpLLL-ffi shim built by
`scripts/oracle/setup_fplll_ffi.sh`); the loader calls `dlopen`, resolves that
symbol, and records the reduction function. Once installed, a {name}`Hex.lll`
call whose candidate certifies under {name}`Hex.certCheck` returns the accelerated
basis; an absent reducer, a load failure, or a rejected candidate all fall
through to the exact {name}`Hex.lllNative`. Loading is an explicit action; there is no
environment-variable read and no implicit load; and the trust boundary is
unchanged: every external candidate is checked before use.

A later successful load replaces the current reducer; a failed load leaves the
existing state untouched and returns `false` (writing the `dlopen`/`dlsym`
diagnostic to stderr) when the library cannot be loaded or does not export the
expected symbol. -/
@[expose]
def lll.loadExternalReducer (path : System.FilePath) : IO Bool :=
  Internal.ExternalReducer.loadExternalReducerImpl path.toString

/-- Whether an external LLL reducer is currently installed in this
process (via {name}`Hex.lll.loadExternalReducer` or a statically linked symbol).
When this is `false`, {name}`Hex.lll` runs the exact {name}`Hex.lllNative`; when
it is `true`, {name}`Hex.lll` attempts the certified external path first. Querying availability is
side-effect-free apart from the one-shot static-symbol trial it may trigger. -/
@[expose]
def lll.externalReducerActive : IO Bool :=
  return Internal.ExternalReducer.externalReducerAvailable ()

/-- First row of {name}`Hex.lllNative`'s output on the exact native path. It is
the non-selected counterpart of the public short-vector entry point below,
never consults an external reducer, and takes no
`b.independent` hypothesis, so Mathlib-free callers can use it directly; its
short-vector guarantee at `η = 1/2` is
proved by `HexLLLMathlib.lllNative_first_row_norm_sq_le`. -/
@[expose]
def lllNative.firstShortVector (b : Matrix Int n m) (δ : Rat := 3/4)
    (hδ : 1/4 < δ := by grind) (hδ' : δ ≤ 1 := by grind) (hn : 1 ≤ n := by grind) :
    Vector Int m :=
  (lllNative b δ hδ hδ' hn).getRow ⟨0, hn⟩

/-- The first row of the reduced basis: a provably short vector, bounded by the
LLL approximation factor relative to any nonzero lattice vector, though not
necessarily the shortest lattice vector. The precise correspondence theorem is
`HexLLLMathlib.lll_first_row_norm_sq_le`. This is the canonical short-vector
entry point for integer-polynomial recombination algorithms. -/
@[expose]
def lll.firstShortVector (b : Matrix Int n m) (δ : Rat := 3/4)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Vector Int m :=
  (lll b δ hδ hδ' hn).getRow ⟨0, hn⟩

/-- Full {name}`Hex.lllNative` output as an ordered array of candidate short
vectors on the exact native path, forgoing the external reducer and the
`b.independent` hypothesis. -/
@[expose]
def lllNative.shortVectors (b : Matrix Int n m) (δ : Rat := 3/4)
    (hδ : 1/4 < δ := by grind) (hδ' : δ ≤ 1 := by grind) (hn : 1 ≤ n := by grind) :
    Array (Vector Int m) :=
  (lllNative b δ hδ hδ' hn).rows.toArray

/-- The full reduced basis viewed as an ordered array of candidate short
vectors. -/
@[expose]
def lll.shortVectors (b : Matrix Int n m) (δ : Rat := 3/4)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Array (Vector Int m) :=
  (lll b δ hδ hδ' hn).rows.toArray

end Hex
