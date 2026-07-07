/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Provider
public import HexLLL.Native

public section

/-!
The public LLL entry points. `lll` keeps two paths: the certified
external-candidate dispatch (provider → `certCheck`) and, when no
provider candidate certifies, the exact `lllNative`. Both satisfy the
same `(δ, 11/20)` contract. `lll.firstShortVector` / `lll.shortVectors`
expose the reduced rows for downstream consumers.
-/

namespace Hex

open Hex.Internal

/-- Top-level LLL entry point. Dispatches first to the certified-external path:
if `LLLProvider.providerAvailable ()` is true and the candidate passes
`certCheck B B' U V δ (11/20)`, the certified `B'` is returned; otherwise the
exact `lllNative` runs. Both paths satisfy the identical post-condition
(`isLLLReduced (lll …) δ (11/20)`, same lattice, the public short-vector bound),
so dispatch is invisible to callers and to proofs. -/
@[expose]
def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Matrix Int n m :=
  match LLLProvider.dispatch b δ with
  | some B' => B'
  | none => lllNative b δ (one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn

/-- Install an external LLL acceleration provider from the shared library at
`path` for the rest of this process, returning whether the load succeeded.

The library must export `lean_fplll_lll_reduce` (the fpLLL-ffi shim built by
`scripts/oracle/setup_fplll_ffi.sh`); `loadProvider` `dlopen`s it, resolves that
symbol, and points the dispatch at it. Once installed, a `lll` call whose
provider candidate certifies under `Hex.certCheck` returns the accelerated
basis; an absent provider, a load failure, or a rejected candidate all fall
through to the exact `lllNative`. Loading is an explicit action — there is no
environment-variable read and no implicit load — and the trust boundary is
unchanged: every provider candidate is still checked before use.

A later successful load replaces the current provider; a failed load leaves the
existing state untouched and returns `false` (writing the `dlopen`/`dlsym`
diagnostic to stderr) when the library cannot be loaded or does not export the
expected symbol. -/
@[expose]
def lll.loadProvider (path : System.FilePath) : IO Bool :=
  Internal.LLLProvider.loadProviderImpl path.toString

/-- Whether an external LLL acceleration provider is currently installed in this
process (via `Hex.lll.loadProvider` or a statically-linked provider symbol).
When this is `false`, `lll` runs the exact `lllNative`; when it is `true`, `lll`
attempts the certified external path first. Querying availability is
side-effect-free apart from the one-shot static-symbol probe it may trigger. -/
@[expose]
def lll.providerActive : IO Bool :=
  return Internal.LLLProvider.providerAvailable ()

/-- First row of `lllNative`'s output: the `lll.firstShortVector` counterpart on
the exact native path. It never consults an external provider and takes no
`b.independent` hypothesis, so Mathlib-free callers can use it directly; its
short-vector guarantee is `lllNative_first_row_norm_sq_le` at `η = 1/2`. -/
@[expose]
def lllNative.firstShortVector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ := by grind) (hδ' : δ ≤ 1 := by grind) (hn : 1 ≤ n := by grind) :
    Vector Int m :=
  (lllNative b δ hδ hδ' hn).getRow ⟨0, hn⟩

/-- The first row of the reduced basis: a provably short vector, bounded by the
LLL approximation factor relative to any nonzero lattice vector (see
`lll_first_row_norm_sq_le`), not necessarily the shortest lattice
vector. Canonical short-vector entry point for downstream callers such as
`hex-berlekamp-zassenhaus` recombination. -/
@[expose]
def lll.firstShortVector (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Vector Int m :=
  (lll b δ hδ hδ' hn).getRow ⟨0, hn⟩

/-- Full `lllNative` output as an ordered array of candidate short vectors: the
`lll.shortVectors` counterpart on the exact native path, forgoing the external
provider and the `b.independent` hypothesis. -/
@[expose]
def lllNative.shortVectors (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ := by grind) (hδ' : δ ≤ 1 := by grind) (hn : 1 ≤ n := by grind) :
    Array (Vector Int m) :=
  (lllNative b δ hδ hδ' hn).rows.toArray

/-- The full reduced basis viewed as an ordered array of candidate short
vectors. -/
@[expose]
def lll.shortVectors (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind)
    (hn : 1 ≤ n := by grind) :
    Array (Vector Int m) :=
  (lll b δ hδ hδ' hn).rows.toArray

end Hex
