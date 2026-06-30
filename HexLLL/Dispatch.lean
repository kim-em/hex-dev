/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Provider
public import HexLLL.Steered
public import HexLLL.Native

public section

/-!
The public LLL entry points. `lll` dispatches external provider →
steered → native, all certified to the same `(δ, 11/20)` contract, and
`lll.firstShortVector` / `lll.shortVectors` expose the reduced rows for
downstream consumers.
-/

namespace Hex

open Hex.Internal

/-- Top-level LLL entry point. Dispatches first to the certified-external path:
if `LLLProvider.providerAvailable ()` is true and the candidate passes
`certCheck B B' U V δ (11/20)`, the certified `B'` is returned; otherwise the
native body `lllSteered` runs (the approximation-steered reducer, which itself
certifies its output at `(δ, 11/20)` and falls back to the exact `lllNative`).
The paths satisfy the identical post-condition (`isLLLReduced (lll …) δ (11/20)`,
same lattice, the public short-vector bound), so dispatch is invisible to callers
and to proofs. -/
@[expose]
def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (_hind : b.independent) :
    Matrix Int n m :=
  match LLLProvider.dispatch b δ with
  | some B' => B'
  | none => lllSteered b δ (one_quarter_lt_of_eta_eleven_twentieths hδ) hδ' hn

/-- Proof-free executable variant of `lll.firstShortVector`. Runs the
approximation-steered reducer with certified output (`lllSteered`); the
classical precondition `1/4 < δ` flows to the exact fallback. -/
@[expose]
def lll.firstShortVectorUnchecked (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) :
    Vector Int m :=
  (lllSteered b δ hδ hδ' hn)[0]

/-- The first row of the reduced basis: a provably short vector, bounded by the
LLL approximation factor relative to any nonzero lattice vector (see
`lll_first_row_norm_sq_le_unconditional`), not necessarily the shortest lattice
vector. Canonical short-vector entry point for downstream callers such as
`hex-berlekamp-zassenhaus` recombination. -/
@[expose]
def lll.firstShortVector (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    Vector Int m :=
  (lll b δ hδ hδ' hn hind)[0]

/-- Proof-free executable variant of `lll.shortVectors`. Runs the
approximation-steered reducer with certified output (`lllSteered`). -/
@[expose]
def lll.shortVectorsUnchecked (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) :
    Array (Vector Int m) :=
  (lllSteered b δ hδ hδ' hn).toArray

/-- The full reduced basis viewed as an ordered array of candidate short
vectors. -/
@[expose]
def lll.shortVectors (b : Matrix Int n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hind : b.independent) :
    Array (Vector Int m) :=
  (lll b δ hδ hδ' hn hind).toArray

end Hex
