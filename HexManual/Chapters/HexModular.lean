/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexModular

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexModular: CRT and rational reconstruction" =>
%%%
tag := "hex-modular"
%%%

# Introduction
%%%
tag := "hex-modular-intro"
%%%

`HexModular` provides executable symmetric residues, incremental Chinese
remaindering, rational reconstruction, and a bounded multimodular loop.
The implementation is Mathlib-free and uses `HexArith` for its compiled
integer extended GCD.

Every search routine checks its output before returning it. Downstream
algorithms can replay the small public correctness lemmas without unfolding
the Euclidean search or trusting an external oracle.

# Symmetric representatives
%%%
tag := "hex-modular-symmetric"
%%%

{docstring Hex.Modular.symMod}

The three characterizing theorems say that reduction preserves the ordinary
residue, lands in the closed half-modulus interval, and is unique away from
the even-modulus tie.

{docstring Hex.Modular.symMod_emod}

{docstring Hex.Modular.symMod_le}

{docstring Hex.Modular.symMod_unique}

# Incremental Chinese remaindering
%%%
tag := "hex-modular-crt"
%%%

{docstring Hex.Modular.Crt}

{docstring Hex.Modular.Crt.init}

{docstring Hex.Modular.Crt.push}

A successful push multiplies the accumulated modulus, records the new
residue, and preserves every residue already represented by the state.

{docstring Hex.Modular.Crt.push_modulus}

{docstring Hex.Modular.Crt.push_congr_new}

{docstring Hex.Modular.Crt.push_congr_old}

{docstring Hex.Modular.crt_unique}

For several residue streams sharing the same moduli,
{name}`Hex.Modular.CrtVec` computes one inverse per push and reuses it across
all coordinates. Its `push_modulus`, `push_congr_new`, and `push_congr_old`
theorems have the same shape as the scalar results.

# Rational reconstruction
%%%
tag := "hex-modular-reconstruction"
%%%

{docstring Hex.Modular.Row}

{docstring Hex.Modular.euclidUntil}

{docstring Hex.Modular.ratRecon?}

{docstring Hex.Modular.ratReconWide?}

Successful bounded reconstruction supplies congruence and size facts, and
the reduced denominator is coprime to the modulus. Under the standard
strict uniqueness bound, every admissible rational is found.

{docstring Hex.Modular.ratRecon?_congr}

{docstring Hex.Modular.ratRecon?_bounds}

{docstring Hex.Modular.ratRecon?_den_coprime}

{docstring Hex.Modular.ratRecon_unique}

{docstring Hex.Modular.ratRecon?_complete}

{docstring Hex.Modular.ratReconVec?}

The maximal-quotient variant is intentionally heuristic. Its theorem promises
only the checked modular congruence, not recovery of a preferred rational.

{docstring Hex.Modular.ratReconMaxQuot?}

{docstring Hex.Modular.ratReconMaxQuot?_congr}

# Multimodular loops
%%%
tag := "hex-modular-loop"
%%%

{docstring Hex.Modular.crtLoop}

The loop skips missing images and rejected moduli, tests the caller's exact
acceptance function only after a successful push, and consumes at most the
supplied fuel. {name}`Hex.Modular.CrtTrace` records the precise consumed
prefix.

{docstring Hex.Modular.crtLoop_trace}

{docstring Hex.Modular.crtLoop_of_some}

## Worked example
%%%
tag := "hex-modular-worked"
%%%

The first computation combines `1 mod 3` and `0 mod 2`; the second recovers
the rational `2/3` from its residue `68 mod 101`.

```lean
open Hex.Modular

namespace HexModularChapter

def combined : Option (Nat × Int) := do
  let first ← Crt.init.push 1 3
  let second ← first.push 0 2
  pure (second.modulus, second.value)

#guard combined = some (6, -2)
#guard symMod 17 10 = -3
#guard
  ratRecon? 68 101 8 8 =
    some (Rat.divInt 2 3)

end HexModularChapter
```

# The Mathlib correspondence
%%%
tag := "hex-modular-mathlib"
%%%

The executable library states congruence using integer remainders and
`Rat`. The specified `HexModularMathlib` companion transports those results
to `ZMod` and `ℚ`, including the Chinese-remainder equivalence and rational
reconstruction predicates. Until that bridge is available, the integer
congruence lemmas above are the supported proof boundary.

# Cross-references
%%%
tag := "hex-modular-cross-references"
%%%

* {ref "hex-arith"}[`HexArith`] supplies the compiled extended GCD used by
  CRT accumulation.
* {ref "hex-mod-arith"}[`HexModArith`] supplies the bundled deterministic
  modulus stream used by modular algorithms.
* `HexPolyZGcd`, `HexMvGcd`, and `HexMvHensel` consume this library's CRT,
  reconstruction, and multimodular-loop APIs.
