/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMvFactor

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMvFactor: checked multivariate factorization" =>
%%%
tag := "hex-mv-factor"
%%%

# Introduction
%%%
tag := "hex-mv-factor-intro"
%%%

`HexMvFactor` factors sparse multivariate polynomials over `Int`. Its bounded
driver combines structural answers, content and square-free decomposition,
Kronecker splitting, evaluation-point search, leading-coefficient
distribution, and checked extended EEZ lifting.

A stopped search is data, not an unchecked exception: the partial result
retains its already verified decomposition, the exact failure reason, and the
generator state. A complete answer additionally replays an irreducibility
certificate for every distinct factor.

# Checked decompositions
%%%
tag := "hex-mv-factor-decompositions"
%%%

{docstring Hex.MvFactor.Factor}

{docstring Hex.MvFactor.Decomp}

{docstring Hex.MvFactor.checkDecomp}

{docstring Hex.MvFactor.IsDecompOf}

{docstring Hex.MvFactor.CheckedDecomp}

{docstring Hex.MvFactor.checkDecomp_sound}

The decomposition stores integer content separately and gives each
nonconstant, primitive, normalized factor a positive multiplicity. Replay
also checks pairwise distinctness, making the result canonical enough for
downstream comparison and tactic output.

# Kronecker splitting
%%%
tag := "hex-mv-factor-kronecker"
%%%

{docstring Hex.MvFactor.kron}

{docstring Hex.MvFactor.unKron?}

{docstring Hex.MvFactor.findSplit}

{docstring Hex.MvFactor.kronDecide}

{docstring Hex.MvFactor.kronDecide_checks}

{docstring Hex.MvFactor.kronDecide_split}

Mixed-radix weights make the substitution injective on the polynomial's
degree box. Decoding rejects exponent vectors outside that box, and every
candidate split is multiplied back in the original multivariate ring before
it is exposed.

# Evaluation points and EEZ lifting
%%%
tag := "hex-mv-factor-eez"
%%%

{docstring Hex.MvFactor.Config}

{docstring Hex.MvFactor.probe}

{docstring Hex.MvFactor.scoutPoints}

{docstring Hex.MvFactor.distribute?}

{docstring Hex.MvFactor.factorSquarefree}

Point enumeration is deterministic for a fixed `Rand` state and explicitly
bounded by shell and fuel limits. Probes reject degree drops and unsuitable
images before building a Hensel input. Grouped recombination tests products
of lifted image factors and retains only exact multivariate divisors.

# Public factorization
%%%
tag := "hex-mv-factor-public"
%%%

{docstring Hex.MvFactor.Failure}

{docstring Hex.MvFactor.Partial}

{docstring Hex.MvFactor.factorWith}

{docstring Hex.MvFactor.factor?}

{docstring Hex.MvFactor.completeWith}

{docstring Hex.MvFactor.complete?}

`factor?` returns a checked product decomposition or a checked partial
decomposition with a stopping reason. `complete?` goes further: it requires
the irreducibility producer to certify every factor and performs one final
independent replay.

# Irreducibility certificates
%%%
tag := "hex-mv-factor-irreducibility"
%%%

{docstring Hex.MvFactor.IrredCert}

{docstring Hex.MvFactor.checkIrred}

{docstring Hex.MvFactor.checkIrred_sound}

{docstring Hex.MvFactor.Complete}

{docstring Hex.MvFactor.checkComplete}

{docstring Hex.MvFactor.checkComplete_sound}

Certificates cover constants, selected-variable degree one, irreducible
images with primitive leading data, embeddings from lower arity, and complete
Kronecker decisions. The checker, not the producer, is the trusted boundary.

# Cross-references
%%%
tag := "hex-mv-factor-cross-references"
%%%

* {ref "hex-mv-gcd"}[`HexMvGcd`] supplies exact division, content, and
  square-free decomposition.
* {ref "hex-mv-hensel"}[`HexMvHensel`] supplies checked reconstruction from
  suitable univariate image factorizations.
* The Mathlib companion transports checked results to `MvPolynomial` and
  provides the `factor_poly` and `irreducibility` tactics.
