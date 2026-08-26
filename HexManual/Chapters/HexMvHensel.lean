/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMvHensel

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMvHensel: checked multivariate lifting" =>
%%%
tag := "hex-mv-hensel"
%%%

# Introduction
%%%
tag := "hex-mv-hensel-intro"
%%%

`HexMvHensel` reconstructs multivariate integer factors from a factorization
of a univariate image. The extended EEZ pipeline translates an evaluation
point to the origin, installs prescribed leading coefficients, introduces
the remaining variables in order, and solves each correction equation in a
bounded degree box.

Every partial operation returns `Option` or a structured failure. Successful
public results cross an independent checker, so callers do not need to trust
point selection, the diophantine solver, or the reconstruction loop.

# Coordinates and images
%%%
tag := "hex-mv-hensel-coordinates"
%%%

{docstring Hex.MvHensel.shift}

{docstring Hex.MvHensel.unshift}

{docstring Hex.MvHensel.imageAt}

{docstring Hex.MvHensel.lcIn}

{docstring Hex.MvHensel.truncate}

The chosen main variable is fixed by translation. `imageAt` evaluates every
remaining-variable coefficient, while `lcIn` retains the top coefficient as
a polynomial in those variables.

# Univariate and multivariate corrections
%%%
tag := "hex-mv-hensel-corrections"
%%%

{docstring Hex.MvHensel.UniValid}

{docstring Hex.MvHensel.solveUni}

{docstring Hex.MvHensel.solveUni_spec}

{docstring Hex.MvHensel.witnessOf?}

{docstring Hex.MvHensel.diophantine}

{docstring Hex.MvHensel.diophantine_spec}

The univariate solver chooses degree-bounded symmetric representatives modulo
the prime power. The recursive solver lifts this partial-fraction equation
through the non-main variables and checks the final box congruence.

# Inputs, certificates, and replay
%%%
tag := "hex-mv-hensel-certificates"
%%%

{docstring Hex.MvHensel.Input}

{docstring Hex.MvHensel.Failure}

{docstring Hex.MvHensel.valid}

{docstring Hex.MvHensel.Cert}

{docstring Hex.MvHensel.check}

{docstring Hex.MvHensel.check_sound}

Validation covers tuple arities, absence of degree drop, image and leading
coefficient products, leading images, the working prime, coprimality, and
witness degree. Replay then establishes exact reassembly and the frame of
every returned factor.

# Stagewise lifting and retries
%%%
tag := "hex-mv-hensel-lifting"
%%%

{docstring Hex.MvHensel.IsStage}

{docstring Hex.MvHensel.lift}

{docstring Hex.MvHensel.liftWith}

{docstring Hex.MvHensel.lift_checks}

{docstring Hex.MvHensel.lift_progress}

Reconstruction failures retain the attempted modulus. `liftWith` can double
the exponent and regenerate the partial-fraction witness a bounded number of
times; malformed inputs are not retried.

# Uniqueness and completeness
%%%
tag := "hex-mv-hensel-completeness"
%%%

{docstring Hex.MvHensel.coeffBound}

{docstring Hex.MvHensel.lift_unique}

{docstring Hex.MvHensel.lift_complete}

{docstring Hex.MvHensel.no_lift_of_reconstruct}

The executable bound applies mixed-radix Kronecker substitution after the
coordinate shift. Once the modulus exceeds twice a valid factor-coefficient
bound, reconstruction is complete and a reconstruction failure proves that
no compatible lift tuple exists.

# Cross-references
%%%
tag := "hex-mv-hensel-cross-references"
%%%

* {ref "hex-modular"}[`HexModular`] supplies arbitrary-precision symmetric
  residues and rational reconstruction infrastructure.
* {ref "hex-mv-gcd"}[`HexMvGcd`] supplies named-variable content and the gcd
  layer used by the completeness contracts.
* `HexMvFactor` constructs valid lift inputs, distributes leading
  coefficients, and recombines the checked factors.
