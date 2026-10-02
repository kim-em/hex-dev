/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexReflectMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexReflect: shared algebraic reflection" =>
%%%
tag := "hex-reflect"
%%%

# Introduction
%%%
tag := "hex-reflect-intro"
%%%

`HexReflect` turns a batch of commutative-ring expressions into `Hex.MvPoly`
values over one sealed variable environment and proves that the conversion
preserves interpretation. It is the only Hex library that imports
`Lean.Meta.Sym.Arith`: Lean canonicalizes expressions, classifies their
algebraic structure, and recognizes the fixed ring language, while this
library owns the atom environment, the conversion to executable values, the
interpretation proofs, provider selection, conditions, and resource
accounting. Symbolic frontends such as the planned matrix tactics consume
the session and result records defined here rather than parsing expressions
themselves.

The computational library is Mathlib-free and depends on
{ref "hex-mv-poly"}[`HexMvPoly`] and {ref "hex-basic"}[`HexBasic`].
`HexReflectMathlib`, described in
{ref "hex-reflect-mathlib"}[the correspondence section], states the
conversion theorem for Mathlib's multivariate polynomials.

# Sessions and batches
%%%
tag := "hex-reflect-sessions"
%%%

A session belongs to one tactic invocation or one programmatic batch. The
standalone runner enters `SymM.run` exactly once; every operation is written
over any monad that lifts `SymM` and carries the session state, so a richer
caller can run the same operations without a nested run.

{docstring Hex.Reflect.ReflectM}

{docstring Hex.Reflect.run}

A batch has two phases. While the environment is growing, every input is
canonicalized, classified, and reified with the current Lean reifier; an
otherwise unrecognized subexpression becomes one atom, and repeated
canonical atoms receive the same identifier. Sealing fixes the size `n`, and
every conversion after that point is against the same `Fin n`.

{docstring Hex.Reflect.reifyCommRing}

{docstring Hex.Reflect.reifyCommSemiring}

{docstring Hex.Reflect.sealAtoms}

{docstring Hex.Reflect.reflectRingBatch}

A matrix frontend passes all entries as one batch: calling the
single-expression runner once per entry would number equal atoms
differently and make polynomial matrix operations meaningless.

{docstring Hex.Reflect.reflectRing}

# Conversion and its proof
%%%
tag := "hex-reflect-conversion"
%%%

The conversion consumes the reflected value directly. It normalizes with
`Expr.toPoly`, or with `Expr.toPolyC` when Lean supplies characteristic
evidence, translates each ordered variable and exponent to an exponent
vector, maps every integer coefficient through the selected coefficient
provider, and builds the polynomial with `Hex.MvPoly.ofTerms` under the
requested comparator. Every variable bound is checked.

{docstring Hex.Reflect.convertTerms?}

{docstring Hex.Reflect.ofIntTerms}

{docstring Hex.Reflect.convert}

The value-level soundness theorem is proved from the public
`Lean.Grind.CommRing` denotation theorems and the evaluation laws of
`Hex.MvPoly`.

{docstring Hex.Reflect.eval₂_convertTerms}

{docstring Hex.Reflect.eval₂_convertTermsC}

The Meta proof returned to a caller applies these theorems to the quoted
reflected syntax, sealed context, and term list. The equality between the
pure conversion and the quoted term list is left to reduction of concrete
reflected data, and the result is related to the caller's source by
definitional equality. No symbolic evaluation is decided by the kernel.

{docstring Hex.Reflect.Conversion.mkProof}

{docstring Hex.Reflect.EqualityResult}

# Providers, conditions, and budgets
%%%
tag := "hex-reflect-providers"
%%%

A provider supplies executable operations together with the theorems needed
to interpret them. Registration is separate from `Lean.Meta.Sym.Arith`
recognition: it can change which verified computation handles a request, but
it cannot change the source grammar or atom allocation.

{docstring Hex.Reflect.Registration}

{docstring Hex.Reflect.CoeffLaws}

{docstring Hex.Reflect.ProviderOutcome}

{docstring Hex.Reflect.Decline}

{docstring Hex.Reflect.Failure}

Conditions record the propositions a result depends on, together with their
provenance. Deduplication uses provenance and canonical proposition identity
and preserves the first occurrence, so side-goal order is deterministic.

{docstring Hex.Reflect.Condition}

{docstring Hex.Reflect.dischargeConditions}

Budgets bound every dimension of a request independently. Exhaustion is a
decline that reports the dimension, limit, consumed amount, and requested
increment.

{docstring Hex.Reflect.Budget}

{docstring Hex.Reflect.BudgetExhausted}

# Mathlib correspondence
%%%
tag := "hex-reflect-mathlib"
%%%

`HexReflectMathlib` records the coefficient interpretation of a reflected
batch as a Mathlib ring homomorphism, translates Mathlib characteristic
evidence into the Grind form used by characteristic-aware normalization, and
states the conversion theorem for `MvPolynomial (Fin n) R` through
`HexMvPolyMathlib.equiv`.

{docstring HexReflectMathlib.coeffLaws_ofRingHom}

{docstring HexReflectMathlib.isCharP_of_charP}

{docstring HexReflectMathlib.eval₂_equiv_ofIntTerms}

{docstring HexReflectMathlib.aeval_algEquiv_ofIntTerms}
