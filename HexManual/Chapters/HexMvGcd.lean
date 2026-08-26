/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMvGcd

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMvGcd: checked sparse multivariate gcds" =>
%%%
tag := "hex-mv-gcd"
%%%

# Introduction
%%%
tag := "hex-mv-gcd-intro"
%%%

`HexMvGcd` supplies exact division, content, gcd, and square-free
decomposition for `Hex.MvPoly`. The public gcd is canonical up to the
coefficient-domain normalization convention, and every fast proposal is
accepted only after replay by the common certificate checker.

The implementation is Mathlib-free. Integer inputs use heuristic and Brown
modular producers before a deterministic subresultant fallback; rational and
bounded prime-field inputs use the same checked boundary with the appropriate
coefficient operations.

# Exact division and normalization
%%%
tag := "hex-mv-gcd-division"
%%%

{docstring Hex.MvPoly.divMod}

{docstring Hex.MvPoly.divExact?}

{docstring Hex.MvPoly.divMod_spec}

{docstring Hex.MvPoly.eq_mul_of_divExact?_eq_some}

The division order is the polynomial's declared monomial order. Exact
division returns `none` when the sparse remainder is nonzero; it never exposes
a quotient that has not been checked against the original product.

{docstring Hex.MvPoly.content}

{docstring Hex.MvPoly.primPart}

{docstring Hex.MvPoly.polyNormalize}

# Certificates and the public gcd
%%%
tag := "hex-mv-gcd-certificates"
%%%

{docstring Hex.MvPoly.GcdCert}

{docstring Hex.MvPoly.checkGcd}

{docstring Hex.MvPoly.checkGcd_sound}

{docstring Hex.MvPoly.gcdCert}

{docstring Hex.MvPoly.gcd}

{docstring Hex.MvPoly.cofactors}

The checker proves exact left and right cofactor identities and that the two
remaining cofactors are coprime. The maximality theorem then gives the usual
universal property.

{docstring Hex.MvPoly.gcd_dvd_left}

{docstring Hex.MvPoly.gcd_dvd_right}

{docstring Hex.MvPoly.dvd_gcd}

# Named-variable content
%%%
tag := "hex-mv-gcd-content-in"
%%%

Multivariate factorization treats one variable as the current main variable.
The recursive coefficient view supports content and primitive part in all
other variables without changing the sparse ambient representation.

{docstring Hex.MvPoly.contentIn}

{docstring Hex.MvPoly.primPartIn}

{docstring Hex.MvPoly.contentIn_mul_primPartIn}

# Square-free decomposition
%%%
tag := "hex-mv-gcd-square-free"
%%%

{docstring Hex.MvPoly.SqfDecomp}

{docstring Hex.MvPoly.sqfDecomp}

{docstring Hex.MvPoly.radical}

{docstring Hex.MvPoly.sqfDecomp_prod}

{docstring Hex.MvPoly.sqfDecomp_squarefree}

The decomposition records primitive square-free factors together with
positive, increasing multiplicities. Its ordered product reconstructs the
primitive part; scalar and monomial content remain explicit.

# Cross-references
%%%
tag := "hex-mv-gcd-cross-references"
%%%

* {ref "hex-mv-poly"}[`HexMvPoly`] supplies the sparse representation and
  recursive coefficient views.
* {ref "hex-poly-z-gcd"}[`HexPolyZGcd`] supplies the univariate integer
  fallback and square-free base case.
* `HexMvHensel` uses named-variable content and checked gcd certificates in
  its lifting contracts; `HexMvFactor` consumes the square-free split.
