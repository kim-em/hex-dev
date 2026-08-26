/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Factorization
public import HexBerlekampZassenhausMathlib.FactorSoundness
public meta import HexBerlekampZassenhausMathlib.FactorTactic
public import HexBerlekampZassenhausMathlib.FactorTactic
public meta import HexBerlekampZassenhausMathlib.KernelFactorTactic
public import HexBerlekampZassenhausMathlib.KernelFactorTactic

public section

/-!
Stable Mathlib API for integer Berlekamp-Zassenhaus factorization.

This umbrella contains the factorization specification and the tactics for
`Hex.ZPoly` and `Polynomial ℤ`. Import
`HexBerlekampZassenhausMathlib.All` only when developing the correspondence
proofs themselves.
-/
