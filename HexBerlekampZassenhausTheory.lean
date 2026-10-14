/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausTheory.Factorization
public import HexBerlekampZassenhausTheory.FactorSoundness
public meta import HexBerlekampZassenhausTheory.FactorTactic
public import HexBerlekampZassenhausTheory.FactorTactic
public meta import HexBerlekampZassenhausTheory.KernelFactorTactic
public import HexBerlekampZassenhausTheory.KernelFactorTactic

public section

/-!
Stable Mathlib API for integer Berlekamp-Zassenhaus factorization.

This umbrella contains the factorization specification and the tactics for
`Hex.ZPoly` and `Polynomial ℤ`. Import
`HexBerlekampZassenhausTheory.All` only when developing the correspondence
proofs themselves.
-/
