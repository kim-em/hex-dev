/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality

public section

/-! Rejection immediately above the core elaborator's bit ceiling. -/

/--
error: primality: input has 513 bits; the enforced policy supports at most 512 bits; raising the ceiling requires new end-to-end benchmark evidence
-/
#guard_msgs in
example : Hex.Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 :=
  primality 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
