/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module
public import HexGraphIso.Nauty.VSet.Basic
public import HexGraphIso.Nauty.VSet.Card
public import HexGraphIso.Nauty.VSet.Nat

/-!
Packed vertex sets: the representation and its set algebra
(`VSet.Basic`), cardinality (`VSet.Card`), and the `Nat` bitset view
the kernel-facing checker consumes (`VSet.Nat`).
-/
