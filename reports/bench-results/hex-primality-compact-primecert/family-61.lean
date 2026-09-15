/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import PrimeCert
public section
set_option maxRecDepth 65536
set_option exponentiation.threshold 512
namespace PrimeCert.Comparator.Bit61
theorem result : Nat.Prime 1945555039024054273 := prime_cert%
  [small {2},
   pock (1945555039024054273, 5, 2 ^ 56)]
end PrimeCert.Comparator.Bit61
