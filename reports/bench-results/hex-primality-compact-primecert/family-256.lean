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
namespace PrimeCert.Comparator.Bit256
theorem result : Nat.Prime
    93628759656736142393278101159368737990730026663232799828780155818898507169793 := prime_cert%
  [small {2},
   pock (93628759656736142393278101159368737990730026663232799828780155818898507169793, 5, 2 ^ 248)]
end PrimeCert.Comparator.Bit256
