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
namespace PrimeCert.Comparator.Bit31
theorem result : Nat.Prime 2147483647 := prime_cert%
  [small {151; 331},
   pock (2147483647, 3, 151 * 331)]
end PrimeCert.Comparator.Bit31
