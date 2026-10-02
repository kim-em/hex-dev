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
namespace PrimeCert.Comparator.Bit123
theorem result : Nat.Prime 9304595970494411110326649421962412033 := prime_cert%
  [small {2},
   pock (9304595970494411110326649421962412033, 3, 2 ^ 120)]
end PrimeCert.Comparator.Bit123
