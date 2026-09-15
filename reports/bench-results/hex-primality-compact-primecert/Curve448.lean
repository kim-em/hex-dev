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
theorem result : Nat.Prime (2 ^ 448 - 2 ^ 224 - 1) := prime_cert%
  [small {2; 3; 5; 7; 11; 151; 223; 641},
   pock3 (3402277943, 5, 3, 2 * 7 * 151),
   pock (1469495262398780123809, 3, 223 * 3402277943),
   pock (2531, 2, 5 * 11),
   pock3 (167773885276849215533569, 17, 7, 2 ^ 9 * 7 ^ 2 * 2531),
   pock3 (726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439, 7, 3, 2 * 641 * 1469495262398780123809 * 167773885276849215533569)]
