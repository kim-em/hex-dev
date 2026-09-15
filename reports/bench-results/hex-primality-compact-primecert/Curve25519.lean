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
theorem result : Nat.Prime (2 ^ 255 - 19) := prime_cert%
  [small {2; 3; 173; 223; 353; 487},
   pock (57467, 2, 487),
   pock (4153, 2, 173),
   pock3 (31757755568855353, 5, 3, 2 ^ 3 * 223 * 4153),
   pock3 (74058212732561358302231226437062788676166966415465897661863160754340907, 2, 3, 2 * 353 * 57467 * 31757755568855353),
   pock (57896044618658097711785492504343953926634992332820282019728792003956564819949, 2, 74058212732561358302231226437062788676166966415465897661863160754340907)]
