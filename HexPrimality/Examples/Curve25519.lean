/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert

public section

/-!
A compact Pocklington and Brillhart–Lehmer–Selfridge certificate for the
Curve25519 prime `2^255 - 19`. Every child is checked recursively.
-/

namespace Hex.Nat

private def curve25519Cert : PrimeCert :=
  .pock 57896044618658097711785492504343953926634992332820282019728792003956564819949 [
    (2, 0,
      .pock3 74058212732561358302231226437062788676166966415465897661863160754340907
        2028478494862525422475607 22304740449229861598212 2028478494862525422475606 [
        (2, 0, .small 2),
        (2, 0, .small 353),
        (2, 0, .small 57467),
        (2, 0,
          .pock3 31757755568855353 4028945 289 4028944 [
            (5, 2, .small 2),
            (2, 0, .small 223),
            (2, 0, .small 4153)])])]

/-- On the shared AMD EPYC 9455 host with Lean 4.35.0-rc3, dependencies built,
and CPU 12 leased automatically, a fresh `lake build +HexPrimality.Examples.Curve25519`
reported 679 ms for module elaboration and kernel checking, and 4.505 seconds
of total wall time. These are host-specific observations, not isolated kernel CPU time. -/
theorem curve25519_prime :
    Prime (2 ^ 255 - 19) := by
  exact prime_of_checkPrimeAt (c := curve25519Cert) (by decide +kernel)

/-- info: 'Hex.Nat.curve25519_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms curve25519_prime

end Hex.Nat
