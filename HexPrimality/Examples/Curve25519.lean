/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality

public section

/-!
A compact Pocklington certificate for the Curve25519 prime `2^255 - 19`.
Every witness base is `2`; the remaining numbers are subjects of child
certificates, not trusted primality assumptions.
-/

namespace Hex.Nat

private def curve25519Cert : PrimeCert :=
  .pock 57896044618658097711785492504343953926634992332820282019728792003956564819949 [
    (2, 0,
      .pock 74058212732561358302231226437062788676166966415465897661863160754340907 [
        (2, 0, .small 2),
        (2, 0, .small 3),
        (2, 0,
          .pock 75445702479781427272750846543864801 [
            (2, 0, .small 75707),
            (2, 0,
              .pock 1919519569386763 [
                (2, 0, .small 127),
                (2, 0,
                  .pock 8574133 [
                    (2, 0, .small 103),
                    (2, 0, .small 991)])])])])]

/-- On this shared AMD EPYC 9455 host with Lean 4.34.0-rc2 and dependencies
already built, `lake build HexPrimality.Examples.Curve25519` reported 25 seconds
for this module's kernel replay; the enclosing shell measured 29.578 seconds
of wall-clock time. These are host-specific observations. -/
theorem curve25519_prime :
    Prime (2 ^ 255 - 19) := by
  exact prime_of_checkPrimeAt (c := curve25519Cert) (by decide +kernel)

end Hex.Nat
