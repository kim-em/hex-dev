/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Elab
public meta import HexPrimality.Elab

public section

namespace Hex.PrimalityCurveProbe

def input : Nat := 2 ^ 255 - 19

theorem result : Hex.Nat.Prime (2 ^ 255 - 19) :=
  Hex.Nat.prime_of_checkPrimeAt (c := .pock 57896044618658097711785492504343953926634992332820282019728792003956564819949 [
    (2, 0,
      .pock 74058212732561358302231226437062788676166966415465897661863160754340907 [
        (2, 0, .small 2), (2, 0, .small 3),
        (2, 0,
          .pock 75445702479781427272750846543864801 [
            (2, 0, .small 75707),
            (2, 0,
              .pock 1919519569386763 [
                (2, 0, .small 127),
                (2, 0,
                  .pock 8574133 [
                    (2, 0, .small 103), (2, 0, .small 991)])])])])]) (by decide +kernel)
#print axioms result

end Hex.PrimalityCurveProbe
