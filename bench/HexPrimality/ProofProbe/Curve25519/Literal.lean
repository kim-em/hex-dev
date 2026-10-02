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

def certificate : Hex.Nat.PrimeCert :=
  Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])]

end Hex.PrimalityCurveProbe
