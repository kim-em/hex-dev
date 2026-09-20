/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Elab

public section

namespace Hex.PrimalityProducer

/-- A separate-module producer: no new semantics in the checker. -/
def fermat (k : Nat) : Hex.Nat.PrimeCert :=
  .pock (2 ^ (2 ^ k) + 1) [(3, 2 ^ k - 1, .small 2)]

/-- Registration uses Lean's existing macro registry, with an explicit call site.
For composite Fermat numbers the resulting certificate fails the checker. -/
macro "fermat_cert% " k:num : term => `(fermat $k)

/-- A surface-language prototype with natural (positive) exponents and named
intermediate certificates. Factor ordering remains explicit in the source. -/
macro "power_cert% " n:num " from " q:term:max " ^ " e:num &"base" a:num : term => do
  if e.getNat == 0 then Lean.Macro.throwErrorAt e "certificate exponent must be positive"
  let pred := Lean.Syntax.mkNumLit (toString (e.getNat - 1))
  `(Hex.Nat.PrimeCert.pock $n [($a, $pred, $q)])

/-- Named intermediate primes in the certificate emitted for Curve25519. -/
def curve : Hex.Nat.PrimeCert :=
  let two : Hex.Nat.PrimeCert := .small 2
  let q := Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
    [(5, 2, two), (2, 0, .small 223), (2, 0, .small 4153)]
  let r := Hex.Nat.PrimeCert.pock3
    74058212732561358302231226437062788676166966415465897661863160754340907
    2028478494862525422475607 22304740449229861598212 2028478494862525422475606
    [(2, 0, two), (2, 0, .small 353), (2, 0, .small 57467), (2, 0, q)]
  .pock (2 ^ 255 - 19) [(2, 0, r)]

end Hex.PrimalityProducer
