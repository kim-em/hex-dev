/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZGcd.Cert

public section

/-!
Ordinary-kernel canaries for the certificate replay closure.
-/

namespace Hex

namespace ZPoly

private def kernelG : ZPoly := DensePoly.ofList [1, 1]
private def kernelL : ZPoly := DensePoly.ofList [2, 1]
private def kernelR : ZPoly := DensePoly.ofList [3, 1]
private def kernelF : ZPoly := kernelG * kernelL
private def kernelH : ZPoly := kernelG * kernelR

private def kernelCert : GcdCert :=
  { gcd := kernelG
    cofL := kernelL
    cofR := kernelR
    coprime := .constant (-1) 1 1 }

private theorem kernelCert_accepts :
    checkGcd kernelF kernelH kernelCert = true := by
  decide +kernel

private theorem corruptGcd_rejected :
    checkGcd kernelF kernelH { kernelCert with gcd := 1 } = false := by
  decide +kernel

private theorem zeroConstant_rejected :
    checkGcd kernelF kernelH
      { kernelCert with coprime := .constant (-1) 1 0 } = false := by
  decide +kernel

private theorem kernelBoundsTwo : ZMod64.Bounds 2 := by
  constructor <;> decide

private theorem kernelPrimeTwo : Hex.Nat.Prime 2 := by
  apply Hex.Nat.isPrimeTrial_isPrime
  decide

private def kernelP2 : ZMod64.Prime :=
  { m := 2, bounds := kernelBoundsTwo, prime := kernelPrimeTwo }

private def kernelModG : ZPoly := DensePoly.ofList [1, 1]
private def kernelModL : ZPoly := DensePoly.ofList [0, 1]
private def kernelModR : ZPoly := DensePoly.ofList [1, 1]
private def kernelModF : ZPoly := kernelModG * kernelModL
private def kernelModH : ZPoly := kernelModG * kernelModR

private def kernelModCert : GcdCert :=
  let p := kernelP2
  letI : ZMod64.Bounds p.m := p.bounds
  { gcd := kernelModG
    cofL := kernelModL
    cofR := kernelModR
    coprime := .modular p 1 1 }

/-- The modular constructor also stays within the ordinary-kernel replay
closure at the smallest prime. -/
private theorem kernelModCert_accepts :
    checkGcd kernelModF kernelModH kernelModCert = true := by
  decide +kernel

end ZPoly

end Hex
