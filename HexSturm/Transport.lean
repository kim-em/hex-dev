/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic
public import HexRealRoots.Map

public section
namespace Hex

/-- Clear a literal three-term identity when its three polynomial entries
are scaled by `a`, `b`, and `c`. All new scalar factors are integers; no
division or chain production is performed on the translated evidence. -/
@[expose] def RemainderStep.clearDenominators (a b c : Nat) (s : RemainderStep Rat) : RemainderStep Int where
  leftScale := (b * c * s.rightScale.den * (ZPoly.clearDenominators s.quotient).1 : Nat) * s.leftScale.num
  quotient := DensePoly.scale (a * c * s.leftScale.den * s.rightScale.den : Nat)
    (ZPoly.clearDenominators s.quotient).2
  rightScale := (a * b * s.leftScale.den * (ZPoly.clearDenominators s.quotient).1 : Nat) * s.rightScale.num

/-- Clear every polynomial and scale in a supplied literal chain. Initial
product scaling includes both the head and query clearing factors. The terminal
identity is translated from its supplied quotient, without running division. -/
@[expose] def SignedRemainderChain.clearDenominators (p : DensePoly Rat) (queryScale : Nat) (cert : SignedRemainderChain Rat) : SignedRemainderChain Int :=
  let entries := Hex.Array.map' (fun q => (ZPoly.clearDenominators q).2) cert.chain
  let factor i := (ZPoly.clearDenominators (cert.chain.getD i 0)).1
  { chain := entries
    degrees := Hex.Array.map' DensePoly.natDegree entries
    initial := RemainderStep.clearDenominators ((ZPoly.clearDenominators p).1 * queryScale)
      (ZPoly.clearDenominators p).1 (factor 1) cert.initial
    steps := Hex.Array.ofFn' fun i : Fin cert.steps.size =>
      RemainderStep.clearDenominators (factor i.val) (factor (i.val + 1)) (factor (i.val + 2)) cert.steps[i]
    terminal := cert.terminal.map fun (l, q) =>
      let s := RemainderStep.clearDenominators (factor (cert.chain.size - 2)) (factor (cert.chain.size - 1)) 1 ⟨l, q, 1⟩
      (s.leftScale, s.quotient) }

/-- Translate both supplied chains and renew exact endpoint signs and literal
input bindings. The caller supplies the dyadic interval represented by the
original rational endpoints; the full literal context is retained. -/
@[expose] def TarskiCertificate.clearDenominators {Ctx : Type u} (p g : DensePoly Rat) (I : DyadicInterval)
    (cert : TarskiCertificate Rat Rat Ctx) : TarskiCertificate Int Dyadic Ctx :=
  TarskiCertificate.fromChains Int.sign EndpointSigns.intDyadic cert.context
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 (.finite I.lower) (.finite I.upper)
    (SignedRemainderChain.clearDenominators p 1 cert.squarefree) (SignedRemainderChain.clearDenominators p (ZPoly.clearDenominators g).1 cert.remainders)

/-- Embed integer literal evidence and dyadic endpoints in the rationals,
retaining the supplied context, signs, variations and value. -/
@[expose] def TarskiCertificate.toRat {Ctx : Type u}
    (cert : TarskiCertificate Int Dyadic Ctx) : TarskiCertificate Rat Rat Ctx :=
  cert.map (fun z : Int => (z : Rat)) (fun _ => Rat.intCast_eq_zero_iff) Dyadic.toRat

end Hex
