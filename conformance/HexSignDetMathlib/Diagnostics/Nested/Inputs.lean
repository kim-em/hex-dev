/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib
public import HexRationalFn
public import HexOrderedFn.Infinitesimal
public import HexSignDet.Dag
public import HexSignDet.Replay
public meta import HexRationalFn.Basic
public meta import HexRationalFn.Arithmetic
public meta import HexRationalFn.Field

public section

namespace Hex.SignDetMathlib.Diagnostics.Nested
open Hex.SignDet
open scoped Hex

/-- Literal coefficient values and the existing lawful field dictionaries. -/
structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  sign : Carrier → Int
  generator : Carrier
  square : Carrier
  doubled : Carrier

/-- At each level, supply ε·(g+ε), its square, and its double as literal
polynomials. Preparing evidence performs no coefficient multiplication. -/
@[expose] def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, Sturm.orderSign, 1, 1, 2⟩
  | depth + 1 =>
    let base := coefficients depth
    letI := base.field
    letI := base.equality
    ⟨RationalFn base.Carrier, inferInstance, inferInstance,
      OrderedFn.Infinitesimal.sign base.sign,
      RationalFn.ofPoly (DensePoly.ofCoeffs #[0, base.generator, 1]),
      RationalFn.ofPoly (DensePoly.ofCoeffs #[0, 0, base.square, base.doubled, 1]),
      RationalFn.ofPoly (DensePoly.ofCoeffs #[0, base.doubled, 2])⟩

variable {E : Type} [Lean.Grind.Field E] [DecidableEq E]

@[expose] def head : DensePoly E := DensePoly.ofCoeffs #[0, 1]

/-- Supplied linear chain: no query or remainder-chain producer is invoked. -/
@[expose] def chain (q : E) : SignedRemainderChain E := {
  chain := #[head, DensePoly.C q], degrees := #[1, 0]
  initial := ⟨1, 0, 1⟩, steps := #[], terminal := some (q, head) }

@[expose] def query (q : E) : TarskiCertificate E E Nat := {
  context := 7, head := head, queryPoly := DensePoly.C q
  lower := .negInf, upper := .posInf
  squarefree := chain 1, remainders := chain q
  lowerSigns := #[-1, 1], upperSigns := #[1, 1]
  lowerVariations := 1, upperVariations := 0, value := 1 }

@[expose] def leaf (q square : E) : Node E Nat := {
  context := 7, head := head, lower := .negInf, upper := .posInf
  queries := [DensePoly.C q], size := 3
  system := {
    rows := #v[[0], [1], [2]], columns := #v[[-1], [0], [1]]
    counts := #v[0, 0, 1], values := #v[1, 1, 1], denominator := 2
    inverse := Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]] }
  moments := #v[query 1, query q, query square]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide +kernel⟩]
    denom := 1
    adj := Matrix.identity 1 } }

@[expose] def parent (q : E) : Node E Nat := {
  context := 7, head := head, lower := .negInf, upper := .posInf
  queries := [DensePoly.C q, DensePoly.C q], size := 1
  system := {
    rows := #v[[0, 0]], columns := #v[[1, 1]], counts := #v[1], values := #v[1]
    denominator := 1, inverse := Matrix.identity 1 }
  moments := #v[query 1]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide +kernel⟩]
    denom := 1
    adj := Matrix.identity 1 } }

/-- Two parent edges refer to the same accepted leaf at this coefficient level. -/
@[expose] def graph (q square : E) : Dag E Nat :=
  ⟨#[⟨leaf q square, none⟩, ⟨parent q, some (0, 0)⟩], 1⟩

/-- Mutate the first leaf's second moment, retaining every other literal. -/
@[expose] def forge (g : Dag E Nat) : Dag E Nat :=
  {g with entries := g.entries.modify 0 fun e =>
    let moments := e.node.moments.modify 1 fun t =>
      let initial := {t.remainders.initial with leftScale := 2}
      {t with remainders := {t.remainders with initial := initial}}
    {e with node := {e.node with moments := moments}}}

/-- The ordinary graph checker on supplied coefficient values. The optional
forgery changes a positive initial scale without changing any matrix, query,
endpoint, context or reported sign. -/
@[expose] def check (depth : Nat) (stale : Bool := false)
    (forged : Bool := false) : Bool :=
  let c := coefficients depth
  letI := c.field
  letI := c.equality
  letI : NatCast c.Carrier := Lean.Grind.Semiring.natCast
  let g := graph c.generator c.square
  let g := if stale then {g with entries := g.entries.modify 0 fun e =>
    {e with node := {e.node with context := 8}}} else g
  let evidence := if forged then forge g else g
  evidence.check c.sign 7 head .negInf .posInf
    [DensePoly.C c.generator, DensePoly.C c.generator]

/-- The actual forged moment passes every chain guard before the initial
identity, fails that identity and chain replay, while the original chain passes. -/
@[expose] def scaleFailure (depth : Nat) : Bool :=
  let c := coefficients depth
  letI := c.field
  letI := c.equality
  letI : NatCast c.Carrier := Lean.Grind.Semiring.natCast
  let g := forge (graph c.generator c.square)
  match g.entries[0]? with
  | none => false
  | some entry =>
    match entry.node.moments.toArray[1]? with
    | none => false
    | some moment =>
      let cert := moment.remainders
      let p := moment.head
      let f := moment.queryPoly
      let n := cert.chain.size
      let passedGuards := !p.isZero && decide (0 < n) && decide (n ≤ p.size) &&
        decide (cert.chain[0]? = some p) &&
        decide (cert.degrees = Hex.Array.map' DensePoly.natDegree cert.chain) &&
        cert.chain.all (fun r => !r.isZero) &&
        (Array.range (n - 1)).all (fun i =>
          (cert.chain.getD (i + 1) 0).size < (cert.chain.getD i 0).size) &&
        decide (c.sign cert.initial.leftScale = 1) &&
        decide (c.sign cert.initial.rightScale = 1)
      let identity := SignedRemainderChain.subIsZero
        (DensePoly.scale cert.initial.leftScale (f * p.derivative))
        (cert.initial.quotient * p +
          DensePoly.scale cert.initial.rightScale (cert.chain.getD 1 0))
      passedGuards && !identity && !cert.check c.sign p f &&
        (query c.generator).remainders.check c.sign head (DensePoly.C c.generator)

end Hex.SignDetMathlib.Diagnostics.Nested
