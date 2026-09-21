/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.SignedRemainderChain
public import HexRealRoots.Var

public section

/-! Shared endpoint adapters, domain guards, query production and literal replay. -/
namespace Hex

open scoped Hex

/-- An exact endpoint, including both infinities. -/
inductive Endpoint (E : Type u) where
  | negInf
  | finite (value : E)
  | posInf

/-- Constructor comparison is exposed for ordinary-kernel literal replay. -/
instance [DecidableEq E] : DecidableEq (Endpoint E)
  | .negInf, .negInf | .posInf, .posInf => isTrue rfl
  | .finite a, .finite b =>
    match decEq a b with
    | isTrue h => isTrue (congrArg Endpoint.finite h)
    | isFalse h => isFalse (fun he => h (Endpoint.finite.inj he))
  | .negInf, .finite _ | .negInf, .posInf | .finite _, .negInf |
    .finite _, .posInf | .posInf, .negInf | .posInf, .finite _ => isFalse (by intro h; cases h)

/-- Exact finite comparison and evaluation signs. Endpoint values may belong to
an ordered extension of the coefficient domain, as for integer/dyadic queries. -/
structure EndpointAdapter (D : Type u) (E : Type v) [Zero D] [DecidableEq D] where
  compare : E → E → Int
  evalSign : DensePoly D → E → Int

namespace Endpoint

@[expose] def lt [Zero D] [DecidableEq D] (adapter : EndpointAdapter D E) :
    Endpoint E → Endpoint E → Bool
  | .negInf, .finite _ | .negInf, .posInf | .finite _, .posInf => true
  | .finite a, .finite b => adapter.compare a b < 0
  | _, _ => false

@[expose] def signAt [Zero D] [DecidableEq D]
    (sign : D → Int) (adapter : EndpointAdapter D E) (p : DensePoly D) : Endpoint E → Int
  | .negInf => sign p.leadingCoeff * (if p.natDegree % 2 = 1 then -1 else 1)
  | .finite a => adapter.evalSign p a
  | .posInf => sign p.leadingCoeff

@[expose] def rootFree [Zero D] [DecidableEq D] (adapter : EndpointAdapter D E)
    (p : DensePoly D) : Endpoint E → Bool
  | .finite a => adapter.evalSign p a != 0
  | _ => true

end Endpoint

/-- Literal inputs/context and finite query evidence. `Ctx` is the caller's full
literal context data, not a hash. A derivative-chain replay proves the
squarefree guard without running a gcd search in the checker. -/
structure QueryReplay (D : Type u) (E : Type v) (Ctx : Type w) [Zero D] [DecidableEq D] where
  context : Ctx
  head : DensePoly D
  queryPoly : DensePoly D
  lower : Endpoint E
  upper : Endpoint E
  squarefree : SignedRemainderChain D
  remainders : SignedRemainderChain D
  lowerSigns : Array Int
  upperSigns : Array Int
  lowerVariations : Nat
  upperVariations : Nat
  value : Int

namespace QueryReplay

variable {D : Type u} {E : Type v} {Ctx : Type w}
variable [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]

/-- Exact signs of a literal chain at a finite or infinite endpoint. -/
@[expose] def signs (sign : D → Int) (adapter : EndpointAdapter D E)
    (chain : Array (DensePoly D)) (endpoint : Endpoint E) : Array Int :=
  Hex.Array.map' (fun p => endpoint.signAt sign adapter p) chain

/-- Nonzero input, strictly ordered endpoints and finite endpoint nonvanishing.
These guards precede all constant and zero-query shortcuts. -/
@[expose] def endpointGuards (adapter : EndpointAdapter D E) (p : DensePoly D)
    (a b : Endpoint E) : Bool :=
  !p.isZero && a.lt adapter b && a.rootFree adapter p && b.rootFree adapter p

/-- A nonzero constant terminal gcd is the squarefree criterion; its stored
leading coefficient need not be literal one. -/
@[expose] def constantTail (cert : SignedRemainderChain D) : Bool :=
  (cert.chain.getD (cert.chain.size - 1) 0).size == 1

/-- Attach exact endpoint signs and variations to supplied producer chains.
This is shared by ordinary and prepared-domain frontends. -/
@[expose] def fromChains (sign : D → Int) (adapter : EndpointAdapter D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E)
    (squarefree remainders : SignedRemainderChain D) : QueryReplay D E Ctx :=
  let lowerSigns := signs sign adapter remainders.chain a
  let upperSigns := signs sign adapter remainders.chain b
  let lowerVariations := signVar lowerSigns.toList
  let upperVariations := signVar upperSigns.toList
  { context := context
    head := p
    queryPoly := f
    lower := a
    upper := b
    squarefree := squarefree
    remainders := remainders
    lowerSigns := lowerSigns
    upperSigns := upperSigns
    lowerVariations := lowerVariations
    upperVariations := upperVariations
    value := (lowerVariations : Int) - upperVariations }

/-- Produce a finite query certificate using the one shared signed-remainder
kernel. The normalizer is a total positive-content backend; field callers may
use `SignedRemainderChain.normalizeId`. No root search or isolation is performed. -/
@[expose] def certify [Neg D] (sign : D → Int) (adapter : EndpointAdapter D E)
    (normalize : DensePoly D → D × DensePoly D) (context : Ctx)
    (p f : DensePoly D) (a b : Endpoint E) : Option (QueryReplay D E Ctx) :=
  if !endpointGuards adapter p a b then none else
    let squarefree := SignedRemainderChain.build sign normalize p 1
    if !constantTail squarefree then none else
      some (fromChains sign adapter context p f a b squarefree (SignedRemainderChain.build sign normalize p f))

/-- The query value of the shared producer. Negative values are retained. -/
@[expose] def query [Neg D] (sign : D → Int) (adapter : EndpointAdapter D E)
    (normalize : DensePoly D → D × DensePoly D)
    (p f : DensePoly D) (a b : Endpoint E) : Option Int :=
  (certify sign adapter normalize () p f a b).map QueryReplay.value

/-- Check full literal bindings, both chain replays, exact endpoint signs and
variations. All arithmetic equations are zero-difference checks; all input and
context bindings remain literal equalities. The checker never calls a producer. -/
@[expose] def check [DecidableEq E] [DecidableEq Ctx]
    (sign : D → Int) (adapter : EndpointAdapter D E) (context : Ctx)
    (p f : DensePoly D) (a b : Endpoint E) (value : Int) (cert : QueryReplay D E Ctx) : Bool :=
  decide (cert.context = context) && decide (cert.head = p) && decide (cert.queryPoly = f) &&
    decide (cert.lower = a) && decide (cert.upper = b) && decide (cert.value = value) &&
    endpointGuards adapter p a b &&
    SignedRemainderChain.check sign p 1 cert.squarefree && constantTail cert.squarefree &&
    SignedRemainderChain.check sign p f cert.remainders &&
    decide (cert.lowerSigns = signs sign adapter cert.remainders.chain a) &&
    decide (cert.upperSigns = signs sign adapter cert.remainders.chain b) &&
    cert.lowerSigns.all (fun s => -1 ≤ s && s ≤ 1) &&
    cert.upperSigns.all (fun s => -1 ≤ s && s ≤ 1) &&
    decide (cert.lowerVariations = signVar cert.lowerSigns.toList) &&
    decide (cert.upperVariations = signVar cert.upperSigns.toList) &&
    decide (value = (cert.lowerVariations : Int) - cert.upperVariations)

end QueryReplay

namespace ZPoly

/-- Positive integer content normalization; the producer calls it only on a
nonzero remainder. It never changes the input head or makes entries monic. -/
@[expose] def queryNormalize (p : ZPoly) : Int × ZPoly :=
  (DensePoly.content p, DensePoly.primitivePart p)

/-- Exact dyadic endpoints for integer coefficients. -/
@[expose] def queryAdapter : EndpointAdapter Int Dyadic where
  compare a b := dyadicSign (a - b)
  evalSign p a := dyadicSign (ZPoly.evalDyadic p a)

/-- The signed sum at roots in the open interval, with nonzero squarefree input
and root-free endpoints. Invalid mathematical inputs return `none`. -/
@[expose] def tarskiQuery (p f : ZPoly) (I : DyadicInterval) : Option Int :=
  QueryReplay.query Int.sign queryAdapter queryNormalize p f (.finite I.lower) (.finite I.upper)

end ZPoly

/-- The integer/dyadic specialization of the shared literal replay. -/
abbrev TarskiReplay := QueryReplay Int Dyadic Unit

namespace TarskiReplay

@[expose] def certify (p f : ZPoly) (I : DyadicInterval) : Option TarskiReplay :=
  QueryReplay.certify Int.sign ZPoly.queryAdapter ZPoly.queryNormalize () p f
    (.finite I.lower) (.finite I.upper)

@[expose] def check (p f : ZPoly) (I : DyadicInterval) (value : Int) (cert : TarskiReplay) : Bool :=
  QueryReplay.check Int.sign ZPoly.queryAdapter () p f (.finite I.lower) (.finite I.upper) value cert

end TarskiReplay
end Hex
