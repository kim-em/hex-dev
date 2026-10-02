/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Basic

public section

namespace Hex.SignDet.Codec
open Lean

variable {E Ctx : Type} [Zero E] [DecidableEq E]

def remainder (value : ValueCodec E) (s : RemainderStep E) : Json :=
  .arr #[value.encode s.leftScale, poly value s.quotient, value.encode s.rightScale]

def readRemainder (value : ValueCodec E) (j : Json) : Except String (RemainderStep E) := do
  let a ← tuple 3 j
  return ⟨← value.decode a[0], ← readPoly value a[1], ← value.decode a[2]⟩

def terminal (value : ValueCodec E) (t : E × DensePoly E) : Json :=
  .arr #[value.encode t.1, poly value t.2]

def readTerminal (value : ValueCodec E) (j : Json) : Except String (E × DensePoly E) := do
  let a ← tuple 2 j
  return (← value.decode a[0], ← readPoly value a[1])

def chain (value : ValueCodec E) (c : SignedRemainderChain E) : Json :=
  .arr #[array (poly value) c.chain, toJson c.degrees, remainder value c.initial,
    array (remainder value) c.steps, option (terminal value) c.terminal]

def readChain (value : ValueCodec E) (j : Json) : Except String (SignedRemainderChain E) := do
  let a ← tuple 5 j
  return ⟨← readArray (readPoly value) a[0], ← fromJson? a[1],
    ← readRemainder value a[2], ← readArray (readRemainder value) a[3],
    ← readOption (readTerminal value) a[4]⟩

/-- Every literal Tarski field is serialized, including both witnesses and
all supplied endpoint signs and variation counts. -/
def tarski (value : ValueCodec E) (context : ValueCodec Ctx)
    (c : TarskiCertificate E E Ctx) : Json :=
  .arr #[context.encode c.context, poly value c.head, poly value c.queryPoly,
    endpoint value c.lower, endpoint value c.upper, chain value c.squarefree,
    chain value c.remainders, toJson c.lowerSigns, toJson c.upperSigns,
    toJson c.lowerVariations, toJson c.upperVariations, toJson c.value]

def readTarski (value : ValueCodec E) (context : ValueCodec Ctx) (j : Json) :
    Except String (TarskiCertificate E E Ctx) := do
  let a ← tuple 12 j
  return ⟨← context.decode a[0], ← readPoly value a[1], ← readPoly value a[2],
    ← readEndpoint value a[3], ← readEndpoint value a[4], ← readChain value a[5],
    ← readChain value a[6], ← fromJson? a[7], ← fromJson? a[8],
    ← fromJson? a[9], ← fromJson? a[10], ← fromJson? a[11]⟩

def reductionStep (value : ValueCodec E) (s : ReductionStep E) : Json :=
  .arr #[toJson s.index, poly value s.next, remainder value s.witness]

def readReductionStep (value : ValueCodec E) (arity : Nat) (j : Json) :
    Except String (ReductionStep E) := do
  let a ← tuple 3 j
  let i ← index arity a[0]
  return ⟨i.val, ← readPoly value a[1], ← readRemainder value a[2]⟩

def reduction (value : ValueCodec E) (r : Reduction E) : Json :=
  .arr #[list (reductionStep value) r.steps, poly value r.result]

def readReduction (value : ValueCodec E) (arity : Nat) (j : Json) :
    Except String (Reduction E) := do
  let a ← tuple 2 j
  return ⟨← readList (readReductionStep value arity) a[0], ← readPoly value a[1]⟩

def preparation (value : ValueCodec E) (r : QueryReduction E) : Json :=
  list (reductionStep value) r.steps

def readPreparation (value : ValueCodec E) (arity : Nat) (j : Json) :
    Except String (QueryReduction E) := do
  return ⟨← readList (readReductionStep value arity) j⟩

end Hex.SignDet.Codec
