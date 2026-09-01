/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor

namespace Hex.IntFactor.ProofProbe

open Hex.Nat

def cert61 : PrimeCert :=
  .pock 1945555039024054273
    [(891154892214722695, 55, .small 2),
     (110189291828549774, 2, .small 3)]

def replayCerts : List PrimeCert :=
  [.small 2, .small 3, .small 5, .small 7, .small 11,
   .small 13, .small 17, .small 19, .small 23, cert61]

def replayFactors (count : Nat) : List PrimePower :=
  (replayCerts.take count).map fun cert => ⟨1, cert⟩

def replayCase (count : Nat) : Factorization :=
  let factors := replayFactors count
  ⟨(factors.map (·.prime)).prod, factors⟩

end Hex.IntFactor.ProofProbe
