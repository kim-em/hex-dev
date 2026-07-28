/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.DecisionCheck

public section

/-! Stable structural hashes shared by compiled and fresh-module HexRCF probes. -/

namespace Hex.RCFBench

open Hex Hex.RCF

instance : Hashable ZPoly where
  hash p := hash p.toArray

def dyadicKey : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => n * 1_000_003 + k

instance : Hashable Dyadic where
  hash x := hash (dyadicKey x)

instance : Hashable DyadicInterval where
  hash I := hash (I.lower, I.upper)

def cmpTag : Cmp → Nat
  | .lt => 0
  | .le => 1
  | .eq => 2
  | .ge => 3
  | .gt => 4
  | .ne => 5

instance : Hashable Cmp where
  hash cmp := hash (cmpTag cmp)

def formulaHash : Formula → UInt64
  | .atom atom => hash (0, atom.p, atom.cmp)
  | .tt => hash (1 : Nat)
  | .ff => hash (2 : Nat)
  | .not φ => hash (3, formulaHash φ)
  | .and φ ψ => hash (4, formulaHash φ, formulaHash ψ)
  | .or φ ψ => hash (5, formulaHash φ, formulaHash ψ)
  | .imp φ ψ => hash (6, formulaHash φ, formulaHash ψ)

instance : Hashable Formula where
  hash := formulaHash

instance : Hashable Sentence where
  hash
    | .forallReal φ => hash (0, φ)
    | .existsReal φ => hash (1, φ)
    | .forallIoc a b φ => hash (2, a, b, φ)
    | .existsIoc a b φ => hash (3, a, b, φ)

instance : Hashable SturmStep where
  hash step := hash (step.leftScale, step.quotient, step.rightScale)

instance : Hashable SturmReplay where
  hash replay := hash (replay.chain, replay.derivScale, replay.steps)

instance : Hashable CarrierCert where
  hash cert := hash (
    cert.carrier, cert.repeated, cert.derivPart, cert.factorScale,
    cert.derivScale, cert.replay)

instance : Hashable IsolationCert where
  hash cert := hash cert.intervals

instance : Hashable CommonRootCert where
  hash cert := hash (
    cert.gcd, cert.atomFactor, cert.carrierFactor, cert.atomCoeff,
    cert.carrierCoeff, cert.scale, cert.replay)

instance : Hashable SignMatrixCert where
  hash cert := hash cert.commonRoots

def rootCmpTag : Separation.RootCmp → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

instance : Hashable Separation.RootCmp where
  hash cmp := hash (rootCmpTag cmp)

instance {n : Nat} : Hashable (IocCmps n) where
  hash cert := hash (cert.lower.toArray, cert.upper.toArray)

def certificateHash : Certificate → UInt64
  | .emptyIoc => hash (0 : Nat)
  | .constants => hash (1 : Nat)
  | .noRoots data => hash (2, data.carrier, data.isolations)
  | .cells data => hash (
      3, data.carrier, data.isolations, data.signs, data.iocCmps)

instance : Hashable Certificate where
  hash := certificateHash

end Hex.RCFBench
