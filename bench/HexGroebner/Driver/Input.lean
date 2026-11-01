/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.F4
public import Lean.Data.Json.Parser
public import Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.Groebner.Driver
open Lean

def parseTerm (j : Json) : Except String RawTerm := do
  let values ← j.getArr?
  if values.size != 2 then throw "term needs [exponents,coefficient]"
  let powers ← values[0]!.getArr? >>= fun a => a.mapM Json.getNat?
  let c ← values[1]!.getNat?
  if c ≥ 2^64 then throw "coefficient exceeds UInt64"
  return ⟨powers,c.toUInt64⟩

/-- Validate the field bound before trial primality testing; retain explicit
field and monomial-order identity in the resulting computation context. -/
def parseInput (j : Json) : Except String (Context × Array RawPolynomial) := do
  let modulus ← j.getObjValAs? Nat "p"
  if bound : modulus < 2^31 then
    if h : Hex.Nat.isPrimeTrial modulus = true then
      let field : PrimeField := ⟨modulus.toUInt64, by
        simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by omega : modulus < 2^64)] using Hex.Nat.isPrimeTrial_isPrime h, by
        simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by omega : modulus < 2^64)] using bound⟩
      let variables ← j.getObjValAs? Nat "variables"
      let order ← j.getObjValAs? String "order"
      let order ← match order with
        | "lex" => pure TermOrder.lex
        | "grlex" => pure TermOrder.grlex
        | "grevlex" => pure TermOrder.grevlex
        | _ => throw "unknown monomial order"
      let generators ← j.getObjVal? "generators" >>= Json.getArr? >>= fun a =>
        a.mapM fun p => p.getArr? >>= fun a => a.mapM parseTerm
      return (⟨field,variables,order⟩,generators)
    else throw "modulus is not prime"
  else throw "modulus must be below 2^31"

def polynomial (p : RawPolynomial) : Json := .arr (p.map fun t =>
  .arr #[toJson t.exponents,toJson t.coefficient.toNat])

def statistics (s : Statistics) : Json := Json.mkObj [
  ("work",toJson s.work),("allocatedBytes",toJson s.allocatedBytes),
  ("pairs",toJson s.pairs),("rounds",toJson s.rounds),
  ("matrixCalls",toJson s.matrixCalls),("matrixEntries",toJson s.matrixEntries),
  ("matrixRows",toJson s.matrixRows),("largestBatch",toJson s.largestBatch),
  ("peakMatrixRows",toJson s.peakMatrixRows),("peakMatrixEntries",toJson s.peakMatrixEntries),
  ("productPairs",toJson s.productPairs),("chainPairs",toJson s.chainPairs),("gmPairs",toJson s.gmPairs)]

end Hex.Groebner.Driver
