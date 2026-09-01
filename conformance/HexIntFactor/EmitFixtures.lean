/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexIntFactor

/-! Deterministic JSONL fixtures for integer factorization. -/

open Hex.Nat
open Hex.Conformance.Emit

private def lib := "HexIntFactor"

private def quote (s : String) : String := "\"" ++ s ++ "\""

private def emitFixture (kind case fields : String) : IO Unit := do
  let line := "{\"kind\":" ++ quote kind ++ ",\"lib\":" ++ quote lib ++
    ",\"case\":" ++ quote case ++ fields ++ "}\n"
  match (← IO.getEnv "HEX_FIXTURE_OUTPUT") with
  | none => IO.print line
  | some path =>
      let handle ← IO.FS.Handle.mk path IO.FS.Mode.append
      handle.putStr line

private def powersJson (entries : List PrimePower) : String :=
  "[" ++ String.intercalate "," (entries.map fun e =>
    "[" ++ toString e.prime ++ "," ++ toString e.exponent ++ "]") ++ "]"

private def natsJson (values : Array Nat) : String :=
  "[" ++ String.intercalate "," (values.toList.map toString) ++ "]"

private def rejected (context : String) : IO α :=
  throw <| IO.userError (context ++ ": factorization candidate rejected")

private def factorJson (n : Nat) : IO String :=
  match factor? n (Hex.Rand.ofSeed n) with
  | .ok (F, _) => pure (powersJson F.raw.factors)
  | .error f => match f.stop with
    | .zero => pure (quote "refused")
    | .incomplete => pure "null"
    | .rejected => rejected ("factor/" ++ toString n)

private def partsJson (parts : List CyclotomicPart) : String :=
  "[" ++ String.intercalate "," (parts.map fun p =>
    "[" ++ toString p.index ++ "," ++ toString p.value ++ "]") ++ "]"

private def emitFactor (tag : String) (n : Nat) : IO Unit := do
  let case := "factor/" ++ tag
  emitFixture "factor" case (",\"n\":" ++ toString n)
  emitResult lib case "factor" (← factorJson n)

private def emitDivisorFns (tag : String) (n : Nat) : IO Unit := do
  let case := "divisorfn/" ++ tag
  emitFixture "divisorfn" case (",\"n\":" ++ toString n)
  let value ← match factor? n (Hex.Rand.ofSeed n) with
    | .error failure => match failure.stop with
      | .rejected => rejected case
      | .zero | .incomplete => pure "null"
    | .ok (F, _) =>
        pure <| "{\"divisors\":" ++ natsJson (divisors F) ++
        ",\"tau\":" ++ toString (numDivisors F) ++
        ",\"sigma0\":" ++ toString (sigma F 0) ++
        ",\"sigma1\":" ++ toString (sigma F 1) ++
        ",\"sigma2\":" ++ toString (sigma F 2) ++
        ",\"phi\":" ++ toString (totient F) ++
        ",\"rad\":" ++ toString (radical F) ++
        ",\"sqfpart\":" ++ toString (squarefreePart F) ++
        ",\"sqdiv\":" ++ toString (squareDivisor F) ++ "}"
  emitResult lib case "divisorfn" value

private def emitOrder (tag : String) (a n : Nat) : IO Unit := do
  let case := "order/" ++ tag
  emitFixture "order" case
    (",\"base\":" ++ toString a ++ ",\"modulus\":" ++ toString n)
  emitResult lib case "order" (toString (orderOf a n))

private def signName : Sign → String | .minus => "minus" | .plus => "plus"

private def emitCyclotomicAs (family : String) (b n : Nat) (sign : Sign) : IO Unit := do
  let case := "cyclotomic/" ++ family ++ "/" ++ toString b ++ "/" ++
    toString n ++ "/" ++ signName sign
  emitFixture "cyclotomic" case
    (",\"b\":" ++ toString b ++ ",\"n\":" ++ toString n ++
      ",\"sign\":" ++ quote (signName sign))
  emitResult lib case "cyclotomic"
    (match cyclotomicSplit? b n sign with | some parts => partsJson parts | none => "null")

private def emitCyclotomic (b n : Nat) (sign : Sign) : IO Unit :=
  emitCyclotomicAs "grid" b n sign

private def primesBelowHundred : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
   53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private def primePowersBelowHundred : List Nat :=
  [4, 8, 16, 32, 64, 9, 27, 81, 25, 49]

private def factorCases : List (String × Nat) :=
  [("edge/zero", 0), ("edge/one", 1),
   ("perfect/2pow20", 2 ^ 20), ("perfect/3pow13", 3 ^ 13),
   ("perfect/1000003sq", 1000003 ^ 2), ("perfect/composite", (6 ^ 5) ^ 3),
   ("balanced/32", 65521 * 65519),
   ("balanced/48", 16777213 * 16777199),
   ("balanced/64", 4294967291 * 4294967279)]

private def conwayCases : List (Nat × Nat) :=
  (List.range 8 |>.map (fun i => (2, i + 1))) ++
  [3, 5, 7, 11, 13].flatMap fun p =>
    List.range 6 |>.map fun i => (p, i + 1)

def main : IO Unit := do
  for (tag, n) in factorCases do emitFactor tag n
  for p in primesBelowHundred do emitFactor ("below100/" ++ toString p) p
  for n in primePowersBelowHundred do emitFactor ("below100/" ++ toString n) n
  for n in [1, 2, 4, 12, 72, 360, 248832, 1296000] do
    emitDivisorFns (toString n) n
  emitOrder "primitive/3mod7" 3 7
  emitOrder "nonprimitive/2mod7" 2 7
  emitOrder "primepower/2mod9" 2 9
  emitOrder "noncyclic/5mod8" 5 8
  emitOrder "unreduced/10mod7" 10 7
  for b in [2, 3, 5, 7, 10] do
    for i in List.range 32 do
      emitCyclotomic b (i + 1) .minus
      emitCyclotomic b (i + 1) .plus
  for (p, n) in conwayCases do
    emitCyclotomicAs "conway" p n .minus
