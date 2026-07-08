/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Hex.BenchOracle.Flint
import Lean.Data.Json

/-!
# Warm factorization service for the cross-system benchmark suite

A persistent process speaking the suite line protocol (identical to the verified
Isabelle comparator `scripts/oracle/bz-isabelle/Main.hs`):

* request (one line): `{"coeffs":[c0,c1,...]}` — integer coefficients, **ascending**
  degree order.
* reply (one line): `{"ok":true,"result":{"scalar":s,"factors":[{"coeffs":[...],
  "multiplicity":m},...]}}` on success, `{"ok":true,"result":null}` when the
  selected entry declines (counted as unsolved on the charts, deliberately not
  distinguished from a timeout), or `{"ok":false,"error":"..."}` on a malformed
  request.

The `--entry` flag selects which library entry answers each request:

* `factor` — the production cost-based hybrid (`Hex.ZPoly.factorize`); never declines.
* `factorLattice` — the van Hoeij CLD lattice tier (`Hex.factorLattice`).
* `factorClassicalNoDecline` — classical recombination run to completion or
  cutoff (`Hex.factorClassicalNoDecline`), exposing the classical exponential
  wall.

This is a comparator driver, not a hex-internal benchmark harness: it emits raw
timings for the external orchestrator, keeping the one-harness rule intact.
-/

open Lean (Json JsonNumber)
open Hex
open Hex.BenchOracle.Flint (intsToJson)

namespace HexBench.FactorService

/-- Which library entry answers each request. -/
inductive Entry where
  | factor
  | factorLattice
  | factorClassicalNoDecline
deriving Repr, DecidableEq

def Entry.ofString? : String → Option Entry
  | "factor" => some .factor
  | "factorLattice" => some .factorLattice
  | "factorClassicalNoDecline" => some .factorClassicalNoDecline
  | _ => none

/-- Dispatch to the selected entry. `none` means the entry declined; the
production `factor` never declines (it wraps its total `Factorization`). -/
def Entry.run : Entry → ZPoly → Option Factorization
  | .factor, f => some (Hex.ZPoly.factorize f)
  | .factorLattice, f => Hex.factorLattice f
  | .factorClassicalNoDecline, f => Hex.factorClassicalNoDecline f

/-- Parse a request line into its ascending coefficient list. -/
def parseCoeffs (line : String) : Except String (List Int) := do
  let j ← Json.parse line
  let cj ← j.getObjVal? "coeffs"
  let arr ← cj.getArr?
  arr.toList.mapM Json.getInt?

/-- Encode a total factorization as the protocol `result` object. -/
def factorizationToJson (φ : Factorization) : Json :=
  Json.mkObj
    [ ("scalar", Json.num (JsonNumber.fromInt φ.scalar)),
      ("factors",
        Json.arr (φ.factors.map fun (p, m) =>
          Json.mkObj
            [ ("coeffs", intsToJson p.toArray.toList),
              ("multiplicity", Json.num (JsonNumber.fromInt (Int.ofNat m))) ])) ]

def replyOk (result : Json) : Json :=
  Json.mkObj [("ok", Json.bool true), ("result", result)]

def replyDecline : Json :=
  Json.mkObj [("ok", Json.bool true), ("result", Json.null)]

def replyError (msg : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str msg)]

/-- Answer one request line (pure: factoring is total, so no exception path). -/
def handleLine (entry : Entry) (line : String) : Json :=
  match parseCoeffs line with
  | .error msg =>
      replyError s!"expected JSON object with integer array field coeffs: {msg}"
  | .ok coeffs =>
      let f := DensePoly.ofCoeffs coeffs.toArray
      match entry.run f with
      | some φ => replyOk (factorizationToJson φ)
      | none => replyDecline

partial def runLoop (entry : Entry) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then
      return ()  -- EOF: getLine yields "" only at end of stream
    else
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty then
        loop  -- skip blank keep-alive lines
      else
        stdout.putStrLn (handleLine entry trimmed).compress
        stdout.flush
        loop
  loop

/-- `--entry <name>`; defaults to `factor`. -/
def parseEntryArg : List String → String
  | "--entry" :: v :: _ => v
  | _ :: rest => parseEntryArg rest
  | [] => "factor"

def main (args : List String) : IO Unit := do
  let entryName := parseEntryArg args
  match Entry.ofString? entryName with
  | none =>
      throw <| IO.userError
        s!"unknown --entry {entryName}; expected factor|factorLattice|factorClassicalNoDecline"
  | some entry => runLoop entry

end HexBench.FactorService

def main (args : List String) : IO Unit :=
  HexBench.FactorService.main args
