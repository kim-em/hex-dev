/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Lean

/-!
The `rebuild_luebeckConwayPolynomial?` command, which regenerates the committed
Lübeck Conway coefficient table from the cached slice of Lübeck's published
data.

The committed table stays ordinary Lean code that the kernel checks like any
other definition. This command exists so that *changing which slice is
committed* is one invocation rather than a hand edit: it reads the cache, keeps
the entries inside the requested scope, and offers the regenerated definition as
a `Try this:` replacement for the definition written immediately below it.

The emitted replacement carries the invocation that produced it, commented out
directly above the definition, so a reader can see the scope the committed table
came from and re-run it without reconstructing the arguments.

The cache itself is refreshed from Lübeck's table by
`scripts/oracle/update_luebeck_conway_cache.py`, which is the only step that
touches the network. This command reads only the committed JSON, so a rebuild is
reproducible offline and its output is a pure function of the cache and the
scope.
-/

namespace Hex.Conway.Rebuild

open Lean Elab Command

/-- One committed table row: the prime, the degree, and the Conway polynomial's
coefficients stored ascending by degree. -/
structure Entry where
  /-- The characteristic. -/
  p : Nat
  /-- The extension degree. -/
  n : Nat
  /-- Coefficients of `C(p, n)`, ascending by degree, so the last entry is the
  leading `1`. -/
  coeffs : List Nat
  deriving Inhabited

/-- Read the committed Lübeck cache and return its entries in file order.

Fails with a readable message rather than an exception when the file is absent
or does not have the shape `update_luebeck_conway_cache.py` writes, since the
usual cause is running the command from outside the package root. -/
def readCache (path : System.FilePath) : IO (Array Entry) := do
  unless ← path.pathExists do
    throw <| IO.userError
      s!"Lübeck Conway cache not found at '{path}'. \
         Run this command from the package root, or pass an explicit path with \
         `from \"…\"`. Regenerate the cache with \
         scripts/oracle/update_luebeck_conway_cache.py."
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text)
  let entries ← IO.ofExcept (json.getObjVal? "entries" >>= Json.getArr?)
  entries.mapM fun e => do
    let p ← IO.ofExcept (e.getObjVal? "p" >>= Json.getNat?)
    let n ← IO.ofExcept (e.getObjVal? "n" >>= Json.getNat?)
    let coeffsJson ← IO.ofExcept (e.getObjVal? "coeffs" >>= Json.getArr?)
    let coeffs ← coeffsJson.toList.mapM fun c => IO.ofExcept c.getNat?
    pure { p, n, coeffs }

/-- Keep the entries inside the requested scope, ordered by prime then degree so
the generated `match` reads in the same order as Lübeck's table. -/
def selectScope (entries : Array Entry) (primes : List Nat) (maxDegree : Nat) :
    Array Entry :=
  let kept := entries.filter fun e => primes.contains e.p && 1 ≤ e.n && e.n ≤ maxDegree
  kept.qsort fun a b => if a.p = b.p then a.n < b.n else a.p < b.p

/-- Render the scope back as the command that produced it, for the commented-out
line the replacement carries. -/
def renderInvocation (primes : List Nat) (maxDegree : Nat) (path : String) : String :=
  let primeList := String.intercalate ", " (primes.map toString)
  s!"rebuild_luebeckConwayPolynomial? primes [{primeList}] degrees {maxDegree} from \"{path}\""

/-- Render the regenerated coefficient table, including the commented-out
invocation above it. -/
def renderTable (entries : Array Entry) (invocation : String) : String :=
  let header :=
    "-- Regenerate this definition with the command on the next line, which\n\
     -- rewrites it from the committed Lübeck cache:\n\
     -- " ++ invocation ++ "\n\
     /-- Committed Lübeck Conway-table coefficients, stored ascending by degree. -/\n\
     def luebeckConwayCoeffs? : Nat → Nat → Option (List Nat)\n"
  let rows := entries.foldl (init := "") fun acc e =>
    let coeffs := String.intercalate ", " (e.coeffs.map toString)
    acc ++ s!"  | {e.p}, {e.n} => some [{coeffs}]\n"
  header ++ rows ++ "  | _, _ => none"

/-- Scope specification: the primes to keep and the largest degree to keep for
each of them. Degrees below the maximum that Lübeck's table happens not to list
are simply absent, so a gap in the source is tolerated rather than fatal. -/
syntax (name := rebuildLuebeck)
  "rebuild_luebeckConwayPolynomial?" &"primes" "[" num,* "]" &"degrees" num
    (&"from" str)? command : command

@[command_elab rebuildLuebeck]
def elabRebuild : CommandElab := fun stx => do
  let primeStx := stx[3].getSepArgs
  let primeScope := primeStx.toList.map fun s => s.isNatLit?.getD 0
  let maxDegree := stx[6].isNatLit?.getD 0
  let pathArg := stx[7]
  let defaultPath := "scripts/oracle/luebeck_conway_cache.json"
  let path :=
    if pathArg.isNone then defaultPath
    else pathArg[0][1].isStrLit?.getD defaultPath
  let inner := stx[8]

  -- The command is only meaningful in front of the definition it regenerates;
  -- checking that here turns a misplaced invocation into an error at the
  -- invocation rather than a silently ignored suggestion.
  let isTarget :=
    inner.find? (fun s => s.isOfKind ``Lean.Parser.Command.declId
      && s[0].getId.eraseMacroScopes == `luebeckConwayCoeffs?) |>.isSome
  unless isTarget do
    throwErrorAt inner
      "rebuild_luebeckConwayPolynomial? must be followed by the definition of \
       `luebeckConwayCoeffs?` that it regenerates; found a different command."

  -- Elaborate the committed definition first, so the file still means what it
  -- says while a rebuild is only ever offered as a suggestion.
  elabCommand inner

  if primeScope.isEmpty then
    throwError "rebuild_luebeckConwayPolynomial? needs at least one prime in its scope."

  let entries ← readCache path
  let selected := selectScope entries primeScope maxDegree
  if selected.isEmpty then
    throwError "the requested scope selects no entries from '{path}'."
  let invocation := renderInvocation primeScope maxDegree path
  let replacement := renderTable selected invocation
  liftTermElabM do
    Lean.Meta.Tactic.TryThis.addSuggestion stx
      { suggestion := .string replacement
        postInfo? := some
          s!"\n\n{selected.size} entries for primes \
             {String.intercalate ", " (primeScope.map toString)} through degree {maxDegree}." }

end Hex.Conway.Rebuild
