/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Lean

public section

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
meta def readCache (path : System.FilePath) : IO (Array Entry) := do
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
the generated `match` reads in the same order as Lübeck's table.

The scope gives a maximum degree per prime rather than one maximum for all of
them, matching the `SLICE` in `scripts/oracle/update_luebeck_conway_cache.py`.
The proof cost of an entry grows with both the prime and the degree, so a
uniform bound would either stop the small primes short of what the budget
affords or push the large ones past it. -/
meta def selectScope (entries : Array Entry) (scope : List (Nat × Nat)) : Array Entry :=
  let kept := entries.filter fun e =>
    match scope.find? (fun s => s.1 = e.p) with
    | some (_, maxDegree) => 1 ≤ e.n && e.n ≤ maxDegree
    | none => false
  kept.qsort fun a b => if a.p = b.p then a.n < b.n else a.p < b.p

/-- Render the scope back as the command that produced it, for the commented-out
line the replacement carries. -/
meta def renderInvocation (scope : List (Nat × Nat)) (path : String) : String :=
  let pairs := String.intercalate ", " (scope.map fun s => s!"{s.1}:{s.2}")
  s!"rebuild_luebeckConwayPolynomial? scope [{pairs}] from \"{path}\""

/-- Render the regenerated coefficient table, including the commented-out
invocation above it. -/
meta def renderTable (entries : Array Entry) (invocation : String) : String :=
  let header :=
    "-- Regenerate this definition with the command on the next line, which\n\
     -- rewrites it from the committed Lübeck cache:\n\
     -- " ++ invocation ++ "\n\
     /-- Committed Lübeck Conway-table coefficients, stored ascending by degree. -/\n\
     @[expose]\n\
     def luebeckConwayCoeffs? : Nat → Nat → Option (List Nat)\n"
  let rows := entries.foldl (init := "") fun acc e =>
    let coeffs := String.intercalate ", " (e.coeffs.map toString)
    acc ++ s!"  | {e.p}, {e.n} => some [{coeffs}]\n"
  header ++ rows ++ "  | _, _ => none"

/-- One scope entry, written `p:maxDegree`. -/
syntax scopeEntry := num ":" num

/-- Scope specification: a maximum degree per prime, written
`scope [2:8, 3:6]`. Degrees below the maximum that Lübeck's table happens not to
list are simply absent, so a gap in the source is tolerated rather than fatal. -/
syntax (name := rebuildLuebeck)
  "rebuild_luebeckConwayPolynomial?" &"scope" "[" scopeEntry,* "]"
    (&"from" str)? command : command

@[command_elab rebuildLuebeck]
meta def elabRebuild : CommandElab := fun stx => do
  let scope := stx[3].getSepArgs.toList.map fun s =>
    (s[0].isNatLit?.getD 0, s[2].isNatLit?.getD 0)
  let pathArg := stx[5]
  let defaultPath := "scripts/oracle/luebeck_conway_cache.json"
  let path :=
    if pathArg.isNone then defaultPath
    else pathArg[0][1].isStrLit?.getD defaultPath
  let inner := stx[6]

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

  if scope.isEmpty then
    throwError "rebuild_luebeckConwayPolynomial? needs at least one prime in its scope."

  -- A scope is a claim about what the committed table should contain, so a
  -- claim that cannot mean what it appears to is rejected rather than
  -- silently resolved. `selectScope` takes the first match for a prime, so a
  -- repeated prime would quietly drop the second bound.
  let primes := scope.map Prod.fst
  for prime in primes do
    if (primes.filter (· = prime)).length > 1 then
      throwError "prime {prime} appears more than once in the scope; \
                  give each prime a single maximum degree."
  for (prime, maxDegree) in scope do
    if maxDegree = 0 then
      throwError "prime {prime} has maximum degree 0, which selects nothing; \
                  drop it from the scope instead."

  let entries ← readCache path
  for (prime, _) in scope do
    if !entries.any (fun e => e.p = prime) then
      throwError "the cache at '{path}' has no rows for prime {prime}; \
                  widen the cache or drop the prime from the scope."
  let selected := selectScope entries scope
  if selected.isEmpty then
    throwError "the requested scope selects no entries from '{path}'."
  let invocation := renderInvocation scope path
  let replacement := renderTable selected invocation
  liftTermElabM do
    Lean.Meta.Tactic.TryThis.addSuggestion stx
      { suggestion := .string replacement
        postInfo? := some
          s!"\n\n{selected.size} entries over scope \
             {String.intercalate ", " (scope.map fun s => s!"{s.1}:{s.2}")}." }

end Hex.Conway.Rebuild
