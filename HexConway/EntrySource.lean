/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.Irreducibility
import HexBerlekamp.CertificateSyntax
import HexPolyFp.Field
import HexConway.Table
import HexConway.Rebuild

/-!
Source generation for a single committed Conway-table entry.

Widening the committed slice means adding, for each new `(p, n)`, a polynomial
literal, its monic and degree facts, a table-hit lemma, a Rabin irreducibility
certificate, the kernel check that validates the certificate, and the
irreducibility theorem the check feeds. Of those, only the certificate is not
mechanical: it has to be computed by running the Frobenius chain and the
extended gcd, which is what `Berlekamp.buildIrreducibilityCertificate?` does in
compiled code.

`entryCertData` runs that generator for a `(p, n)` pair given its coefficients,
and `entryBlock` renders the whole per-entry block as Lean source. The
`#conway_entry_source` command prints the block for pasting into
`HexConway.Table` and `HexConway.Certificates`.

Nothing here is used by the committed library at build time. The generator
carries no soundness claim of its own: a wrong certificate makes the committed
`decide` check fail, so a bad entry cannot pass unnoticed. What the certificate
does *not* establish is that the entry is the Conway polynomial for its pair,
which is why the coefficients are read from the cache rather than supplied.

Two limits on the emitted block, both of which need a human rather than a
retry:

* It assumes the prime already has its `ZMod64.Bounds`, `Hex.Nat.Prime`, and
  `ZMod64.PrimeModulus` instances, and it refers to `supportedEntry_{p}_1` for
  the primality witness. Adding a prime the table does not yet carry, such as
  the cache's 97, 521, or 65537, needs those prerequisites written first, and
  the `n = 1` entry cannot take its witness from itself.
* It emits a fixed 8M heartbeat budget, which suits the entries committed so
  far but not all of them: four existing certificates need 20M. A generated
  block that fails to elaborate on heartbeats wants its budget raised, not its
  certificate regenerated.
-/

namespace Hex.Conway.EntrySource

open Lean Elab Command

/-- Serialized Rabin certificate: the prime, the degree, the Frobenius pow
chain, and the Bezout witness pairs, all as canonical `Nat` representatives. -/
abbrev CertData := Nat × Nat × List (List Nat) × List (List Nat × List Nat)

/-- Compute the Rabin irreducibility certificate for `C(p, n)` from its
coefficient list, serialized to plain `Nat` data.

Returns `none` when the modulus is out of `ZMod64` range, when the coefficient
list is not monic, or when the polynomial fails Rabin's test, which for a
correctly transcribed Conway entry means the transcription is wrong. -/
def entryCertData (p : Nat) (coeffs : List Nat) : Option CertData :=
  if h0 : 0 < p then
    if h1 : p < 2 ^ 31 then
      haveI : Hex.ZMod64.Bounds p := ⟨h0, h1⟩
      let f : Hex.FpPoly p :=
        Hex.FpPoly.ofCoeffs (coeffs.toArray.map (fun c => Hex.ZMod64.ofNat p c))
      -- `Monic` unfolds to this equation, so the decidable equality on residues
      -- is what makes the guard computable.
      if hm : Hex.DensePoly.leadingCoeff f = 1 then
        (Hex.Berlekamp.buildIrreducibilityCertificate? f hm).map
          Hex.CertificateSyntax.rabinCertData
      else
        none
    else
      none
  else
    none

/-- Re-check a generated certificate the way the committed `decide` will.

This is the same predicate the emitted kernel check uses, so a `true` here means
the emitted entry will elaborate, and a `false` means it will not. -/
def entryCertValidates (p : Nat) (coeffs : List Nat) (cert : CertData) : Bool :=
  if h0 : 0 < p then
    if h1 : p < 2 ^ 31 then
      haveI : Hex.ZMod64.Bounds p := ⟨h0, h1⟩
      let f : Hex.FpPoly p :=
        Hex.FpPoly.ofCoeffs (coeffs.toArray.map (fun c => Hex.ZMod64.ofNat p c))
      if hm : Hex.DensePoly.leadingCoeff f = 1 then
        let rebuilt : Hex.Berlekamp.IrreducibilityCertificate :=
          { p := p
            n := cert.2.1
            powChain := (cert.2.2.1.map fun cs =>
              Hex.FpPoly.ofCoeffs (cs.toArray.map (fun c => Hex.ZMod64.ofNat p c))).toArray
            bezout := (cert.2.2.2.map fun w =>
              { left := Hex.FpPoly.ofCoeffs (w.1.toArray.map (fun c => Hex.ZMod64.ofNat p c))
                right :=
                  Hex.FpPoly.ofCoeffs (w.2.toArray.map (fun c => Hex.ZMod64.ofNat p c)) }).toArray }
        Hex.Berlekamp.checkIrreducibilityCertificateLinearIncremental f hm rebuilt
      else
        false
    else
      false
  else
    false

/-- Render a coefficient list as the `FpPoly` literal the committed entries use:
the first residue carries the type ascription that fixes `p`, and the empty list
needs the ascription on the array instead. -/
def renderCoeffs (p : Nat) (coeffs : List Nat) : String :=
  match coeffs with
  | [] => s!"FpPoly.ofCoeffs (#[] : Array (ZMod64 {p}))"
  | c :: rest =>
      let tail := rest.foldl (init := "") fun acc d => acc ++ s!", {d}"
      s!"FpPoly.ofCoeffs #[({c} : ZMod64 {p}){tail}]"

/-- An opening brace, kept as a binding so the templates below can mention one
without colliding with string interpolation. -/
private def lb : String := "{"

/-- A closing brace, the counterpart of {name}`Hex.Conway.EntrySource.lb`. -/
private def rb : String := "}"

/-- Render the table-hit lemma, whose closing `match` needs one `rfl` arm per
stored coefficient plus a catch-all for the positions above the degree. -/
def hitLemma (p n : Nat) (coeffs : List Nat) (name : String) : String :=
  let listLit := "[" ++ String.intercalate ", " (coeffs.map toString) ++ "]"
  let arms := (List.range coeffs.length).map fun i => s!"  | {i} => rfl"
  String.intercalate "\n"
    ([ "-- Also add to HexConway/Table.lean, after the literal:",
       "",
       s!"/-- `luebeckConwayPolynomial? {p} {n}` resolves to the committed `C({p}, {n})`",
       s!"literal, rewriting the table lookup to the direct `{name}` form. -/",
       s!"@[simp, grind =] theorem luebeckConwayPolynomial?_hit_{p}_{n} :",
       s!"    luebeckConwayPolynomial? {p} {n} = some {name} := by",
       s!"  show some (luebeckConwayPolynomialOfCoeffs {p} {listLit}) = some {name}",
       "  congr 1",
       "  apply DensePoly.ext_coeff",
       "  intro k",
       s!"  rw [show DensePoly.coeff (luebeckConwayPolynomialOfCoeffs {p} {listLit}) k =",
       s!"        ({listLit}.toArray.map (fun m => ZMod64.ofNat {p} m)).getD k",
       s!"          (Zero.zero : ZMod64 {p}) from",
       "      DensePoly.coeff_ofCoeffs _ k]",
       s!"  simp [List.toArray, Array.map, DensePoly.coeff, {name}]",
       "  match k with" ] ++ arms ++ [ s!"  | _ + {coeffs.length} => rfl" ])

/-- Render the coefficient-list transports and the `SupportedEntry` witness that
`HexConway.Api` carries for each committed entry. -/
def apiBlock (p n : Nat) (coeffs : List Nat) (name : String) : String :=
  let listLit := "[" ++ String.intercalate ", " (coeffs.map toString) ++ "]"
  let ofCoeffs := s!"luebeckConwayPolynomialOfCoeffs {p} {listLit}"
  String.intercalate "\n"
    [ "-- Add to HexConway/Api.lean:",
      "",
      s!"/-- The coefficient-list constructor for the committed `C({p}, {n})` Conway entry",
      "yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and",
      "the literal's irreducibility proof. -/",
      s!"private theorem luebeckConwayPolynomialOfCoeffs_{p}_{n}_irreducible :",
      s!"    FpPoly.Irreducible ({ofCoeffs}) := by",
      s!"  have hhit := luebeckConwayPolynomial?_hit_{p}_{n}",
      s!"  change some ({ofCoeffs}) =",
      s!"    some {name} at hhit",
      s!"  have hpoly : {ofCoeffs} =",
      s!"      {name} :=",
      "    Option.some.inj hhit",
      "  rw [hpoly]",
      s!"  exact {name}_irreducible",
      "",
      s!"/-- The coefficient-list constructor for the committed `C({p}, {n})` Conway entry",
      "yields a monic `FpPoly`. -/",
      s!"private theorem luebeckConwayPolynomialOfCoeffs_{p}_{n}_monic :",
      s!"    DensePoly.Monic ({ofCoeffs}) := by",
      s!"  have hhit := luebeckConwayPolynomial?_hit_{p}_{n}",
      s!"  change some ({ofCoeffs}) =",
      s!"    some {name} at hhit",
      s!"  have hpoly : {ofCoeffs} =",
      s!"      {name} :=",
      "    Option.some.inj hhit",
      "  rw [hpoly]",
      s!"  exact {name}_monic",
      "",
      s!"/-- The current committed table supports `C({p}, {n})`. -/",
      s!"def supportedEntry_{p}_{n} : SupportedEntry {p} {n} :=",
      s!"  ⟨{name},",
      s!"    supportedEntry_{p}_1.prime,",
      s!"    luebeckConwayPolynomial?_hit_{p}_{n}⟩",
      "",
      "-- Add one arm to each aggregate case-bash, in table order:",
      s!"  · cases hcoeffs",
      s!"    exact luebeckConwayPolynomialOfCoeffs_{p}_{n}_irreducible",
      s!"  · cases hcoeffs",
      s!"    exact luebeckConwayPolynomialOfCoeffs_{p}_{n}_monic" ]

/-- Render the per-entry source block for `(p, n)`: the table-side literal with
its monic and degree lemmas, then the certificate side with its kernel check and
the irreducibility theorem. -/
def entryBlock (p n : Nat) (coeffs : List Nat) (cert : CertData) : String :=
  let name := s!"luebeckConwayPolynomial_{p}_{n}"
  let cert_ := s!"cert_{p}_{n}"
  let coeffLit :=
    match coeffs with
    | [] => s!"#[] : Array (ZMod64 {p})"
    | c :: rest =>
        let tail := rest.foldl (init := "") fun acc d => acc ++ s!", {d}"
        s!"#[({c} : ZMod64 {p}){tail}]"
  let powChain := String.intercalate ", " (cert.2.2.1.map (renderCoeffs p))
  let bezout := String.intercalate ", " (cert.2.2.2.map fun w =>
    s!"{lb} left := {renderCoeffs p w.1}, right := {renderCoeffs p w.2} {rb}")
  String.intercalate "\n"
    [ "-- Add to HexConway/Table.lean:",
      "",
      s!"/-- The committed `C({p}, {n})` Luebeck entry, stored ascending by degree. -/",
      s!"def {name} : FpPoly {p} :=",
      s!"  {lb} coeffs := {coeffLit}",
      "    normalized := by",
      "      right",
      s!"      decide {rb}",
      "",
      s!"/-- The committed `C({p}, {n})` entry is monic. -/",
      s!"@[simp, grind .] theorem {name}_monic :",
      s!"    DensePoly.Monic {name} := by",
      "  rfl",
      "",
      s!"/-- The committed `C({p}, {n})` entry has positive degree. -/",
      s!"@[simp, grind .] theorem {name}_degree_pos :",
      s!"    0 < FpPoly.degree {name} := by",
      "  decide",
      "",
      "-- Add to HexConway/Certificates.lean:",
      "",
      s!"/-- Rabin irreducibility certificate for the committed `C({p}, {n})` entry. -/",
      s!"private def {cert_} : Berlekamp.IrreducibilityCertificate where",
      s!"  p := {p}",
      s!"  n := {cert.2.1}",
      s!"  powChain := #[{powChain}]",
      s!"  bezout := #[{bezout}]",
      "",
      "set_option maxRecDepth 4096 in",
      "set_option maxHeartbeats 8000000 in",
      s!"/-- `{cert_}_incremental_check` confirms the incremental Rabin certificate",
      s!"`{cert_}` validates for the committed `C({p}, {n})` entry. -/",
      s!"private theorem {cert_}_incremental_check :",
      "    Berlekamp.checkIrreducibilityCertificateLinearIncremental",
      s!"        {name} {name}_monic {cert_} = true := by",
      "  decide",
      "",
      s!"/-- The committed `C({p}, {n})` entry is irreducible. -/",
      s!"@[grind .] theorem {name}_irreducible :",
      s!"    FpPoly.Irreducible {name} :=",
      "  Berlekamp.rabinTest_imp_irreducible",
      s!"    {name}",
      s!"    {name}_monic",
      "    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest",
      s!"      {name} {name}_monic {cert_} {cert_}_incremental_check)" ]
    ++ "\n\n" ++ hitLemma p n coeffs name
    ++ "\n\n" ++ apiBlock p n coeffs name

/-- Print the per-entry source block for a Conway pair in the committed cache.

Takes only the pair. The coefficients are read from the cache row for that
pair rather than supplied by the caller, so the emitted block cannot be
labelled `C(p, n)` while holding some other polynomial. That distinction
matters because Tier 1 proves only that a committed entry is monic,
irreducible, and of the requested degree; nothing in Lean says it is *the*
Conway polynomial, so a mislabelled entry would typecheck.

Widen the cache first with `scripts/oracle/update_luebeck_conway_cache.py` if
the pair is missing. -/
syntax (name := conwayEntrySource)
  "#conway_entry_source" num num (&"from" str)? : command

@[command_elab conwayEntrySource]
def elabEntrySource : CommandElab := fun stx => do
  let p := stx[1].isNatLit?.getD 0
  let n := stx[2].isNatLit?.getD 0
  let pathArg := stx[3]
  let defaultPath := "scripts/oracle/luebeck_conway_cache.json"
  let path :=
    if pathArg.isNone then defaultPath else pathArg[0][1].isStrLit?.getD defaultPath
  let entries ← Rebuild.readCache path
  let some entry := entries.find? (fun e => e.p = p && e.n = n)
    | throwError "the cache at '{path}' has no row for C({p}, {n}); widen it with \
                  scripts/oracle/update_luebeck_conway_cache.py first."
  let coeffs := entry.coeffs
  -- Shape checks the cache itself does not enforce. A row that fails any of
  -- these would still produce a certificate for *something*, so reject it here
  -- rather than emit a block whose label does not match its contents.
  unless coeffs.length = n + 1 do
    throwError "the cache row for C({p}, {n}) has {coeffs.length} coefficients, \
                expected {n + 1} for a degree-{n} polynomial."
  unless coeffs.getLast? = some 1 do
    throwError "the cache row for C({p}, {n}) is not monic."
  unless coeffs.all (fun c => c < p) do
    throwError "the cache row for C({p}, {n}) has a coefficient outside F_{p}."
  match entryCertData p coeffs with
  | none =>
      throwError "no Rabin certificate for C({p}, {n}); the cached coefficients are \
                  not a monic irreducible polynomial over F_{p}, so the cache is wrong."
  | some cert =>
      unless cert.2.1 = n do
        throwError "the certificate for C({p}, {n}) reports degree {cert.2.1}; \
                    this is a generator bug, not a bad entry."
      unless entryCertValidates p coeffs cert do
        throwError "the generated certificate for C({p}, {n}) does not validate; \
                    this is a generator bug, not a bad entry."
      logInfo (entryBlock p n coeffs cert)

end Hex.Conway.EntrySource
