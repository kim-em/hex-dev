/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.Irreducibility
import HexBerlekamp.CertificateSyntax
import HexPolyFp.Field
import HexConway.Table

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
`decide` check fail, so a bad entry cannot pass unnoticed.
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

/-- Print the per-entry source block for a committed or candidate Conway pair.

The coefficients come from the committed cache table, so this only works for
pairs the cache already covers; widen the cache first with
`scripts/oracle/update_luebeck_conway_cache.py` if the pair is missing. -/
syntax (name := conwayEntrySource)
  "#conway_entry_source" num num &"coeffs" "[" num,* "]" : command

@[command_elab conwayEntrySource]
def elabEntrySource : CommandElab := fun stx => do
  let p := stx[1].isNatLit?.getD 0
  let n := stx[2].isNatLit?.getD 0
  let coeffs := stx[5].getSepArgs.toList.map fun s => s.isNatLit?.getD 0
  match entryCertData p coeffs with
  | none =>
      throwError "no Rabin certificate for C({p}, {n}); the coefficients are not \
                  a monic irreducible polynomial over F_{p}, so check the transcription."
  | some cert =>
      unless entryCertValidates p coeffs cert do
        throwError "the generated certificate for C({p}, {n}) does not validate; \
                    this is a generator bug, not a bad entry."
      logInfo (entryBlock p n coeffs cert)

end Hex.Conway.EntrySource
