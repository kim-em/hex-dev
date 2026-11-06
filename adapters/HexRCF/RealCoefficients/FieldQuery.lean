/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FieldTransport
public import HexRCF.RealCoefficients.SignInputs
public section

universe u
open Hex Hex.RCF.RealCoefficients Hex.RealClosure
namespace Hex.RCF.RealCoefficients.FieldQuery
variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- Every sign dependency must have an explicit table entry, including exact zero. -/
@[expose] def coveredWith (lookup : E → Option Int) (keys : List E) : Bool :=
  QueryReplay.covered lookup keys

/-- Executable lookup used only after complete coverage preflight. Its default
branch cannot contribute to acceptance, as `missing_rejects` establishes. -/
@[expose] def cachedWith (lookup : E → Option Int) (x : E) : Int := QueryReplay.cached lookup x

/-- Check the original query and all finite signs and degree guards. The enclosing
checker authenticates the sign table once before checking its queries. No
root, sign or inverse producer is called during replay. -/
@[expose] def checkWith {C : Type u} [DecidableEq C] (lookup : E → Option Int) (context : C)
    (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C) : Bool :=
  QueryReplay.check lookup context head test a b value cert

/-- Linear retrieval retains the original public checker interface. -/
@[expose] def covered (table : LiteralSign.Table E) (keys : List E) : Bool :=
  coveredWith table.lookup? keys

@[expose] def cached (table : LiteralSign.Table E) (x : E) : Int :=
  cachedWith table.lookup? x

@[expose] def check {C : Type u} [DecidableEq C] (table : LiteralSign.Table E) (context : C)
    (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C) : Bool :=
  checkWith table.lookup? context head test a b value cert

/-- Every sign used by a query, including semantic leading-coefficient guards. -/
@[expose] def keys {C : Type u} (head : DensePoly E) (a b : Endpoint E)
    (cert : TarskiCertificate E E C) : List E :=
  QueryReplay.keys head a b cert

theorem cached_eq (table : LiteralSign.Table E) (keys : List E)
    (coverage : covered table keys = true) (x : E) (member : x ∈ keys)
    (read : E → ℝ) : cached table x = table.sign read x := by
  have present := List.all_eq_true.mp coverage x member
  cases hit : table.lookup? x with
  | none => simp [hit] at present
  | some value => simp [cached, cachedWith, QueryReplay.cached, LiteralSign.Table.sign, hit]

theorem checked {C : Type u} [DecidableEq C]
    (table : LiteralSign.Table E)
    (tableChecked : Field.checkSignTable p s hw hp table = true)
    (context : C) (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C)
    (accepted : check table context head test a b value cert = true) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) head)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) test)
      (Transport.endpoint (Field.value (Field.literalRep p s hw hp)) a)
      (Transport.endpoint (Field.value (Field.literalRep p s hw hp)) b)
      value (Transport.query (Field.value (Field.literalRep p s hw hp)) id cert) = true := by
  exact QueryReplay.checked table.lookup? (Field.value (Field.literalRep p s hw hp))
    (FieldTransport.closed (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp)
      (FieldTransport.real table tableChecked))
    (fun x observed hit => Field.checkSignTable_lookup p s hw hp table tableChecked x observed hit)
    context head test a b value cert accepted

theorem missing_rejects {C : Type u} [DecidableEq C]
    (table : LiteralSign.Table E) (context : C) (head test : DensePoly E)
    (a b : Endpoint E) (value : Int) (cert : TarskiCertificate E E C)
    (x : E) (member : x ∈ SignInputs.certificate head a b cert)
    (missing : table.lookup? x = none) :
    check table context head test a b value cert = false := by
  exact QueryReplay.missing_rejects table.lookup? context head test a b value cert x member missing

end Hex.RCF.RealCoefficients.FieldQuery
