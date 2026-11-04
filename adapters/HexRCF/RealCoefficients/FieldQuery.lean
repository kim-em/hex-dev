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
@[expose] def covered (table : LiteralSign.Table E) (keys : List E) : Bool :=
  keys.all fun x => (table.lookup? x).isSome

/-- Executable lookup used only after complete coverage preflight. Its default
branch cannot contribute to acceptance, as `missing_rejects` establishes. -/
@[expose] def cached (table : LiteralSign.Table E) (x : E) : Int := (table.lookup? x).getD 0

/-- Check the original query and all finite signs and degree guards. The enclosing
checker authenticates the sign table once before checking its queries. No
root, sign or inverse producer is called during replay. -/
@[expose] def check {C : Type u} [DecidableEq C] (table : LiteralSign.Table E) (context : C)
    (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C) : Bool :=
  covered table (SignInputs.certificate head a b cert) &&
    FieldTransport.leadingCheck table head &&
    cert.squarefree.chain.all (FieldTransport.leadingCheck table) &&
    cert.remainders.chain.all (FieldTransport.leadingCheck table) &&
    Sturm.check (cached table) context head test a b value cert

/-- Every sign used by a query, including semantic leading-coefficient guards. -/
@[expose] def keys {C : Type u} (head : DensePoly E) (a b : Endpoint E)
    (cert : TarskiCertificate E E C) : List E :=
  SignInputs.certificate head a b cert ++ [head.coeff (head.size - 1)] ++
    cert.squarefree.chain.toList.map (fun q => q.coeff (q.size - 1)) ++
    cert.remainders.chain.toList.map (fun q => q.coeff (q.size - 1))

theorem cached_eq (table : LiteralSign.Table E) (keys : List E)
    (coverage : covered table keys = true) (x : E) (member : x ∈ keys)
    (read : E → ℝ) : cached table x = table.sign read x := by
  have present := List.all_eq_true.mp coverage x member
  cases hit : table.lookup? x with
  | none => simp [hit] at present
  | some value => simp [cached, LiteralSign.Table.sign, hit]

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
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨coverage, headChecked⟩, squarefree⟩, remainders⟩, accepted⟩ := accepted
  have real := FieldTransport.real table tableChecked
  have same := SignInputs.certificate_check_congr (cached table)
    (table.sign (Field.value (Field.literalRep p s hw hp))) context head test a b value cert
    (fun x member => cached_eq table _ coverage x member _)
  rw [same] at accepted
  exact FieldTransport.query table tableChecked real context head test a b value cert headChecked
    (fun r member => Array.all_eq_true_iff_forall_mem.mp squarefree r member)
    (fun r member => Array.all_eq_true_iff_forall_mem.mp remainders r member) accepted

theorem missing_rejects {C : Type u} [DecidableEq C]
    (table : LiteralSign.Table E) (context : C) (head test : DensePoly E)
    (a b : Endpoint E) (value : Int) (cert : TarskiCertificate E E C)
    (x : E) (member : x ∈ SignInputs.certificate head a b cert)
    (missing : table.lookup? x = none) :
    check table context head test a b value cert = false := by
  have absent : covered table (SignInputs.certificate head a b cert) = false := by
    cases h : covered table (SignInputs.certificate head a b cert) with
    | false => rfl
    | true =>
      have present := List.all_eq_true.mp h x member
      simp [missing] at present
  simp [check, absent]

end Hex.RCF.RealCoefficients.FieldQuery
