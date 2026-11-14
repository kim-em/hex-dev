/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Field
public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRCF.RealCoefficients.QueryReplay
public import HexRealClosureTheory.TransportClosedQuery
public import HexRealRootsTheory.Separation
public section

universe u
open Hex
namespace Hex.RCF.RealCoefficients.FieldTransport
open Hex.RCF.RealCoefficients
open Hex.RealClosure

variable {p : ZPoly} {root : SimpleRoot p}

theorem closed (rep : RefinedIsolation p) (same : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) :
    Transport.Closed (Field.value rep : PolyQuot p root → ℝ) (fun _ => True) where
  zero := trivial
  add := fun _ _ _ _ => trivial
  mul := fun _ _ _ _ => trivial
  sub := fun _ _ _ _ => trivial
  one := trivial
  natCast := fun _ => trivial
  read_zero := Field.value_zero rep same real
  read_add := fun a b _ _ => Field.value_add rep same real a b
  read_mul := fun a b _ _ => Field.value_mul rep same real a b
  read_sub := fun a b _ _ => Field.value_sub rep same real a b
  read_one := Field.value_one rep same real
  read_natCast := Field.value_natCast rep same real

theorem quotient (rep : RefinedIsolation p) (same : SimpleRoot.mk rep = root)
    (real : rep.root.im = 0) (a b q : PolyQuot p root)
    (denominator : Field.value rep b ≠ 0) (identity : q * b = a) :
    Field.value rep q = Field.value rep a / Field.value rep b := by
  apply (eq_div_iff denominator).mpr
  rw [← Field.value_mul rep same real, identity]

variable {s : DyadicSquare} {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- The checked sign-table header authenticates the selected real embedding. -/
theorem real (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) :
    (Field.literalRep p s hw hp).root.im = 0 := by
  have reality : s.meetsRealAxis = true := by
    simp only [Field.checkSignTable, Bool.and_eq_true] at checked
    exact checked.1.2
  exact Field.literalRep_real p s hw hp reality

/-- A nonzero recorded sign proves the original interpreted denominator is
nonzero, without global zero reflection for the coordinate representation. -/
theorem nonzero (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (a : E) (observed : Int)
    (hit : table.lookup? a = some observed) (nonzero : observed ≠ 0) :
    Field.value (Field.literalRep p s hw hp) a ≠ 0 := by
  intro zero
  have sign := Field.checkSignTable_lookup p s hw hp table checked a observed hit
  rw [zero] at sign
  exact nonzero (by simpa using sign)

/-- Rational dyadic points use the same fixed selected real embedding. -/
theorem point (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (d : Dyadic) :
    Field.value (Field.literalRep p s hw hp) (PolyQuot.ofRat d.toRat : E) =
      HexRealRootsTheory.Dyadic.toReal d := by
  simpa only [HexRealRootsTheory.toReal_eq_cast_toRat] using
    FieldSpecialize.value_ofRat (Field.literalRep p s hw hp)
      (Field.literalRep_mk p s hw hp) (real table checked) d.toRat

/-- Require a recorded nonzero sign for each nonempty polynomial's top coefficient. -/
@[expose] def leadingWith (lookup : E → Option Int) (q : DensePoly E) : Bool :=
  QueryReplay.leading lookup q

@[expose] def leadingCheck (table : LiteralSign.Table E) (q : DensePoly E) : Bool :=
  leadingWith table.lookup? q

theorem leading (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (q : DensePoly E)
    (accepted : leadingCheck table q = true) :
    Transport.Leading (Field.value (Field.literalRep p s hw hp)) q := by
  exact QueryReplay.leading_spec table.lookup? (Field.value (Field.literalRep p s hw hp))
    (fun x value found => Field.checkSignTable_lookup p s hw hp table checked x value found)
    q accepted

theorem query {C : Type u} [DecidableEq C]
    (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true)
    (real : (Field.literalRep p s hw hp).root.im = 0)
    (context : C) (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C)
    (headChecked : leadingCheck table head = true)
    (squarefree : ∀ r ∈ cert.squarefree.chain, leadingCheck table r = true)
    (remainders : ∀ r ∈ cert.remainders.chain, leadingCheck table r = true)
    (accepted : Sturm.check (table.sign (Field.value (Field.literalRep p s hw hp)))
      context head test a b value cert = true) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) head)
      (Transport.polynomial (Field.value (Field.literalRep p s hw hp)) test)
      (Transport.endpoint (Field.value (Field.literalRep p s hw hp)) a)
      (Transport.endpoint (Field.value (Field.literalRep p s hw hp)) b)
      value (Transport.query (Field.value (Field.literalRep p s hw hp)) id cert) = true := by
  let read : E → ℝ := Field.value (Field.literalRep p s hw hp)
  let sign := table.sign read
  have signs (x : E) : (SignType.sign (read x) : Int) = sign x :=
    (Field.checkSignTable_spec p s hw hp table checked x).symm
  exact QueryReplay.transport read
    (closed (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp) real) sign signs
    context head test a b value cert
    (leading table checked head headChecked)
    (fun r member => leading table checked r (squarefree r member))
    (fun r member => leading table checked r (remainders r member))
    accepted

end Hex.RCF.RealCoefficients.FieldTransport
