/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Field
public import HexRealClosureTheory.TransportClosedQuery
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

/-- Require a recorded nonzero sign for each nonempty polynomial's top coefficient. -/
@[expose] def leadingCheck (table : LiteralSign.Table E) (q : DensePoly E) : Bool :=
  if q.size = 0 then true
  else match table.lookup? (q.coeff (q.size - 1)) with
    | none => false
    | some observed => observed != 0

theorem leading (table : LiteralSign.Table E)
    (checked : Field.checkSignTable p s hw hp table = true) (q : DensePoly E)
    (accepted : leadingCheck table q = true) :
    Transport.Leading (Field.value (Field.literalRep p s hw hp)) q := by
  intro positive zero
  unfold leadingCheck at accepted
  split at accepted
  · omega
  · rename_i nonempty
    cases hit : table.lookup? (q.coeff (q.size - 1)) with
    | none => simp only [hit, Bool.false_eq_true] at accepted
    | some observed =>
      have sign := Field.checkSignTable_lookup p s hw hp table checked
        (q.coeff (q.size - 1)) observed hit
      rw [zero] at sign
      have observedZero : observed = 0 := by simpa using sign
      simp [hit, observedZero] at accepted

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
  let target := fun x : ℝ => (SignType.sign x : Int)
  have signs (x : E) : target (read x) = sign x :=
    (Field.checkSignTable_spec p s hw hp table checked x).symm
  have domain (chain : SignedRemainderChain E) : Transport.ChainDomain (fun _ : E => True) chain := by
    constructor <;> intros <;> trivial
  have chainSigns (chain : SignedRemainderChain E) :
      Transport.ChainSigns read sign target chain := by
    constructor <;> intros <;> exact signs _
  have endpointSigns (r : DensePoly E) (e : Endpoint E) :
      Transport.EndpointAgreement read sign target r e := by
    cases e <;> exact signs _
  have endpointDomain (e : Endpoint E) : Transport.EndpointDomain (fun _ : E => True) e := by
    cases e <;> trivial
  have data := Transport.QueryData.of_closed read (fun _ => True)
    (closed (Field.literalRep p s hw hp) (Field.literalRep_mk p s hw hp) real)
    sign target head test a b cert
    (fun _ _ => trivial) (fun _ _ => trivial) (domain _) (domain _)
    (leading table checked head headChecked)
    (fun r member => leading table checked r (squarefree r member))
    (fun r member => leading table checked r (remainders r member))
    (chainSigns _) (chainSigns _) (endpointDomain a) (endpointDomain b)
    (fun _ _ _ _ => signs _) (endpointSigns head a) (endpointSigns head b)
    (fun r _ => endpointSigns r a) (fun r _ => endpointSigns r b)
  exact Transport.query_check read
    (Field.value_zero _ (Field.literalRep_mk p s hw hp) real)
    (Field.value_one _ (Field.literalRep_mk p s hw hp) real)
    id sign target context head test a b value cert data accepted

end Hex.RCF.RealCoefficients.FieldTransport
