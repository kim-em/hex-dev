/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FieldRootSigns
public import HexRCF.RealCoefficients.SignInputs
public import HexRCF.RealCoefficients.RadicalCheck
public import HexRCF.Certificate
public section

/-! Executable finite root/cell checking, independent of real semantics. -/

namespace Hex.RCF.RealCoefficients.RepresentationCarrier
open Hex
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E]

/-- Product before squarefree preparation; zero atoms are omitted. -/
@[expose] def product (ps : List (DensePoly E)) : DensePoly E :=
  (ps.filter (fun p => !p.isZero)).foldr (· * ·) 1

end Hex.RCF.RealCoefficients.RepresentationCarrier

namespace Hex.RCF.RealCoefficients.QueryReplay
open Hex
variable {E : Type u}

/-- Every coefficient sign read by replay must have an explicit entry. -/
@[expose] def covered (lookup : E → Option Int) (keys : List E) : Bool :=
  keys.all fun x => (lookup x).isSome

/-- Executable retrieval after coverage preflight. The missing-entry branch
cannot contribute to an accepted query. -/
@[expose] def cached (lookup : E → Option Int) (x : E) : Int := (lookup x).getD 0

variable [Zero E] [DecidableEq E]

/-- Preserve a stored degree by authenticating its nonzero top coefficient.
The representation need not reflect zero under real evaluation. -/
@[expose] def leading (lookup : E → Option Int) (q : DensePoly E) : Bool :=
  if q.size = 0 then true
  else match lookup (q.coeff (q.size - 1)) with
    | none => false
    | some observed => observed != 0

variable [Add E] [Sub E] [Mul E] [One E] [NatCast E]

/-- Finite sign and leading-coefficient checks over a coefficient ring.
Replay performs no division, normalization or certificate production. -/
@[expose] def check {C : Type v} [DecidableEq C] (lookup : E → Option Int) (context : C)
    (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C) : Bool :=
  covered lookup (SignInputs.certificate head a b cert) &&
    leading lookup head &&
    cert.squarefree.chain.all (leading lookup) &&
    cert.remainders.chain.all (leading lookup) &&
    Sturm.check (cached lookup) context head test a b value cert

/-- The complete inventory includes the signs used by degree preservation. -/
@[expose] def keys {C : Type v} (head : DensePoly E) (a b : Endpoint E)
    (cert : TarskiCertificate E E C) : List E :=
  SignInputs.certificate head a b cert ++ [head.coeff (head.size - 1)] ++
    cert.squarefree.chain.toList.map (fun q => q.coeff (q.size - 1)) ++
    cert.remainders.chain.toList.map (fun q => q.coeff (q.size - 1))

end Hex.RCF.RealCoefficients.QueryReplay

namespace Hex.RCF.RealCoefficients.IsolationTransport
open Hex
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Authenticate complete and per-interval counts through finite sign lookup.
The point embedding is fixed before producing or checking the certificate. -/
@[expose] def check (lookup : E → Option Int) (point : Dyadic → E)
    (context : Ctx) (head : DensePoly E) (cert : IsolationReplay E Ctx) : Bool :=
  cert.isolations.checkGaps &&
    QueryReplay.check lookup context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total &&
    (List.finRange cert.isolations.intervals.size).all fun i =>
      let interval := cert.isolations.intervals[i]
      QueryReplay.check lookup context head 1
        (.finite (point interval.lower)) (.finite (point interval.upper)) 1 cert.counts[i]

/-- All sign operands, including the finite leading-coefficient guards. -/
@[expose] def keys (point : Dyadic → E) (head : DensePoly E)
    (cert : IsolationReplay E Ctx) : List E :=
  QueryReplay.keys head .negInf .posInf cert.total ++
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      QueryReplay.keys head (.finite (point interval.lower))
        (.finite (point interval.upper)) cert.counts[i]

end Hex.RCF.RealCoefficients.IsolationTransport

namespace Hex.RCF.RealCoefficients.QueryCells
open Hex Hex.RealFormula
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Bind every original row and check its sign at the same isolated root.
Repeated atom occurrences remain in the checked inventory. -/
@[expose] def checkRows (lookup : E → Option Int) (point : Dyadic → E)
    (context : Ctx) (head : DensePoly E) (intervals : Vector DyadicInterval roots)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (rows : FieldRootSigns.Table E Ctx n roots) : Bool :=
  rows.checkRows formula fun atom i cert =>
    let interval := intervals[i]
    QueryReplay.check lookup context head (query atom)
      (.finite (point interval.lower)) (.finite (point interval.upper)) cert.value cert

/-- Complete finite cell checking over stored coefficients with ordinary
arithmetic. Coefficient evidence is authenticated by the caller; no field,
inverse, global zero reflection or numerical search is required here. -/
@[expose] def check (lookup : E → Option Int) (point : Dyadic → E) (context : Ctx)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (radical : RadicalCert E Ctx) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : Bool :=
  formula.polys.all (fun atom => QueryReplay.leading lookup (query atom)) &&
    radical.check context (RepresentationCarrier.product (formula.polys.map query)) &&
    IsolationTransport.check lookup point context radical.core cert &&
    checkRows lookup point context radical.core cert.isolations.intervals.toVector query formula rows &&
    QueryReplay.covered lookup (SignInputs.openSamples point cert (formula.polys.map query))

/-- Sign operands of the actual formula, root queries and ordinary sectors.
Original source bindings and divisor conditions remain the caller's inventory. -/
@[expose] def keys (point : Dyadic → E)
    (query : RealFormula.Poly n → DensePoly E) (formula : QF n)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (rows : FieldRootSigns.Table E Ctx n cert.isolations.intervals.size) : List E :=
  formula.polys.map (fun atom => (query atom).coeff ((query atom).size - 1)) ++
    IsolationTransport.keys point head cert ++
    rows.entries.flatMap (fun row =>
      (List.finRange cert.isolations.intervals.size).flatMap fun i =>
        let interval := cert.isolations.intervals[i]
        QueryReplay.keys head (.finite (point interval.lower))
          (.finite (point interval.upper)) row.evidence[i]) ++
    SignInputs.openSamples point cert (formula.polys.map query)

end Hex.RCF.RealCoefficients.QueryCells

namespace Hex.RCF.RealCoefficients.RepresentationSpecialize
open Hex Hex.RealFormula
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Mul E] [Neg E] [NatCast E]

/-- Integer coefficients use only the representation's actual casts and negation. -/
@[expose] def scalar : Int → E
  | .ofNat n => (n : E)
  | .negSucc n => -((n + 1 : Nat) : E)

/-- Evaluate only the coefficient coordinates with their actual arithmetic. -/
@[expose] def coefficient (values : Fin n → E) (m : Mono (n + 1)) (c : Int) : E :=
  let product := (List.finRange n).foldl (fun acc i =>
    if m[i.castSucc] = 0 then acc else acc * Mono.powBySq (values i) m[i.castSucc]) 1
  if c = 1 then product else scalar c * product

/-- Group terms by their bound-variable exponent through dense coefficient addition.
Coefficient powers and products are evaluated in `E`, without polynomial products
or a ring or field instance on stored expressions. -/
@[expose] def polynomial (values : Fin n → E) (q : RealFormula.Poly (n + 1)) : DensePoly E :=
  q.termsList.foldl (fun acc term =>
    acc + DensePoly.monomial term.1[Fin.last n] (coefficient values term.1 term.2)) 0

/-- Retain every original atom, including zero, repeated and domain-guard atoms. -/
@[expose] def prepare (values : Fin n → E) (formula : RealFormula.QF (n + 1)) :
    List (DensePoly E) := formula.polys.map (polynomial values)

end Hex.RCF.RealCoefficients.RepresentationSpecialize

namespace Hex.RCF.RealCoefficients.Decision
open Hex Hex.RealFormula
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Read root signs from their checked rows and sector signs at the listed
ordinary point. The specialization is supplied independently of its semantics. -/
@[expose] def cellSign (sign : E → Int) (point : Dyadic → E)
    (polynomial : RealFormula.Poly n → DensePoly E) (cert : IsolationReplay E Ctx)
    (rootValue : Fin cert.isolations.intervals.size → RealFormula.Poly n → Int)
    (cell : Cell cert.isolations.intervals.size) (atom : RealFormula.Poly n) : Option Sign :=
  match cell with
  | .open cut => some <| Sign.ofInt <| sign <|
      (polynomial atom).eval (point (cert.isolations.openPoint cut))
  | .root i => some <| Sign.ofInt (rootValue i atom)

end Hex.RCF.RealCoefficients.Decision

namespace Hex.RealFormula.QF
open Hex.RCF

/-- Every Boolean branch is evaluated, including one whose other branch has
already decided the truth value. Thus a missing sign always fails closed. -/
@[expose] def evalSigns (signOf : Hex.RealFormula.Poly n → Option Sign) : Hex.RealFormula.QF n → Option Bool
  | .atom a => do
      let sign ← signOf a.p
      pure (a.cmp.evalRat (sign.toInt : Rat))
  | .tt => some true
  | .ff => some false
  | .not p => do
      let value ← evalSigns signOf p
      pure (!value)
  | .and p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left && right)
  | .or p q => do
      let left ← evalSigns signOf p
      let right ← evalSigns signOf q
      pure (left || right)

end Hex.RealFormula.QF
