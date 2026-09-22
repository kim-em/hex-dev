/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Reduction

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]

/-- The actual Tarski operand. The reduced case never expands the full product. -/
@[expose] def queryPoly (qs : List (DensePoly E)) (es : List Nat)
    (reduction : Option (Reduction E)) : DensePoly E :=
  match reduction with
  | none => moment qs es
  | some r => r.result

/-- Bind a Tarski query to its indexed moment, either directly or by a checked
positive reduction chain. All query/domain/context bindings remain literal. -/
@[expose] def checkMoment [DecidableEq Ctx] (sign : E → Int) (context : Ctx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (es : List Nat)
    (value : Int) (cert : TarskiCertificate E E Ctx) (reduction : Option (Reduction E)) : Bool :=
  (match reduction with
   | none => decide (qs.length = es.length) && es.all (· ≤ 2)
   | some r => r.check sign p qs es) &&
  Sturm.check sign context p (queryPoly qs es reduction) a b value cert

/-- Accepted moment replay always includes checked query evidence, regardless
of the chosen product representation. -/
theorem checkMoment_query [DecidableEq Ctx] {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {a b : Endpoint E} {qs : List (DensePoly E)} {es : List Nat}
    {value : Int} {cert : TarskiCertificate E E Ctx} {reduction : Option (Reduction E)}
    (h : checkMoment sign context p a b qs es value cert reduction = true) :
    Sturm.check sign context p (queryPoly qs es reduction) a b value cert = true := by
  simp only [checkMoment, Bool.and_eq_true] at h
  exact h.2

/-- A supplied reduction is checked before its result is used as a query. -/
theorem checkMoment_reduction [DecidableEq Ctx] {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {a b : Endpoint E} {qs : List (DensePoly E)} {es : List Nat}
    {value : Int} {cert : TarskiCertificate E E Ctx} {r : Reduction E}
    (h : checkMoment sign context p a b qs es value cert (some r) = true) :
    r.check sign p qs es = true := by
  simp only [checkMoment, Bool.and_eq_true] at h
  exact h.1

end Hex.SignDet
