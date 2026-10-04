/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic
import all HexSturm.Basic

public section

/-! Value queries with an initial remainder-only reduction. Polynomial `%`
uses the existing verified `modArray` implementation. The shared Tarski
producer therefore receives a query of degree below the head, rather than
retaining the original high-degree quotient as literal certificate evidence.
Division must have its lawful interpretation for the correspondence theorem.
The original certificate and query APIs remain available. -/
namespace Hex.Sturm

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [NatCast E] [Neg E] [Inv E] [Div E]

/-- Reduce a query by its validated head before calling the shared producer.
At every head root the reduced query has the original query's value. -/
@[expose] def queryReducedPrepared (domain : PreparedDomain E) (f : DensePoly E) : Int :=
  queryPrepared domain (f % domain.head)

/-- Validate the domain before reducing the query. The original literal
certificate API is used when evidence binding the unreduced query is needed. -/
@[expose] def queryReduced (sign : E → Int) (p f : DensePoly E)
    (a b : Endpoint E) : Option Int :=
  match prepare sign p a b with
  | none => none
  | some domain => some (queryReducedPrepared domain f)

/-- Domain-first reduction agrees with ordinary querying of the remainder. -/
theorem queryReduced_eq_query (sign : E → Int) (p f : DensePoly E) (a b : Endpoint E) :
    queryReduced sign p f a b = query sign p (f % p) a b := by
  cases he : TarskiCertificate.checkEndpoints (EndpointSigns.ofSign sign) p a b <;>
    cases hc : SignedRemainderChain.lastIsConstant
      (SignedRemainderChain.build sign (normalize sign) p 1) <;>
    simp [queryReduced, prepare, queryReducedPrepared, queryPrepared, query,
      TarskiCertificate.query, TarskiCertificate.certify, he, hc]

end Hex.Sturm
