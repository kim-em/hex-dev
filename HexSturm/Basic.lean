/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.TarskiShared

public section

/-! Ordered-field frontend to the shared positive-scaled Tarski kernel.
An explicit sign also supports noncanonical representations without asserting
field or order instances on their storage. -/
namespace Hex.Sturm

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]

/-- The exact three-valued sign for canonical ordered coefficients. -/
@[expose] def orderSign [LT E] [DecidableLT E] (a : E) : Int :=
  if a < 0 then -1 else if a = 0 then 0 else 1

/-- Divide by the positive absolute leading coefficient. This controls
coefficient growth without changing signs or forcing positive-leading entries. -/
@[expose] def normalize [Neg E] [Inv E] (sign : E → Int) (p : DensePoly E) : E × DensePoly E :=
  let c := if sign p.leadingCoeff < 0 then -p.leadingCoeff else p.leadingCoeff
  (c, DensePoly.scale c⁻¹ p)

/-- A validated head and pair of endpoints, retaining the sign operation used
for validation. The constructor is private; serialized inputs must go through
`prepare` again. The squarefree chain is reused by prepared queries. -/
structure PreparedDomain (E : Type u) [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
    [NatCast E] [Neg E] [Inv E] where
  private mk ::
  sign : E → Int
  head : DensePoly E
  lower : Endpoint E
  upper : Endpoint E
  squarefree : SignedRemainderChain E
  endpoints_valid : TarskiCertificate.checkEndpoints (EndpointSigns.ofSign sign) head lower upper = true
  last_constant : SignedRemainderChain.lastIsConstant squarefree = true
  produced : squarefree = SignedRemainderChain.build sign (normalize sign) head 1

/-- Validate nonzero head, endpoint guards and a nonzero constant derivative
gcd using the shared chain producer. No query polynomial affects the domain. -/
def prepare [Neg E] [Inv E] (sign : E → Int) (p : DensePoly E) (a b : Endpoint E) :
    Option (PreparedDomain E) :=
  if hg : TarskiCertificate.checkEndpoints (EndpointSigns.ofSign sign) p a b = true then
    let sf := SignedRemainderChain.build sign (normalize sign) p 1
    if hc : SignedRemainderChain.lastIsConstant sf = true then
      some ⟨sign, p, a, b, sf, hg, hc, rfl⟩
    else none
  else none

/-- Successful preparation retains exactly the supplied operation and inputs. -/
theorem prepare_eq_some [Neg E] [Inv E] (sign : E → Int) (p : DensePoly E)
    (a b : Endpoint E) (domain : PreparedDomain E)
    (h : prepare sign p a b = some domain) :
    domain.sign = sign ∧ domain.head = p ∧ domain.lower = a ∧ domain.upper = b := by
  unfold prepare at h
  split at h
  · dsimp only at h
    split at h
    · cases Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp at h
  · simp at h

/-- Query a validated domain without repeating its squarefreeness computation. -/
@[expose] def queryPrepared [Neg E] [Inv E] (domain : PreparedDomain E) (f : DensePoly E) : Int :=
  (TarskiCertificate.fromChains domain.sign (EndpointSigns.ofSign domain.sign) () domain.head f domain.lower domain.upper
    domain.squarefree (SignedRemainderChain.build domain.sign (normalize domain.sign) domain.head f)).value

/-- Produce a literal query certificate with the caller's full context binding. -/
@[expose] def certifyPrepared [Neg E] [Inv E] {Ctx : Type v} (context : Ctx)
    (domain : PreparedDomain E) (f : DensePoly E) : TarskiCertificate E E Ctx :=
  TarskiCertificate.fromChains domain.sign (EndpointSigns.ofSign domain.sign) context domain.head f domain.lower domain.upper
    domain.squarefree (SignedRemainderChain.build domain.sign (normalize domain.sign) domain.head f)

/-- The literal context does not affect a prepared certificate's query value. -/
theorem certifyPrepared_value [Neg E] [Inv E] {Ctx : Type v} (context : Ctx)
    (domain : PreparedDomain E) (f : DensePoly E) :
    (certifyPrepared context domain f).value = queryPrepared domain f := rfl

/-- An ordered-field query on finite or infinite endpoints. The `Option`
records mathematical domain failure; signs and arithmetic are total. -/
@[expose] def query [Neg E] [Inv E] (sign : E → Int) (p f : DensePoly E) (a b : Endpoint E) : Option Int :=
  TarskiCertificate.query sign (EndpointSigns.ofSign sign) (normalize sign) p f a b

/-- Produce a certificate with exact literal context and input bindings. -/
@[expose] def certify [Neg E] [Inv E] {Ctx : Type v} (sign : E → Int) (context : Ctx)
    (p f : DensePoly E) (a b : Endpoint E) : Option (TarskiCertificate E E Ctx) :=
  TarskiCertificate.certify sign (EndpointSigns.ofSign sign) (normalize sign) context p f a b

/-- Certification with any literal context has the same whole query result. -/
theorem certify_value [Neg E] [Inv E] {Ctx : Type v} (sign : E → Int) (context : Ctx)
    (p f : DensePoly E) (a b : Endpoint E) :
    (certify sign context p f a b).map TarskiCertificate.value = query sign p f a b := by
  simp only [certify, query, TarskiCertificate.query, TarskiCertificate.certify]
  split
  · rfl
  · split <;> rfl

/-- Reusing a validated domain gives the same whole result as the ordinary
query, while retaining its existing squarefree chain. -/
theorem query_prepared [Neg E] [Inv E] (domain : PreparedDomain E) (f : DensePoly E) :
    query domain.sign domain.head f domain.lower domain.upper = some (queryPrepared domain f) := by
  simp only [query, TarskiCertificate.query, TarskiCertificate.certify, domain.endpoints_valid, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ← domain.produced, domain.last_constant, Option.map_some,
    queryPrepared]

/-- Prepared certification preserves the exact context and input bindings of
ordinary certification. No semantic equality substitutes for those bindings. -/
theorem certify_prepared [Neg E] [Inv E] {Ctx : Type v} (context : Ctx)
    (domain : PreparedDomain E) (f : DensePoly E) :
    certify domain.sign context domain.head f domain.lower domain.upper =
      some (certifyPrepared context domain f) := by
  simp only [certify, TarskiCertificate.certify, domain.endpoints_valid, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ← domain.produced, domain.last_constant, certifyPrepared]

/-- Preparation and querying have the same domain, independent of the query
polynomial. Preparation's private constructor is never needed by a consumer. -/
theorem prepare_isSome [Neg E] [Inv E] (sign : E → Int) (p f : DensePoly E) (a b : Endpoint E) :
    (prepare sign p a b).isSome = (query sign p f a b).isSome := by
  simp only [prepare, query, TarskiCertificate.query, TarskiCertificate.certify, Option.isSome_map]
  split
  · rename_i hg
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Option.isSome_some, Option.isSome_none]
  · rename_i hg
    have hg' := Bool.eq_false_iff.mpr hg
    simp only [hg', Bool.not_false, ↓reduceIte, Option.isSome_none]

/-- Check a field query certificate through the shared finite checker. -/
@[expose] def check {Ctx : Type v} [DecidableEq Ctx] (sign : E → Int) (context : Ctx)
    (p f : DensePoly E) (a b : Endpoint E) (value : Int) (cert : TarskiCertificate E E Ctx) : Bool :=
  TarskiCertificate.check sign (EndpointSigns.ofSign sign) context p f a b value cert

/-- Accepted replay retains every literal binding, independently of semantic
coefficient interpretation or producer provenance. -/
theorem check_bindings {Ctx : Type v} [DecidableEq Ctx] (sign : E → Int) (context : Ctx)
    (p f : DensePoly E) (a b : Endpoint E) (value : Int) (cert : TarskiCertificate E E Ctx)
    (h : check sign context p f a b value cert = true) :
    cert.context = context ∧ cert.head = p ∧ cert.queryPoly = f ∧
      cert.lower = a ∧ cert.upper = b ∧ cert.value = value := by
  simp only [check, TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Hex.Sturm
