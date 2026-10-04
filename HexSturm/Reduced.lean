/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturm.Basic
import all HexPoly.Euclid.DivGcd

public section

/-! Value queries with an initial remainder-only reduction. The existing verified
`modImpl` worker invokes `modArray` without constructing a quotient. The shared Tarski
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
  queryPrepared domain (DensePoly.modImpl f domain.head)

/-- Validate the domain before reducing the query. The original literal
certificate API is used when evidence binding the unreduced query is needed. -/
@[expose] def queryReduced (sign : E → Int) (p f : DensePoly E)
    (a b : Endpoint E) : Option Int :=
  match prepare sign p a b with
  | none => none
  | some domain => some (queryReducedPrepared domain f)

omit [NatCast E] [Neg E] [Inv E] in
private theorem modImpl_eq_mod (p q : DensePoly E) :
    DensePoly.modImpl p q = p % q := by
  unfold DensePoly.modImpl
  change (if p.natDegree < q.natDegree then p else
    DensePoly.modArray p q (fun coeff => coeff / q.leadingCoeff)) = DensePoly.mod p q
  by_cases hlt : p.natDegree < q.natDegree
  · simp [hlt, DensePoly.mod, DensePoly.divMod]
  · simp only [hlt, ↓reduceIte, DensePoly.mod, DensePoly.divMod]
    exact DensePoly.modArray_eq_divModArray_snd p q (fun coeff => coeff / q.leadingCoeff)

/-- The remainder-only worker agrees operationally with querying the remainder. -/
theorem queryReducedPrepared_eq (domain : PreparedDomain E) (f : DensePoly E) :
    queryReducedPrepared domain f = queryPrepared domain (f % domain.head) := by
  rw [queryReducedPrepared, modImpl_eq_mod]

/-- Domain-first reduction agrees with ordinary querying of the remainder. -/
theorem queryReduced_eq_query (sign : E → Int) (p f : DensePoly E) (a b : Endpoint E) :
    queryReduced sign p f a b = query sign p (f % p) a b := by
  cases hprepare : prepare sign p a b with
  | none =>
      have hsome := prepare_isSome sign p (f % p) a b
      have invalid : query sign p (f % p) a b = none := by
        cases hquery : query sign p (f % p) a b <;> simp_all
      simp [queryReduced, hprepare, invalid]
  | some domain =>
      obtain ⟨hsign, hhead, hlower, hupper⟩ :=
        prepare_eq_some sign p a b domain hprepare
      simp only [queryReduced, hprepare]
      rw [queryReducedPrepared_eq]
      simpa only [hsign, hhead, hlower, hupper] using
        (query_prepared domain (f % domain.head)).symm


end Hex.Sturm
