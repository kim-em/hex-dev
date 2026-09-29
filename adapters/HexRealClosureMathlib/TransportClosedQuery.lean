/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportClosed

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Add E] [Sub E] [Mul E] [One E] [NatCast E] [CommRing K] [DecidableEq K]

/-- Membership premises concern only the literal finite data stored in a chain. -/
structure ChainDomain (S : E → Prop) (cert : Hex.SignedRemainderChain E) : Prop where
  entries : ∀ p ∈ cert.chain, ∀ i < p.size, S (p.coeff i)
  initialLeft : S cert.initial.leftScale
  initialRight : S cert.initial.rightScale
  initialQuotient : ∀ i < cert.initial.quotient.size, S (cert.initial.quotient.coeff i)
  stepLeft : ∀ i < cert.steps.size, S (cert.steps.getD i ⟨0, 0, 0⟩).leftScale
  stepRight : ∀ i < cert.steps.size, S (cert.steps.getD i ⟨0, 0, 0⟩).rightScale
  stepQuotient : ∀ i < cert.steps.size, ∀ j < (cert.steps.getD i ⟨0, 0, 0⟩).quotient.size,
    S ((cert.steps.getD i ⟨0, 0, 0⟩).quotient.coeff j)
  terminalScale : ∀ scale q, cert.terminal = some (scale, q) → S scale
  terminalQuotient : ∀ scale q, cert.terminal = some (scale, q) → ∀ i < q.size, S (q.coeff i)

/-- Sign agreement is required only at the literal scales used by the checker. -/
structure ChainSigns (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (cert : Hex.SignedRemainderChain E) : Prop where
  initialLeft : targetSign (read cert.initial.leftScale) = sourceSign cert.initial.leftScale
  initialRight : targetSign (read cert.initial.rightScale) = sourceSign cert.initial.rightScale
  stepLeft : ∀ i < cert.steps.size,
    targetSign (read (cert.steps.getD i ⟨0, 0, 0⟩).leftScale) =
      sourceSign (cert.steps.getD i ⟨0, 0, 0⟩).leftScale
  stepRight : ∀ i < cert.steps.size,
    targetSign (read (cert.steps.getD i ⟨0, 0, 0⟩).rightScale) =
      sourceSign (cert.steps.getD i ⟨0, 0, 0⟩).rightScale
  terminal : ∀ scale q, cert.terminal = some (scale, q) →
    targetSign (read scale) = sourceSign scale

omit [DecidableEq K] in
private theorem row_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (cert : Hex.SignedRemainderChain E) (domain : ChainDomain S cert) (n i : Nat) :
    S ((cert.chain.getD n 0).coeff i) := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : cert.chain[n]? with
  | none =>
    simp only [Option.getD_none, Hex.DensePoly.coeff_zero]
    exact data.zero
  | some p =>
    simp only [Option.getD_some]
    exact data.coefficient read S p (domain.entries p (Array.mem_of_getElem? h)) i

omit [DecidableEq K] in
/-- Closure derives all intermediate equations from finite stored membership.
Leading guards and scalar signs remain explicit checker premises. -/
theorem ChainData.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (sourceSign : E → Int) (targetSign : K → Int) (p f : Hex.DensePoly E)
    (cert : Hex.SignedRemainderChain E)
    (hp : ∀ i < p.size, S (p.coeff i)) (hf : ∀ i < f.size, S (f.coeff i))
    (domain : ChainDomain S cert) (head : Leading read p)
    (entries : ∀ r ∈ cert.chain, Leading read r)
    (signs : ChainSigns read sourceSign targetSign cert) :
    ChainData read sourceSign targetSign p f cert := by
  refine ⟨head, entries, ?_, signs.initialLeft, signs.initialRight, ?_,
    signs.stepLeft, signs.stepRight, ?_, signs.terminal⟩
  · exact Initial.of_closed read S data p f _ _ _ _ hp hf
      (fun i _ => row_closed read S data cert domain 1 i)
      domain.initialLeft domain.initialQuotient domain.initialRight
  · intro i hi
    exact Recurrence.of_closed read S data _ _ _ _ _ _
      (fun j _ => row_closed read S data cert domain i j)
      (fun j _ => row_closed read S data cert domain (i + 1) j)
      (fun j _ => row_closed read S data cert domain (i + 2) j)
      (domain.stepLeft i hi) (domain.stepQuotient i hi) (domain.stepRight i hi)
  · intro scale q pair
    exact Terminal.of_closed read S data _ _ scale q
      (fun i _ => row_closed read S data cert domain (cert.chain.size - 2) i)
      (fun i _ => row_closed read S data cert domain (cert.chain.size - 1) i)
      (domain.terminalScale scale q pair) (domain.terminalQuotient scale q pair)

/-- An endpoint's sign agreement is separate from arithmetic preservation. -/
@[expose] def EndpointAgreement (read : E → K) (sourceSign : E → Int)
    (targetSign : K → Int) (p : Hex.DensePoly E) (a : Hex.Endpoint E) : Prop :=
  match a with
  | .finite x => targetSign (read (p.eval x)) = sourceSign (p.eval x)
  | _ => targetSign (read p.leadingCoeff) = sourceSign p.leadingCoeff

/-- Only finite endpoint values need membership in the interpretation domain. -/
@[expose] def EndpointDomain (S : E → Prop) (a : Hex.Endpoint E) : Prop :=
  match a with
  | .finite x => S x
  | _ => True

omit [DecidableEq K] in
/-- Closure supplies finite endpoint arithmetic; the sign is still a premise. -/
theorem EndpointData.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E) (a : Hex.Endpoint E)
    (coefficients : ∀ i < p.size, S (p.coeff i)) (leading : Leading read p)
    (domain : EndpointDomain S a) (sign : EndpointAgreement read sourceSign targetSign p a) :
    EndpointData read sourceSign targetSign p a := by
  refine ⟨leading, ?_⟩
  cases a with
  | finite x => exact ⟨Evaluation.of_closed read S data p x domain coefficients, sign⟩
  | negInf => exact sign
  | posInf => exact sign

omit [DecidableEq K] in
/-- Membership and closure supply all arithmetic of a full Tarski replay.
The remaining finite premises are leading guards and the exact queried signs. -/
theorem QueryData.of_closed {C : Type w} (read : E → K) (S : E → Prop) (data : Closed read S)
    (sourceSign : E → Int) (targetSign : K → Int) (p f : Hex.DensePoly E)
    (a b : Hex.Endpoint E) (cert : Hex.TarskiCertificate E E C)
    (hp : ∀ i < p.size, S (p.coeff i)) (hf : ∀ i < f.size, S (f.coeff i))
    (squarefree : ChainDomain S cert.squarefree) (remainders : ChainDomain S cert.remainders)
    (head : Leading read p) (squarefreeEntries : ∀ r ∈ cert.squarefree.chain, Leading read r)
    (remainderEntries : ∀ r ∈ cert.remainders.chain, Leading read r)
    (squarefreeSigns : ChainSigns read sourceSign targetSign cert.squarefree)
    (remainderSigns : ChainSigns read sourceSign targetSign cert.remainders)
    (lowerDomain : EndpointDomain S a) (upperDomain : EndpointDomain S b)
    (orderSign : ∀ x y, a = .finite x → b = .finite y →
      targetSign (read (x - y)) = sourceSign (x - y))
    (lowerSign : EndpointAgreement read sourceSign targetSign p a)
    (upperSign : EndpointAgreement read sourceSign targetSign p b)
    (lowerRows : ∀ r ∈ cert.remainders.chain, EndpointAgreement read sourceSign targetSign r a)
    (upperRows : ∀ r ∈ cert.remainders.chain, EndpointAgreement read sourceSign targetSign r b) :
    QueryData read sourceSign targetSign p f a b cert := by
  have unit := fun i (_ : i < (1 : Hex.DensePoly E).size) => data.coeff_one read S i
  refine ⟨ChainData.of_closed read S data sourceSign targetSign p 1 cert.squarefree hp unit
    squarefree head squarefreeEntries squarefreeSigns,
    ChainData.of_closed read S data sourceSign targetSign p f cert.remainders hp hf
    remainders head remainderEntries remainderSigns, ?_,
    EndpointData.of_closed read S data sourceSign targetSign p a hp head lowerDomain lowerSign,
    EndpointData.of_closed read S data sourceSign targetSign p b hp head upperDomain upperSign,
    ?_, ?_⟩
  · cases a <;> cases b <;> try exact trivial
    rename_i x y
    exact ⟨data.read_sub x y lowerDomain upperDomain, orderSign x y rfl rfl⟩
  · intro r member
    exact EndpointData.of_closed read S data sourceSign targetSign r a
      (remainders.entries r member) (remainderEntries r member) lowerDomain (lowerRows r member)
  · intro r member
    exact EndpointData.of_closed read S data sourceSign targetSign r b
      (remainders.entries r member) (remainderEntries r member) upperDomain (upperRows r member)

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.ChainData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.ChainData.of_closed
/-- info: 'Hex.RealClosure.Transport.EndpointData.of_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.EndpointData.of_closed
/-- info: 'Hex.RealClosure.Transport.QueryData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.QueryData.of_closed
