/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SignInputs
public import HexRealClosureTheory.TransportClosedQuery
public section

namespace Hex.RCF.RealCoefficients.QueryReplay
open Hex.RealClosure

variable {E : Type u}

/-- Every coefficient sign read by replay must have an explicit entry. -/
@[expose] def covered (lookup : E → Option Int) (keys : List E) : Bool :=
  keys.all fun x => (lookup x).isSome

/-- Executable retrieval after coverage preflight. The missing-entry branch
cannot contribute to an accepted query. -/
@[expose] def cached (lookup : E → Option Int) (x : E) : Int := (lookup x).getD 0

/-- Semantic completion used only in proofs. Executable replay uses `cached`,
and coverage proves that both functions agree at every demanded key. -/
noncomputable def sign (lookup : E → Option Int) (read : E → ℝ) (x : E) : Int :=
  (lookup x).getD (SignType.sign (read x) : Int)

theorem sign_spec (lookup : E → Option Int) (read : E → ℝ)
    (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
    (x : E) : sign lookup read x = (SignType.sign (read x) : Int) := by
  cases found : lookup x with
  | none => simp only [sign, found, Option.getD_none]
  | some value => simpa only [sign, found, Option.getD_some] using sound x value found

theorem cached_eq (lookup : E → Option Int) (keys : List E)
    (coverage : covered lookup keys = true) (x : E) (member : x ∈ keys)
    (read : E → ℝ) : cached lookup x = sign lookup read x := by
  have present := List.all_eq_true.mp coverage x member
  cases found : lookup x with
  | none => simp [found] at present
  | some value => simp only [cached, sign, found, Option.getD_some]

variable [Zero E] [DecidableEq E]

/-- Preserve a stored degree by authenticating its nonzero top coefficient.
The representation need not reflect zero under real evaluation. -/
@[expose] def leading (lookup : E → Option Int) (q : DensePoly E) : Bool :=
  if q.size = 0 then true
  else match lookup (q.coeff (q.size - 1)) with
    | none => false
    | some observed => observed != 0

theorem leading_spec (lookup : E → Option Int) (read : E → ℝ)
    (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
    (q : DensePoly E) (accepted : leading lookup q = true) :
    Transport.Leading read q := by
  intro positive zero
  unfold leading at accepted
  split at accepted
  · omega
  · cases found : lookup (q.coeff (q.size - 1)) with
    | none => simp only [found, Bool.false_eq_true] at accepted
    | some observed =>
      have exactSign := sound _ observed found
      rw [zero] at exactSign
      have observedZero : observed = 0 := by simpa using exactSign
      simp [found, observedZero] at accepted

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

/-- Transfer existing Tarski evidence through a total ring interpretation.
Finite leading guards replace global zero reflection; no source field or
inverse operation is required. -/
theorem transport {C : Type v} [DecidableEq C] (read : E → ℝ)
    (closed : Transport.Closed read (fun _ => True)) (sourceSign : E → Int)
    (agreement : ∀ x, (SignType.sign (read x) : Int) = sourceSign x)
    (context : C) (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C) (headLeading : Transport.Leading read head)
    (squarefree : ∀ r ∈ cert.squarefree.chain, Transport.Leading read r)
    (remainders : ∀ r ∈ cert.remainders.chain, Transport.Leading read r)
    (accepted : Sturm.check sourceSign context head test a b value cert = true) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Transport.polynomial read head) (Transport.polynomial read test)
      (Transport.endpoint read a) (Transport.endpoint read b)
      value (Transport.query read id cert) = true := by
  let target := fun x : ℝ => (SignType.sign x : Int)
  have domain (chain : SignedRemainderChain E) :
      Transport.ChainDomain (fun _ : E => True) chain := by
    constructor <;> intros <;> trivial
  have chainSigns (chain : SignedRemainderChain E) :
      Transport.ChainSigns read sourceSign target chain := by
    constructor <;> intros <;> exact agreement _
  have endpointSigns (r : DensePoly E) (e : Endpoint E) :
      Transport.EndpointAgreement read sourceSign target r e := by
    cases e <;> exact agreement _
  have endpointDomain (e : Endpoint E) :
      Transport.EndpointDomain (fun _ : E => True) e := by
    cases e <;> trivial
  have data := Transport.QueryData.of_closed read (fun _ => True) closed
    sourceSign target head test a b cert
    (fun _ _ => trivial) (fun _ _ => trivial) (domain _) (domain _)
    headLeading squarefree remainders (chainSigns _) (chainSigns _)
    (endpointDomain a) (endpointDomain b) (fun _ _ _ _ => agreement _)
    (endpointSigns head a) (endpointSigns head b)
    (fun r _ => endpointSigns r a) (fun r _ => endpointSigns r b)
  exact Transport.query_check read closed.read_zero closed.read_one
    id sourceSign target context head test a b value cert data accepted

/-- A checked finite query has the same literal bindings and verdict at its
real interpretation. Every demanded sign comes from the supplied lookup. -/
theorem checked {C : Type v} [DecidableEq C] (lookup : E → Option Int)
    (read : E → ℝ) (closed : Transport.Closed read (fun _ => True))
    (sound : ∀ x value, lookup x = some value → value = (SignType.sign (read x) : Int))
    (context : C) (head test : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E C)
    (accepted : check lookup context head test a b value cert = true) :
    Sturm.check (fun x : ℝ => (SignType.sign x : Int)) context
      (Transport.polynomial read head) (Transport.polynomial read test)
      (Transport.endpoint read a) (Transport.endpoint read b)
      value (Transport.query read id cert) = true := by
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨coverage, headChecked⟩, squarefree⟩, remainders⟩, accepted⟩ := accepted
  have same := SignInputs.certificate_check_congr (cached lookup)
    (sign lookup read) context head test a b value cert
    (fun x member => cached_eq lookup _ coverage x member read)
  rw [same] at accepted
  exact transport read closed (sign lookup read) (fun x => (sign_spec lookup read sound x).symm)
    context head test a b value cert (leading_spec lookup read sound head headChecked)
    (fun r member => leading_spec lookup read sound r
      (Array.all_eq_true_iff_forall_mem.mp squarefree r member))
    (fun r member => leading_spec lookup read sound r
      (Array.all_eq_true_iff_forall_mem.mp remainders r member)) accepted

theorem missing_rejects {C : Type v} [DecidableEq C]
    (lookup : E → Option Int) (context : C) (head test : DensePoly E)
    (a b : Endpoint E) (value : Int) (cert : TarskiCertificate E E C)
    (x : E) (member : x ∈ SignInputs.certificate head a b cert)
    (missing : lookup x = none) : check lookup context head test a b value cert = false := by
  have absent : covered lookup (SignInputs.certificate head a b cert) = false := by
    cases result : covered lookup (SignInputs.certificate head a b cert) with
    | false => rfl
    | true =>
      have present := List.all_eq_true.mp result x member
      simp [missing] at present
  simp only [check, absent, Bool.false_and]

end Hex.RCF.RealCoefficients.QueryReplay
