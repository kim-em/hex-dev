/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportQuery
public import HexRealClosureMathlib.TransportPower

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Interpret finite endpoint values and retain both infinities. -/
@[expose] def endpoint (read : E → K) : Hex.Endpoint E → Hex.Endpoint K
  | .negInf => .negInf
  | .finite x => .finite (read x)
  | .posInf => .posInf

variable [Add E] [Sub E] [Mul E]

/-- Finite products and sums at the actual descending Horner accumulators. -/
structure Evaluation (read : E → K) (p : Hex.DensePoly E) (x : E) : Prop where
  products : ∀ i < p.size,
    read (hornerPrefix p x i * x) = read (hornerPrefix p x i) * read x
  sums : ∀ i < p.size,
    read (hornerPrefix p x i * x + p.coeff (p.size - 1 - i)) =
      read (hornerPrefix p x i * x) + read (p.coeff (p.size - 1 - i))

/-- An endpoint records only the scalar sign queried there: a reached Horner
result at a finite endpoint, or the leading coefficient at infinity. -/
@[expose] def EndpointData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p : Hex.DensePoly E) (a : Hex.Endpoint E) : Prop :=
  Leading read p ∧ match a with
    | .finite x => Evaluation read p x ∧ targetSign (read (p.eval x)) = sourceSign (p.eval x)
    | _ => targetSign (read p.leadingCoeff) = sourceSign p.leadingCoeff

/-- Endpoint signs transport their literal finite arithmetic and scalar signs. -/
theorem endpoint_sign (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E) (a : Hex.Endpoint E)
    (data : EndpointData read sourceSign targetSign p a) :
    (endpoint read a).signAt targetSign (Hex.EndpointSigns.ofSign targetSign) (polynomial read p) =
      a.signAt sourceSign (Hex.EndpointSigns.ofSign sourceSign) p := by
  cases a with
  | negInf =>
    simp only [endpoint, Hex.Endpoint.signAt, polynomial_leading read zero p data.1,
      polynomial_degree read zero p data.1]
    rw [data.2]
  | posInf =>
    simp only [endpoint, Hex.Endpoint.signAt, polynomial_leading read zero p data.1]
    exact data.2
  | finite x =>
    simp only [endpoint, Hex.Endpoint.signAt, Hex.EndpointSigns.ofSign]
    rw [← Ring.polynomial_eval read zero p x data.2.1.products data.2.1.sums]
    exact data.2.2

/-- The same finite evaluation sign retains endpoint nonvanishing guards. -/
theorem endpoint_nonvanishing (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E) (a : Hex.Endpoint E)
    (data : EndpointData read sourceSign targetSign p a) :
    (endpoint read a).nonvanishing (Hex.EndpointSigns.ofSign targetSign) (polynomial read p) =
      a.nonvanishing (Hex.EndpointSigns.ofSign sourceSign) p := by
  cases a with
  | negInf => rfl
  | posInf => rfl
  | finite x =>
    have signs := endpoint_sign read zero sourceSign targetSign p (.finite x) data
    change (targetSign ((polynomial read p).eval (read x)) != 0) =
      (sourceSign (p.eval x) != 0)
    rw [show targetSign ((polynomial read p).eval (read x)) = sourceSign (p.eval x) from signs]

/-- Finite endpoint comparison records the actual scalar difference and sign. -/
@[expose] def OrderData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (a b : Hex.Endpoint E) : Prop :=
  match a, b with
  | .finite x, .finite y => read (x - y) = read x - read y ∧
      targetSign (read (x - y)) = sourceSign (x - y)
  | _, _ => True

/-- Exact endpoint ordering transports its finite difference and sign. -/
theorem endpoint_lt (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (a b : Hex.Endpoint E) (data : OrderData read sourceSign targetSign a b) :
    (endpoint read a).lt (Hex.EndpointSigns.ofSign targetSign) (endpoint read b) =
      a.lt (Hex.EndpointSigns.ofSign sourceSign) b := by
  cases a <;> cases b <;> simp only [endpoint, Hex.Endpoint.lt, Hex.EndpointSigns.ofSign]
  rename_i x y
  apply congrArg (fun s : Int => decide (s < 0))
  exact (congrArg targetSign data.1.symm).trans data.2

/-- Interpret literal certificate inputs and chains while retaining all stored
signs, variation counts and the claimed integer value. Contexts map explicitly. -/
@[expose] def query {C : Type w} {D : Type z} (read : E → K) (context : C → D)
    (cert : Hex.TarskiCertificate E E C) : Hex.TarskiCertificate K K D :=
  { context := context cert.context
    head := polynomial read cert.head
    queryPoly := polynomial read cert.queryPoly
    lower := endpoint read cert.lower
    upper := endpoint read cert.upper
    squarefree := chain read cert.squarefree
    remainders := chain read cert.remainders
    lowerSigns := cert.lowerSigns
    upperSigns := cert.upperSigns
    lowerVariations := cert.lowerVariations
    upperVariations := cert.upperVariations
    value := cert.value }

variable [One E] [NatCast E]

/-- Finite obligations of the two stored chain checks and every endpoint
comparison and sign queried by the full Tarski checker. -/
structure QueryData {C : Type w} (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p f : Hex.DensePoly E) (a b : Hex.Endpoint E) (cert : Hex.TarskiCertificate E E C) : Prop where
  squarefree : ChainData read sourceSign targetSign p 1 cert.squarefree
  remainders : ChainData read sourceSign targetSign p f cert.remainders
  order : OrderData read sourceSign targetSign a b
  lower : EndpointData read sourceSign targetSign p a
  upper : EndpointData read sourceSign targetSign p b
  lowerRows : ∀ r ∈ cert.remainders.chain, EndpointData read sourceSign targetSign r a
  upperRows : ∀ r ∈ cert.remainders.chain, EndpointData read sourceSign targetSign r b

/-- Complete accepted Tarski replay transports the finite arithmetic and sign
obligations. Literal bindings, both chain checks, guards, signs, variations and
value all refer to the supplied certificate; no producer or division runs. -/
theorem query_check {C : Type w} {D : Type z} [DecidableEq C] [DecidableEq D]
    (read : E → K) (zero : read 0 = 0) (one : read 1 = 1) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (p f : Hex.DensePoly E) (a b : Hex.Endpoint E) (value : Int)
    (cert : Hex.TarskiCertificate E E C) (data : QueryData read sourceSign targetSign p f a b cert)
    (accepted : Hex.TarskiCertificate.check sourceSign (Hex.EndpointSigns.ofSign sourceSign)
      context p f a b value cert = true) :
    Hex.TarskiCertificate.check targetSign (Hex.EndpointSigns.ofSign targetSign)
      (contextMap context) (polynomial read p) (polynomial read f)
      (endpoint read a) (endpoint read b) value (query read contextMap cert) = true := by
  have map_signs e (rows : ∀ r ∈ cert.remainders.chain,
      EndpointData read sourceSign targetSign r e) :
      Hex.TarskiCertificate.signs targetSign (Hex.EndpointSigns.ofSign targetSign)
        (chain read cert.remainders).chain (endpoint read e) =
      Hex.TarskiCertificate.signs sourceSign (Hex.EndpointSigns.ofSign sourceSign)
        cert.remainders.chain e := by
    simp only [Hex.TarskiCertificate.signs, Hex.Array.map'_eq_map, chain, Array.map_map]
    apply Array.ext (by simp)
    intro i hi hj
    simp only [Array.getElem_map]
    have bound : i < cert.remainders.chain.size := by simpa using hi
    exact endpoint_sign read zero sourceSign targetSign cert.remainders.chain[i] e
      (rows _ (by simp))
  have last_constant : Hex.SignedRemainderChain.lastIsConstant (chain read cert.squarefree) =
      Hex.SignedRemainderChain.lastIsConstant cert.squarefree := by
    simp only [Hex.SignedRemainderChain.lastIsConstant,
      show (chain read cert.squarefree).chain.size = cert.squarefree.chain.size by simp [chain],
      chain_entry read zero]
    congr 1
    apply polynomial_size read zero
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.squarefree.chain[cert.squarefree.chain.size - 1]? with
    | none => simp only [Option.getD_none]; intro h; simp at h
    | some r =>
      simp only [Option.getD_some]
      exact data.squarefree.entries r (Array.mem_of_getElem? h)
  have ends : Hex.TarskiCertificate.checkEndpoints (Hex.EndpointSigns.ofSign targetSign)
      (polynomial read p) (endpoint read a) (endpoint read b) =
      Hex.TarskiCertificate.checkEndpoints (Hex.EndpointSigns.ofSign sourceSign) p a b := by
    simp only [Hex.TarskiCertificate.checkEndpoints, polynomial_isZero read zero p data.lower.1]
    rw [endpoint_lt read sourceSign targetSign a b data.order,
      endpoint_nonvanishing read zero sourceSign targetSign p a data.lower,
      endpoint_nonvanishing read zero sourceSign targetSign p b data.upper]
  simp only [Hex.TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at accepted
  obtain ⟨hctx, hp, hf, ha, hb, hv, he, hsf, hc, hr, hls, hus, hbl, hbu, hvl, hvu, hval⟩ := accepted
  have square := chain_check read zero sourceSign targetSign p 1 cert.squarefree data.squarefree hsf
  rw [polynomial_one read zero one] at square
  have rem := chain_check read zero sourceSign targetSign p f cert.remainders data.remainders hr
  simp only [Hex.TarskiCertificate.check_eq, query, hctx, hp, hf, ha, hb, hv, ends,
    square, rem, last_constant, hc, he, map_signs a data.lowerRows, map_signs b data.upperRows,
    hls, hus, hvl, hvu, decide_true, Bool.true_and]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, true_and]
  exact ⟨by simpa only [hls] using hbl, by simpa only [hus] using hbu,
    by simpa only [hvl, hls, hvu, hus] using hval⟩

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.endpoint_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.endpoint_sign
/-- info: 'Hex.RealClosure.Transport.endpoint_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.endpoint_nonvanishing
/-- info: 'Hex.RealClosure.Transport.endpoint_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.endpoint_lt
/-- info: 'Hex.RealClosure.Transport.query_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.query_check
