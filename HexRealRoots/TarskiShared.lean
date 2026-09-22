/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski

public section

namespace Hex.TarskiCertificate

variable {D : Type u} {E : Type v} {Ctx : Type w} [Zero D] [DecidableEq D]

/-- Literal domain evidence shared by queries on one head and interval. Context
identity and the entire squarefree witness remain part of the stored data. -/
structure Domain (D : Type u) (E : Type v) (Ctx : Type w) [Zero D] [DecidableEq D] where
  context : Ctx
  head : DensePoly D
  lower : Endpoint E
  upper : Endpoint E
  squarefree : SignedRemainderChain D

/-- Extract the supplied domain literals, without validating them. -/
@[expose] def domain (cert : TarskiCertificate D E Ctx) : Domain D E Ctx :=
  ⟨cert.context, cert.head, cert.lower, cert.upper, cert.squarefree⟩

namespace Domain

variable [One D] [Add D] [Sub D] [Mul D] [NatCast D]

/-- A domain whose actual finite replay has succeeded under these fixed sign
operations. This is independent of producer preparation or root-sum semantics. -/
structure Checked (sign : D → Int) (endpointSigns : EndpointSigns D E) where
  private mk ::
  data : Domain D E Ctx
  accepted : checkDomain sign endpointSigns data.head data.lower data.upper data.squarefree = true

/-- Validate the supplied endpoint guards and squarefree chain once. Invalid
certificate evidence returns `none`; this is not a root-nonexistence test. -/
def replay? (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (raw : Domain D E Ctx) : Option (Checked (Ctx := Ctx) sign endpointSigns) :=
  if h : checkDomain sign endpointSigns raw.head raw.lower raw.upper raw.squarefree = true then
    some ⟨raw, h⟩
  else none

/-- Domain replay preserves every literal field, including context identity. -/
theorem replay_data {sign : D → Int} {endpointSigns : EndpointSigns D E}
    {raw : Domain D E Ctx} {d : Checked (Ctx := Ctx) sign endpointSigns}
    (h : replay? sign endpointSigns raw = some d) : d.data = raw := by
  unfold replay? at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

/-- Reuse requires the caller's exact context, head, interval and squarefree
witness. Equal interpretations never replace these literal bindings. -/
@[expose] def binds [DecidableEq E] [DecidableEq Ctx] (d : Domain D E Ctx)
    (context : Ctx) (p : DensePoly D) (a b : Endpoint E) (squarefree : SignedRemainderChain D) : Bool :=
  decide (d.context = context ∧ d.head = p ∧ d.lower = a ∧ d.upper = b ∧ d.squarefree = squarefree)

end Domain

variable [One D] [Add D] [Sub D] [Mul D] [NatCast D] [DecidableEq E] [DecidableEq Ctx]

/-- The query-dependent part of replay, including all certificate bindings. -/
@[expose] def checkBody (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate D E Ctx) : Bool :=
  checkBindings context p f a b value cert && checkQuery sign endpointSigns p f a b value cert

/-- Check a cache hit against an already replayed domain. A literal mismatch
returns false; use `checkCached` for complete replay with fallback. All query
bindings and query-dependent checks remain mandatory on a hit. -/
@[expose] def checkHit (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (d : Domain.Checked (Ctx := Ctx) sign endpointSigns) (cert : TarskiCertificate D E Ctx) : Bool :=
  d.data.binds context p a b cert.squarefree &&
    checkBody sign endpointSigns context p f a b value cert

/-- Shared replay is precisely full replay with an additional literal-cache
binding guard. The full certificate checker is neither weakened nor bypassed. -/
theorem checkHit_eq (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (d : Domain.Checked (Ctx := Ctx) sign endpointSigns) (cert : TarskiCertificate D E Ctx) :
    checkHit sign endpointSigns context p f a b value d cert =
      (d.data.binds context p a b cert.squarefree &&
        check sign endpointSigns context p f a b value cert) := by
  cases hb : d.data.binds context p a b cert.squarefree with
  | false => simp only [checkHit, hb, Bool.false_and]
  | true =>
    have hd := d.accepted
    have hfields := hb
    simp only [Domain.binds, decide_eq_true_eq] at hfields
    rcases hfields with ⟨_, hp, ha, hb', hs⟩
    rw [hp, ha, hb', hs] at hd
    simp only [checkHit, checkBody, check, hb, hd, Bool.true_and, Bool.and_true]

/-- Boolean elimination rule for the opaque validated-domain constructor.
It exposes every check performed when a raw domain is replayed and then used. -/
theorem checkHit_replay (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (raw : Domain D E Ctx) (cert : TarskiCertificate D E Ctx) :
    (Domain.replay? sign endpointSigns raw).elim false
      (fun d => checkHit sign endpointSigns context p f a b value d cert) =
    (checkDomain sign endpointSigns raw.head raw.lower raw.upper raw.squarefree &&
      raw.binds context p a b cert.squarefree && checkBindings context p f a b value cert &&
      checkQuery sign endpointSigns p f a b value cert) := by
  by_cases h : checkDomain sign endpointSigns raw.head raw.lower raw.upper raw.squarefree = true
  · simp only [Domain.replay?, h, dite_eq_left, Option.elim_some, checkHit, checkBody, Bool.true_and, Bool.and_assoc]
  · have hf := Bool.eq_false_iff.mpr h
    simp only [Domain.replay?, hf, Bool.false_eq_true, ↓reduceDIte, Option.elim_none, Bool.false_and]

/-- Use a validated domain when its literals match. A different squarefree
witness is replayed in full, so a cache miss cannot reject otherwise valid
certificate evidence. The query-dependent checks use the same shared kernel. -/
@[expose] def checkCached (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (cache : Option (Domain.Checked (Ctx := Ctx) sign endpointSigns))
    (cert : TarskiCertificate D E Ctx) : Bool :=
  match cache with
  | none => check sign endpointSigns context p f a b value cert
  | some d =>
    if d.data.binds context p a b cert.squarefree then
      checkBody sign endpointSigns context p f a b value cert
    else check sign endpointSigns context p f a b value cert

/-- Cached replay has exactly the original Boolean result for every supplied
certificate and every validated cache, including cache misses and rejections. -/
theorem checkCached_eq (sign : D → Int) (endpointSigns : EndpointSigns D E)
    (context : Ctx) (p f : DensePoly D) (a b : Endpoint E) (value : Int)
    (cache : Option (Domain.Checked (Ctx := Ctx) sign endpointSigns))
    (cert : TarskiCertificate D E Ctx) :
    checkCached sign endpointSigns context p f a b value cache cert =
      check sign endpointSigns context p f a b value cert := by
  cases cache with
  | none => rfl
  | some d =>
    cases hb : d.data.binds context p a b cert.squarefree with
    | false => simp only [checkCached, hb, Bool.false_eq_true, ↓reduceIte]
    | true =>
      have h := checkHit_eq sign endpointSigns context p f a b value d cert
      simpa only [checkHit, checkCached, hb, Bool.true_and, ↓reduceIte] using h

/-- Arbitrary supplied query evidence accepted using a shared domain also
passes the complete shared-kernel checker, regardless of producer provenance. -/
theorem checkHit_checks {sign : D → Int} {endpointSigns : EndpointSigns D E}
    {context : Ctx} {p f : DensePoly D} {a b : Endpoint E} {value : Int}
    {d : Domain.Checked (Ctx := Ctx) sign endpointSigns} {cert : TarskiCertificate D E Ctx}
    (h : checkHit sign endpointSigns context p f a b value d cert = true) :
    check sign endpointSigns context p f a b value cert = true := by
  rw [checkHit_eq] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

end Hex.TarskiCertificate
