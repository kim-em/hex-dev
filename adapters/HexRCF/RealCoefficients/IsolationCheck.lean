/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.SeparationCheck
public import HexSturm.Basic

public section

namespace Hex.RCF.RealCoefficients

/-- Existing dyadic cell isolations with shared Sturm–Tarski evidence for
one root in each interval and for the total number of distinct real roots. -/
structure IsolationReplay (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E] where
  /-- The dyadic intervals in cell order. The older `IsolationCert` Sturm
  checkers are not consulted; `IsolationReplay.check` uses open Tarski queries. -/
  isolations : IsolationCert
  /-- Constant-one query on the entire real line. -/
  total : TarskiCertificate E E Ctx
  /-- Constant-one queries bound to the interval at each index. -/
  counts : Vector (TarskiCertificate E E Ctx) isolations.intervals.size

namespace IsolationReplay

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Bind every root-count certificate to the actual head, context and dyadic
endpoints. Shared queries use open intervals with root-free endpoints; strict
separation reuses the rational solver's gap checker. -/
@[expose] def check (sign : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx) : Bool :=
  cert.isolations.checkGaps &&
    Sturm.check sign context head 1 .negInf .posInf
      cert.isolations.intervals.size cert.total &&
    (List.finRange cert.isolations.intervals.size).all (fun i =>
      let interval := cert.isolations.intervals[i]
      Sturm.check sign context head 1 (.finite (point interval.lower))
        (.finite (point interval.upper)) 1 cert.counts[i])

/-- Recover the exact per-interval query check without recomputing any chain. -/
theorem count_checked (sign : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (cert : IsolationReplay E Ctx)
    (h : cert.check sign point context head = true) (i : Fin cert.isolations.intervals.size) :
    Sturm.check sign context head 1
      (.finite (point cert.isolations.intervals[i].lower))
      (.finite (point cert.isolations.intervals[i].upper)) 1 cert.counts[i] = true := by
  simp only [check, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 i (List.mem_finRange i)

/-- Certify a proposed isolation using one prepared query for the constant
polynomial one. The same recorded chains are evaluated at each interval's
endpoints; the final checker rejects missing roots, overlaps and bad endpoints. -/
def build [Neg E] [Inv E] (sign : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (isolations : IsolationCert) : Option (IsolationReplay E Ctx) :=
  match Sturm.prepare sign head .negInf .posInf with
  | none => none
  | some domain =>
    let total := Sturm.certifyPrepared context domain 1
    let counts := Vector.ofFn fun i : Fin isolations.intervals.size =>
      let interval := isolations.intervals[i]
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) context head 1
        (.finite (point interval.lower)) (.finite (point interval.upper)) total.squarefree total.remainders
    let cert : IsolationReplay E Ctx := ⟨isolations, total, counts⟩
    if cert.check sign point context head then some cert else none

/-- Query a proposed single-root interval using the same checked head and
squarefree chain. Query-dependent remainders are recomputed by the shared
Sturm producer; replay checks the resulting literal certificate separately. -/
@[expose] def queryAt [Neg E] [Inv E] (sign : E → Int) (point : Dyadic → E)
    (context : Ctx) (head q : DensePoly E) (cert : IsolationReplay E Ctx)
    (i : Fin cert.isolations.intervals.size) : TarskiCertificate E E Ctx :=
  let interval := cert.isolations.intervals[i]
  TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) context head q
    (.finite (point interval.lower)) (.finite (point interval.upper))
    cert.total.squarefree
    (SignedRemainderChain.build sign (Sturm.normalize sign) head q)

/-- A successful builder returns exactly the proposed intervals and evidence
accepted by the same checker used for arbitrary certificates. -/
theorem build_checked [Neg E] [Inv E] (sign : E → Int) (point : Dyadic → E) (context : Ctx)
    (head : DensePoly E) (isolations : IsolationCert) (cert : IsolationReplay E Ctx)
    (h : build sign point context head isolations = some cert) :
    cert.isolations = isolations ∧ cert.check sign point context head = true := by
  unfold build at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · cases Option.some.inj h
      exact ⟨rfl, ‹_›⟩
    · contradiction

end IsolationReplay
end Hex.RCF.RealCoefficients
