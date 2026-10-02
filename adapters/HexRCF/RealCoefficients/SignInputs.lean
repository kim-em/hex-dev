/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.LiteralSign
public import HexRCF.RealCoefficients.IsolationCheck
public import HexRCF.Soundness
public import HexRealRoots.SignOperands

public section

/-! Collect the finite coefficient signs read by shared Tarski replay. -/

namespace Hex.RCF.RealCoefficients.SignInputs

open Hex

variable {D : Type u} [Zero D] [DecidableEq D]

/-- The shared core inventory of literal chain scale signs. -/
@[expose] def chain (cert : SignedRemainderChain D) : List D :=
  cert.signOperands

/-- The coefficient passed to `sign` at one finite or infinite endpoint. -/
@[expose] def endpoint [Add D] [Mul D]
    (q : DensePoly D) (bound : Endpoint D) : List D :=
  [bound.signOperand q]

/-- The shared finite-endpoint order and nonvanishing operands. -/
@[expose] def guards [Sub D] [Add D] [Mul D]
    (head : DensePoly D) (lower upper : Endpoint D) : List D :=
  Endpoint.orderOperands lower upper ++ lower.nonvanishingOperands head ++
    upper.nonvanishingOperands head

/-- Reuse the core finite sign inventory for this literal Tarski replay.
The caller may deduplicate by exact coordinate equality before building its
finite rational sign table. The inventory describes result dependencies,
not an ordered trace of runtime calls. -/
@[expose] def certificate [Sub D] [Add D] [Mul D] {Ctx : Type v}
    (head : DensePoly D) (lower upper : Endpoint D)
    (cert : TarskiCertificate D D Ctx) : List D :=
  TarskiCertificate.signOperands head lower upper cert

/-- Sign arguments read when an isolation replay checks its total count and
each count-one interval. -/
@[expose] def isolation [One D] [Sub D] [Add D] [Mul D]
    {Ctx : Type v} (point : Dyadic → D) (head : DensePoly D)
    (cert : IsolationReplay D Ctx) : List D :=
  certificate head .negInf .posInf cert.total ++
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      certificate head (.finite (point interval.lower))
        (.finite (point interval.upper)) cert.counts[i]

/-- Sign arguments read by one query on each isolated root. The supplied
query polynomials and certificates must be bound to the same cell indices. -/
@[expose] def rootQueries [Sub D] [Add D] [Mul D]
    {Ctx : Type v} (point : Dyadic → D) (head : DensePoly D)
    (cert : IsolationReplay D Ctx) (queries : List (Fin cert.isolations.intervals.size →
      TarskiCertificate D D Ctx)) : List D :=
  queries.flatMap fun query =>
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      certificate head (.finite (point interval.lower))
        (.finite (point interval.upper)) (query i)

/-- Open-cell sample values used directly by formula evaluation. They are not
part of a Tarski certificate, but the finite field sign table must record them
just as it records signs read while checking certificates. -/
@[expose] def openSamples [Add D] [Mul D] {Ctx : Type v}
    (point : Dyadic → D) (cert : IsolationReplay D Ctx)
    (queries : List (DensePoly D)) : List D :=
  (Cell.all cert.isolations.intervals.size).toList.flatMap fun cell =>
    match cell with
    | .open cut =>
        queries.map fun q => q.eval (point (cert.isolations.openPoint cut))
    | .root _ => []

/-- The shared core chain congruence, specialized to the adapter inventory. -/
theorem chain_check_congr [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    (sign₁ sign₂ : D → Int) (p q : DensePoly D) (cert : SignedRemainderChain D)
    (h : ∀ x ∈ chain cert, sign₁ x = sign₂ x) :
    SignedRemainderChain.check sign₁ p q cert =
      SignedRemainderChain.check sign₂ p q cert :=
  SignedRemainderChain.check_sign_congr sign₁ sign₂ p q cert h

/-- Finite agreement preserves the adapter's existing shared query checker. -/
theorem certificate_check_congr [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    {Ctx : Type v} [DecidableEq Ctx]
    (sign₁ sign₂ : D → Int) (context : Ctx)
    (head query : DensePoly D) (lower upper : Endpoint D) (value : Int)
    (cert : TarskiCertificate D D Ctx)
    (h : ∀ x ∈ certificate head lower upper cert, sign₁ x = sign₂ x) :
    Sturm.check sign₁ context head query lower upper value cert =
      Sturm.check sign₂ context head query lower upper value cert :=
  TarskiCertificate.check_sign_congr sign₁ sign₂ context head query lower upper value cert h

end Hex.RCF.RealCoefficients.SignInputs
