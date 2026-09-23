/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.LiteralSign

public section

/-! Collect the finite coefficient signs read by shared Tarski replay. -/

namespace Hex.RCF.RealCoefficients.SignInputs

open Hex

variable {D : Type u} [Zero D] [DecidableEq D]

/-- Scale signs tested by the literal signed-remainder-chain checker. -/
@[expose] def chain (cert : SignedRemainderChain D) : List D :=
  [cert.initial.leftScale, cert.initial.rightScale] ++
    cert.steps.toList.flatMap (fun step => [step.leftScale, step.rightScale]) ++
    cert.terminal.toList.map Prod.fst

/-- The coefficient passed to `sign` at one finite or infinite endpoint. -/
@[expose] def endpoint [Add D] [Mul D]
    (q : DensePoly D) (bound : Endpoint D) : List D :=
  match bound with
  | .finite a => [q.eval a]
  | .negInf | .posInf => [q.leadingCoeff]

/-- Inputs read by the endpoint guards for a caller-supplied head and interval. -/
@[expose] def guards [Sub D] [Add D] [Mul D]
    (head : DensePoly D) (lower upper : Endpoint D) : List D :=
  (match lower, upper with
   | .finite a, .finite b => [a - b]
   | _, _ => []) ++
  (match lower with | .finite a => [head.eval a] | _ => []) ++
  (match upper with | .finite b => [head.eval b] | _ => [])

/-- Every sign argument present in a checked Tarski query is reconstructed
from the caller's literal head and endpoints and the supplied chain entries.
The caller may deduplicate this list by exact coordinate equality before
building its finite rational sign table. -/
@[expose] def certificate [Sub D] [Add D] [Mul D] {Ctx : Type v}
    (head : DensePoly D) (lower upper : Endpoint D)
    (cert : TarskiCertificate D D Ctx) : List D :=
  guards head lower upper ++ chain cert.squarefree ++ chain cert.remainders ++
    cert.remainders.chain.toList.flatMap (fun q => endpoint q lower ++ endpoint q upper)

end Hex.RCF.RealCoefficients.SignInputs
