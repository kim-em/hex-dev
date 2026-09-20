/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PolyOps.Basic

public section

/-! Explicit coefficient callbacks and checked claims. An operation record fixes the context;
evidence is indexed by the entire claim, including operands and proposed output. The carrier
needs neither structural equality nor algebraic instances. -/

namespace Hex.PolyOps
universe u v w

/-- Claims interpreted in the fixed context of a coefficient record. -/
inductive Claim (C : Type u) where
  | valid (a : C)
  | add (a b result : C)
  | mul (a b result : C)
  | neg (a result : C)
  | zero (a : C) (result : Bool)
  | sign (a : C) (result : Sign)
  | inverse (a result : C)
  | division (a b result : C)

/-- A mathematical zero-divisor violation retains the operand and its zero evidence. -/
structure ZeroDivisor {C : Type u} (Evidence : Claim C → Type v) where
  divisor : C
  evidence : Evidence (.zero divisor true)

/-- Pure Lean producers and structurally terminating replay. Successful producers propose
certificates; clients use the checked wrappers below. Each producer must reserve its own
allocations and charge any nested work to its incoming budget, including on failure. -/
structure CoeffOps (C : Type u) where
  Evidence : Claim C → Type v
  zero : C
  one : C
  check : (claim : Claim C) → Budget → Evidence claim → CheckResult
  validate : (a : C) → Computation (ZeroDivisor Evidence) (Evidence (.valid a))
  add : (a b : C) → Computation (ZeroDivisor Evidence) ((c : C) × Evidence (.add a b c))
  mul : (a b : C) → Computation (ZeroDivisor Evidence) ((c : C) × Evidence (.mul a b c))
  neg : (a : C) → Computation (ZeroDivisor Evidence) ((c : C) × Evidence (.neg a c))
  zeroTest : (a : C) → Computation (ZeroDivisor Evidence) ((z : Bool) × Evidence (.zero a z))
  sign : (a : C) → Computation (ZeroDivisor Evidence) ((s : Sign) × Evidence (.sign a s))

/-- Inversion is a separate capability; the ring kernel never requests it. -/
structure FieldOps (C : Type u) extends CoeffOps.{u,v} C where
  inv : (a : C) → Computation (ZeroDivisor Evidence) ((c : C) × Evidence (.inverse a c))

/-- Optional exact division, independent of field inversion. Failure to find a quotient is
exhaustion, whereas evidence for a false proposed quotient is rejected. -/
structure ExactOps (C : Type u) extends CoeffOps.{u,v} C where
  divExact : (a b : C) →
    Computation (ZeroDivisor Evidence) ((c : C) × Evidence (.division a b c))

namespace CoeffOps

abbrev Failure (ops : CoeffOps C) := ZeroDivisor ops.Evidence
abbrev Run (ops : CoeffOps C) (α : Type w) := Computation ops.Failure α

/-- Replay charges both the call and the claim before entering the checker. -/
@[expose] def checkWith (ops : CoeffOps C) (claim : Claim C) (e : ops.Evidence claim) :
    ops.Run Unit := do
  charge .replay
  invoke fun b => (ops.check claim b e).result

/-- Check mathematical failure evidence as well as successful evidence. A fabricated domain
violation cannot reach a public wrapper merely by selecting the invalid constructor. -/
@[expose] def call (ops : CoeffOps C) (f : ops.Run α) : ops.Run α := fun b =>
  match invoke f b with
  | .invalid (.domain message e) rest =>
    (ops.checkWith (.zero e.divisor true) e.evidence rest).bind fun _ rest' =>
      .invalid (.domain message e) rest'
  | r => r

@[expose] def validateWith (ops : CoeffOps C) (a : C) : ops.Run (ops.Evidence (.valid a)) := do
  let e ← ops.call (ops.validate a)
  ops.checkWith (.valid a) e
  return e

@[expose] def addWith (ops : CoeffOps C) (a b : C) :
    ops.Run ((c : C) × ops.Evidence (.add a b c)) := do
  let r ← ops.call (ops.add a b)
  ops.checkWith (.add a b r.1) r.2
  return r

@[expose] def mulWith (ops : CoeffOps C) (a b : C) :
    ops.Run ((c : C) × ops.Evidence (.mul a b c)) := do
  let r ← ops.call (ops.mul a b)
  ops.checkWith (.mul a b r.1) r.2
  return r

@[expose] def negWith (ops : CoeffOps C) (a : C) :
    ops.Run ((c : C) × ops.Evidence (.neg a c)) := do
  let r ← ops.call (ops.neg a)
  ops.checkWith (.neg a r.1) r.2
  return r

@[expose] def zeroWith (ops : CoeffOps C) (a : C) :
    ops.Run ((z : Bool) × ops.Evidence (.zero a z)) := do
  charge .decisions
  let r ← ops.call (ops.zeroTest a)
  ops.checkWith (.zero a r.1) r.2
  return r

@[expose] def signWith (ops : CoeffOps C) (a : C) :
    ops.Run ((s : Sign) × ops.Evidence (.sign a s)) := do
  charge .decisions
  let r ← ops.call (ops.sign a)
  ops.checkWith (.sign a r.1) r.2
  return r

end CoeffOps

/-- Checked inversion first decides zero. The zero case retains checked evidence; an unknown
zero decision propagates exhaustion without ever calling inversion. -/
@[expose] def FieldOps.invWith (ops : FieldOps C) (a : C) :
    ops.toCoeffOps.Run ((c : C) × ops.Evidence (.inverse a c)) := do
  let z ← ops.zeroWith a
  if h : z.1 = true then
    fun b => .invalid (.domain "zero divisor" ⟨a, h ▸ z.2⟩) b
  else
    let r ← ops.call (ops.inv a)
    ops.checkWith (.inverse a r.1) r.2
    return r

@[expose] def ExactOps.divWith (ops : ExactOps C) (a b : C) :
    ops.toCoeffOps.Run ((c : C) × ops.Evidence (.division a b c)) := do
  let z ← ops.zeroWith b
  if h : z.1 = true then
    fun rest => .invalid (.domain "zero divisor" ⟨b, h ▸ z.2⟩) rest
  else
    let r ← ops.call (ops.divExact a b)
    ops.checkWith (.division a b r.1) r.2
    return r

end Hex.PolyOps
