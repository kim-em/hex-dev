/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Std

public section

/-! Shared outcomes and cumulative resource accounting for fallible polynomial arithmetic.
A resource counts logical work, not elapsed time or the cost of one big-integer operation.
Every outcome retains its remaining budget; only success carries an arithmetic result. -/

namespace Hex.PolyOps

/-- Exact signs, independent of any coefficient representation. -/
inductive Sign where
  | negative | zero | positive
  deriving DecidableEq, Repr, Inhabited

@[expose] def Sign.toInt : Sign → Int
  | .negative => -1
  | .zero => 0
  | .positive => 1

@[expose] def Sign.ofInt (n : Int) : Sign :=
  if n < 0 then .negative else if n = 0 then .zero else .positive

@[simp] theorem Sign.ofInt_toInt (s : Sign) : ofInt s.toInt = s := by
  cases s <;> decide

theorem Sign.toInt_ofInt (n : Int) (h : n = -1 ∨ n = 0 ∨ n = 1) :
    (ofInt n).toInt = n := by
  rcases h with h | h | h <;> subst n <;> decide

/-- Cumulative charging units. Backends also charge their nested work in these units. -/
inductive Resource where
  | operations | steps | coefficients | decisions | evidenceNodes | evidenceBytes | replay
  deriving DecidableEq, Repr, Inhabited

/-- Initial allowances. Coefficients count allocated array cells. Evidence counters charge
both retained and replayed nodes/bytes, including a producer's immediate check; they measure
cumulative work rather than just final certificate size. Replay counts checked claims. -/
structure Limits where
  allowance : Resource → Nat

/-- Remaining allowances, shared by producers, callbacks and replay. -/
structure Budget where
  operations : Nat
  steps : Nat
  coefficients : Nat
  decisions : Nat
  evidenceNodes : Nat
  evidenceBytes : Nat
  replay : Nat
  deriving DecidableEq, Repr

@[expose] def Budget.remaining (b : Budget) : Resource → Nat
  | .operations => b.operations
  | .steps => b.steps
  | .coefficients => b.coefficients
  | .decisions => b.decisions
  | .evidenceNodes => b.evidenceNodes
  | .evidenceBytes => b.evidenceBytes
  | .replay => b.replay

/-- Materialize the counters once; spending never retains a chain of earlier budgets. -/
@[expose] def Budget.ofFn (f : Resource → Nat) : Budget :=
  ⟨f .operations, f .steps, f .coefficients, f .decisions,
   f .evidenceNodes, f .evidenceBytes, f .replay⟩

@[simp] theorem Budget.remaining_ofFn (f : Resource → Nat) (r : Resource) :
    (ofFn f).remaining r = f r := by cases r <;> rfl

@[expose] def Limits.budget (limits : Limits) : Budget := .ofFn limits.allowance
@[expose] def Limits.uniform (n : Nat) : Limits := ⟨fun _ => n⟩

/-- A child may consume resources but cannot replenish them. -/
@[expose] def Budget.Within (child parent : Budget) : Prop :=
  ∀ r, child.remaining r ≤ parent.remaining r

instance (a b : Budget) : Decidable (a.Within b) :=
  decidable_of_iff
    (a.remaining .operations ≤ b.remaining .operations ∧
     a.remaining .steps ≤ b.remaining .steps ∧
     a.remaining .coefficients ≤ b.remaining .coefficients ∧
     a.remaining .decisions ≤ b.remaining .decisions ∧
     a.remaining .evidenceNodes ≤ b.remaining .evidenceNodes ∧
     a.remaining .evidenceBytes ≤ b.remaining .evidenceBytes ∧
     a.remaining .replay ≤ b.remaining .replay)
    (by constructor
        · intro h r; cases r <;> simp_all
        · intro h; exact ⟨h _, h _, h _, h _, h _, h _, h _⟩)

@[expose] def Budget.cap (a b : Budget) : Budget :=
  .ofFn fun r => min (a.remaining r) (b.remaining r)

/-- Charge before starting work. An unsuccessful reservation consumes no resources. -/
@[expose] def Budget.spend (b : Budget) (r : Resource) (n : Nat) : Option Budget :=
  if n ≤ b.remaining r then
    some (.ofFn fun s => if s = r then b.remaining s - n else b.remaining s)
  else none

theorem Budget.spend_within {b b' : Budget} {r : Resource} {n : Nat}
    (h : b.spend r n = some b') : b'.Within b := by
  unfold spend at h
  split at h
  · cases h
    intro s
    simp only [remaining_ofFn]
    split <;> omega
  · contradiction

/-- Mathematical failures retain their typed evidence. Diagnostic messages are not tags. -/
inductive Invalid (E : Type u) where
  | malformed (message : String)
  | context (message : String)
  | domain (message : String) (evidence : E)
  deriving Repr

inductive Exhaustion where
  | resource (which : Resource)
  | unavailable (message : String)
  deriving DecidableEq, Repr

inductive Rejection where
  /-- A supplied certificate is malformed or its claim is false. -/
  | evidence (message : String)
  /-- A callback attempted to replenish a resource counter. -/
  | budgetIncrease
  /-- An internal assertion or a helper precondition failed on checked data. -/
  | invariant (message : String)
  deriving DecidableEq, Repr

/-- Common internal outcome. Evidence for successful values belongs in the value's type;
`E` is the evidence type for certified mathematical domain violations. -/
inductive Result (α : Type u) (E : Type v := PEmpty) where
  | ok (value : α) (budget : Budget)
  | invalid (reason : Invalid E) (budget : Budget)
  | exhausted (reason : Exhaustion) (budget : Budget)
  | rejected (reason : Rejection) (budget : Budget)

@[expose] def Result.budget : Result α E → Budget
  | .ok _ b | .invalid _ b | .exhausted _ b | .rejected _ b => b

@[expose] def Result.isSome : Result α E → Bool
  | .ok .. => true
  | _ => false

@[expose] def Result.bind (r : Result α E) (f : α → Budget → Result β E) : Result β E :=
  match r with
  | .ok a b => f a b
  | .invalid e b => .invalid e b
  | .exhausted e b => .exhausted e b
  | .rejected e b => .rejected e b

/-- Refuse an untrusted callback's attempt to replenish a counter, on every outcome. -/
@[expose] def Result.constrain (r : Result α E) (parent : Budget) : Result α E :=
  if r.budget.Within parent then r
  else .rejected .budgetIncrease (r.budget.cap parent)

theorem Result.constrain_within (r : Result α E) (b : Budget) :
    (r.constrain b).budget.Within b := by
  unfold constrain
  split
  · assumption
  · intro s
    simpa only [Result.budget, Budget.cap, Budget.remaining_ofFn] using
      Nat.min_le_right (r.budget.remaining s) (b.remaining s)

theorem Result.bind_ok {r : Result α E} {f : α → Budget → Result β E} {v : β} {b : Budget}
    (h : r.bind f = .ok v b) : ∃ a rest, r = .ok a rest ∧ f a rest = .ok v b := by
  cases r with
  | ok a rest => exact ⟨a, rest, rfl, h⟩
  | invalid => contradiction
  | exhausted => contradiction
  | rejected => contradiction

theorem Result.constrain_ok {r : Result α E} {parent b : Budget} {a : α}
    (h : r.constrain parent = .ok a b) : r = .ok a b := by
  unfold constrain at h
  split at h
  · exact h
  · contradiction

/-- Change only the domain-evidence payload when composing library layers. -/
@[expose] def Result.mapDomain (f : E → F) : Result α E → Result α F
  | .ok a b => .ok a b
  | .invalid (.domain m e) b => .invalid (.domain m (f e)) b
  | .invalid (.malformed m) b => .invalid (.malformed m) b
  | .invalid (.context m) b => .invalid (.context m) b
  | .exhausted e b => .exhausted e b
  | .rejected e b => .rejected e b

/-- Evidence checking has no invalid-input outcome: a false claim is rejected. -/
inductive CheckResult where
  | accepted (budget : Budget)
  | rejected (reason : Rejection) (budget : Budget)
  | exhausted (reason : Exhaustion) (budget : Budget)

@[expose] def CheckResult.budget : CheckResult → Budget
  | .accepted b | .rejected _ b | .exhausted _ b => b

@[expose] def CheckResult.result : CheckResult → Result Unit E
  | .accepted b => .ok () b
  | .rejected e b => .rejected e b
  | .exhausted e b => .exhausted e b

/-- A pure, terminating computation which explicitly receives the parent's allowance. -/
abbrev Computation (E : Type v) (α : Type u) := Budget → Result α E

instance : Monad (Computation E) where
  pure a := fun b => .ok a b
  bind f g := fun b => (f b).bind g

@[expose] def charge (r : Resource) (n : Nat := 1) : Computation E Unit := fun b =>
  match b.spend r n with
  | some b' => .ok () b'
  | none => .exhausted (.resource r) b

/-- Invoke a child only after reserving a call, including when the child fails. -/
@[expose] def invoke (f : Computation E α) : Computation E α := fun b =>
  (charge .operations 1 b).bind fun _ b' => (f b').constrain b'

theorem invoke_ok {f : Computation E α} {b b' : Budget} {a : α}
    (h : invoke f b = .ok a b') : ∃ rest, f rest = .ok a b' := by
  obtain ⟨_, rest, _, h⟩ := Result.bind_ok h
  exact ⟨rest, Result.constrain_ok h⟩

/-- Structured public invalidity retains the distinction between input and replay failures. -/
inductive PublicInvalid where
  | malformed (message : String)
  | context (message : String)
  | rejected (reason : Rejection)
  deriving DecidableEq, Repr

/-- Public wrapper used by ordered-function clients. Its mapping preserves every counter. -/
inductive PublicResult (α : Type u) (E : Type v) where
  | ok (value : α) (budget : Budget)
  | exhausted (reason : Exhaustion) (budget : Budget)
  | domain (message : String) (evidence : E) (budget : Budget)
  | invalid (reason : PublicInvalid) (budget : Budget)

@[expose] def PublicResult.budget : PublicResult α E → Budget
  | .ok _ b | .exhausted _ b | .domain _ _ b | .invalid _ b => b

@[expose] def PublicResult.isSome : PublicResult α E → Bool
  | .ok .. => true
  | _ => false

/-- Classify an already checked internal outcome. This mapping does not authenticate raw
producer output; mathematical failures must first pass through the coefficient checker. -/
@[expose] def Result.toPublic : Result α E → PublicResult α E
  | .ok a b => .ok a b
  | .exhausted e b => .exhausted e b
  | .invalid (.domain m e) b => .domain m e b
  | .invalid (.malformed m) b => .invalid (.malformed m) b
  | .invalid (.context m) b => .invalid (.context m) b
  | .rejected e b => .invalid (.rejected e) b

@[simp] theorem Result.toPublic_budget (r : Result α E) : r.toPublic.budget = r.budget := by
  cases r with
  | ok => rfl
  | exhausted => rfl
  | rejected => rfl
  | invalid reason => cases reason <;> rfl

@[simp] theorem Result.toPublic_isSome (r : Result α E) : r.toPublic.isSome = r.isSome := by
  cases r with
  | ok => rfl
  | exhausted => rfl
  | rejected => rfl
  | invalid reason => cases reason <;> rfl

end Hex.PolyOps
