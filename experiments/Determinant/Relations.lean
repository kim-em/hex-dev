/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Compact

/-! Compact monomials with multiplicative signatures. Signatures are optimization
hints only: they never justify an equality. Only monomials with colliding
signatures are normalized, using existing kernel-checked scalar proofs. -/

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Ring.Common
open Mathlib.Tactic.Determinant
namespace Determinant.Relations

register_option det.relations.maxWork : Nat := {
  defValue := 1000000
  descr := "Maximum scalar term visits in the experimental relation normalizer" }

register_option det.relations.trace : Bool := {
  defValue := false
  descr := "Report experimental relation search counters" }

register_option det.relations.maxHeartbeats : Nat := {
  defValue := 2000000
  descr := "Heartbeat limit for the experimental relation backend, including scalar comparison" }

meta section
/-- A local ceiling that never increases the caller's remaining heartbeat allowance. -/
def withBudget {β : Type} (action : MetaM β) : MetaM β := do
  let requested := det.relations.maxHeartbeats.get (← getOptions) * 1000
  unless requested > 0 do throwError "relation heartbeat budget must be positive"
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let remaining := ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  let limit := if ctx.maxHeartbeats == 0 then requested else min remaining requested
  unless limit > 0 do throwError "relation heartbeat budget exhausted"
  withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := now, maxHeartbeats := limit}) action

abbrev Signature := Array (Nat × Nat)

/-- The AtomM prefix observed by this state must remain stable. Relation hooks run
outside Bounded.eval's speculative regions; any rollback there preserves this
prefix. Expansion certificates share the same atom context for their lifetime. -/
structure State where
  atoms : Std.HashMap (Expr × Bool) Nat := {}
  factors : Std.HashMap (Expr × Bool × Nat) Signature := {}
  products : Std.HashMap Expr Signature := {}
  sums : Std.HashMap Expr (PersistentHashMap Signature Expr × PersistentHashSet Expr) := {}
  work : Nat := 0
  rewrites : Nat := 0
  basisSize : Nat := 0
  independent : Bool := false

def merge (a b : Signature) : Signature := Id.run do
  let mut result := a
  for (id, power) in b do
    if let some i := result.findIdx? (fun x => x.1 == id) then
      result := result.modify i fun x => (id, x.2 + power)
    else result := result.push (id, power)
  return result.qsort (fun a b => a.1 < b.1)

def atom (ref : IO.Ref State) (e : Expr) (inverse : Bool) : MetaM Signature := do
  let s ← ref.get
  if let some id := s.atoms[(e, inverse)]? then return #[(id, 1)]
  let id := s.atoms.size
  ref.modify fun s => {s with atoms := s.atoms.insert (e, inverse) id}
  return #[(id, 1)]

/-- Conservative syntax test for quotients the bounded evaluator can split.
A refusal is an optimization decision, never an equality claim. -/
def single (fuel : Nat) (e : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``HAdd.hAdd | some ``Add.add | some ``HSub.hSub | some ``Sub.sub => false
    | some ``HMul.hMul | some ``Mul.mul =>
      args.size >= 2 && single fuel args[args.size-2]! && single fuel args[args.size-1]!
    | some ``Neg.neg => args.size > 0 && single fuel args[args.size-1]!
    | some ``HPow.hPow | some ``Pow.pow => args.size >= 2 && single fuel args[args.size-2]!
    | some ``HDiv.hDiv | some ``Div.div => args.size >= 2 && single fuel args[args.size-2]!
    | _ => true

/-- Syntactic factorization without proof construction or atom-table mutation.
No cancellation of a factor against its inverse is used: it could be zero. -/
def factors (ref : IO.Ref State) (fuel : Nat) (e : Expr) (inverse := false) : MetaM Signature := do
  if let some value := (← ref.get).factors[(e, inverse, fuel)]? then return value
  let compute (_ : Unit) : MetaM Signature := do
    match fuel with
      | 0 => atom ref e inverse
      | fuel + 1 => do
        let args := e.getAppArgs
        match e.getAppFn.constName? with
        | some ``HMul.hMul | some ``Mul.mul =>
          if args.size >= 2 then
            return merge (← factors ref fuel args[args.size-2]! inverse)
              (← factors ref fuel args[args.size-1]! inverse)
          atom ref e inverse
        | some ``HDiv.hDiv | some ``Div.div =>
          if !inverse && args.size >= 2 && single fuel args[args.size-2]! then
            return merge (← factors ref fuel args[args.size-2]!)
              (← factors ref fuel args[args.size-1]! true)
          atom ref e inverse
        | some ``Inv.inv =>
          if !inverse && args.size > 0 then
            return ← factors ref fuel args[args.size-1]! true
          atom ref e inverse
        | some ``HPow.hPow | some ``Pow.pow =>
          if args.size >= 2 then
            if let some n := (← getNatValue? args[args.size-1]!) then
              if n > 0 then
                return (← factors ref fuel args[args.size-2]! inverse).map fun (id, k) => (id, k*n)
          atom ref e inverse
        | some ``Neg.neg =>
          if args.size > 0 then return ← factors ref fuel args[args.size-1]! inverse
          atom ref e inverse
        | some ``OfNat.ofNat | some ``Nat.rawCast | some ``Int.rawCast | some ``Rat.rawCast =>
          return #[]
        | _ => atom ref e inverse
  let value ← compute ()
  ref.modify fun s => {s with factors := s.factors.insert (e, inverse, fuel) value}
  return value


partial def signature {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {e : Q($α)} (ref : IO.Ref State)
    (v : ExProd (α := α) RatCoeff sα e) : MetaM Signature := do
  if let some value := (← ref.get).products.get? e then return value
  let result : Signature ← do
    match (dependent := true) v with
    | .const _ => pure #[]
    | .mul (x := x) (e := exponent) _ power tail =>
      let head : Signature ← do
        match (dependent := true) power with
        | .const n =>
          if n.value.den == 1 then
            pure <| (← factors ref 64 x).map fun (id, k) => (id, k * n.value.num.toNat)
          else atom ref q($x ^ $exponent) false
        | _ => atom ref q($x ^ $exponent) false
      pure (merge head (← signature ref tail))
  ref.modify fun s => {s with products := s.products.insert e result}
  return result

/-- A private factor in each atom makes the factor map injective on monomials.
This is only a sufficient scalar test for skipping collision search. -/
def independent (ref : IO.Ref State) : Mathlib.Tactic.AtomM Bool := do
  let atoms := (← getThe Mathlib.Tactic.AtomM.State).atoms
  let s ← ref.get
  if s.basisSize == atoms.size then return s.independent
  let signatures ← atoms.mapM fun atom => factors ref 64 atom
  let mut occurrences : Std.HashMap Nat Nat := {}
  for signature in signatures do
    for (id, _) in signature do
      occurrences := occurrences.insert id ((occurrences[id]?).getD 0 + 1)
  let result := signatures.all fun signature =>
    signature.any fun (id, power) => power > 0 && occurrences[id]? == some 1
  ref.modify fun s => {s with basisSize := atoms.size, independent := result}
  return result

/-- Cache indices for persistent sum tails; each distinct tail is visited once.
Trie maps and sets share branches across tails instead of copying bucket arrays. -/
partial def index {u : Lean.Level} {α : Q(Type u)} {sα : Q(CommSemiring $α)} {e : Q($α)}
    (ref : IO.Ref State) (v : ExSum (α := α) RatCoeff sα e) :
    MetaM (PersistentHashMap Signature Expr × PersistentHashSet Expr) := do
  if let some result := (← ref.get).sums.get? e then return result
  let limit := det.relations.maxWork.get (← getOptions)
  let result : PersistentHashMap Signature Expr × PersistentHashSet Expr ← do
    match (dependent := true) v with
    | .zero => pure ({}, {})
    | .add (a := a) head tail =>
      ref.modify fun s => {s with work := s.work + 1}
      if (← ref.get).work > limit then throwError "relation scalar work budget exhausted ({limit})"
      let (seen, selected) ← index ref tail
      let key ← signature ref head
      if let some prior := seen.find? key then
        if prior == a then pure (seen, selected) else
          pure (seen, selected.insert prior |>.insert a)
      else
        pure (seen.insert key a, selected)
  ref.modify fun s => {s with sums := s.sums.insert e result}
  return result

/-- Expand a monomial directly, without simplifying inside opaque atoms.
Atoms and products share a cache: every cached certificate proves its own key. -/
partial def expand {u : Lean.Level} {α : Q(Type u)} {rα : Q(CommRing $α)}
    {e : Q($α)} (cache : IO.Ref (Std.HashMap Expr (Cert rα)))
    (v : ExProd (α := α) RatCoeff (commSemiringOfCommRing rα) e) :
    CertM rα (Cert rα) := do
  if let some c := (← cache.get).get? e then return c
  let result : Cert rα ← do
    match (dependent := true) v with
    | .const (e := k) value =>
      pure <| toCert ⟨q($k + 0), .add (.const value) .zero, q(Eq.symm (add_zero $k))⟩
    | .mul (x := x) (e := exponent) _ power tail =>
      let ctx ← read
      let base ← if let some c := (← cache.get).get? x then pure c else do
        let c ← toCert <$> Bounded.eval rcℕ ctx.rc ctx.cα x
        cache.modify fun s => s.insert x c
        pure c
      let ⟨_, vp, pp⟩ ← evalPow₁ ctx.rc rcℕ base.val power
      let cp := (toCert ⟨_, vp, pp⟩).chainProof
        (q(congrArg (fun a : $α => a ^ $exponent) $base.proof))
      Compact.certMul cp (← expand cache tail)
  cache.modify fun s => s.insert e result
  return result

/-- Preserve the original sum tail once all selected monomials have been handled. -/
partial def rewrite {u : Lean.Level} {α : Q(Type u)} {rα : Q(CommRing $α)}
    {e : Q($α)} (cache : IO.Ref (Std.HashMap Expr (Cert rα)))
    (selected : PersistentHashSet Expr) (v : CertVal (α := α) rα e) :
    CertM rα (Cert rα) := do
  if selected.isEmpty then return toCert ⟨e, v, q(rfl)⟩
  match (dependent := true) v with
  | .zero => return toCert ⟨e, v, q(rfl)⟩
  | .add (a := a) head tail =>
    let hc ← if selected.contains a then expand cache head else
      pure <| toCert ⟨q($a + 0), .add head .zero, q(Eq.symm (add_zero $a))⟩
    Compact.certAdd hc (← rewrite cache (selected.erase a) tail)

def normalize {u : Lean.Level} {α : Q(Type u)} {rα : Q(CommRing $α)} (ref : IO.Ref State) (cache : IO.Ref (Std.HashMap Expr (Cert rα))) (c : Cert rα) : CertM rα (Cert rα) := do
  unless (← read).cα.dsα.isSome do return c
  if ← independent ref then return c
  let (_, selected) ← index ref c.val
  if selected.isEmpty then return c
  ref.modify fun s => {s with rewrites := s.rewrites + selected.fold (fun n _ => n + 1) 0}
  return (← rewrite cache selected c.val).chainProof c.proof

/-- Compare the two sides in one representation after partial cancellation. -/
def align {u : Lean.Level} {α : Q(Type u)} {rα : Q(CommRing $α)}
    (ref : IO.Ref State) (cache : IO.Ref (Std.HashMap Expr (Cert rα)))
    (a b : Cert rα) : CertM rα (Cert rα × Cert rα) := do
  unless (← read).cα.dsα.isSome do return (a, b)
  if ← independent ref then return (a, b)
  let (seen, initialA) ← index ref a.val
  let (other, initialB) ← index ref b.val
  let mut selectedA := initialA
  let mut selectedB := initialB
  for (key, e) in other do
    if let some prior := seen.find? key then
      if prior != e || selectedA.contains prior || selectedB.contains e then
        selectedA := selectedA.insert prior
        selectedB := selectedB.insert e
  if selectedA.isEmpty && selectedB.isEmpty then return (a, b)
  let count := selectedA.fold (fun n _ => n + 1) 0 + selectedB.fold (fun n _ => n + 1) 0
  ref.modify fun s => {s with rewrites := s.rewrites + count}
  return ((← rewrite cache selectedA a.val).chainProof a.proof,
    (← rewrite cache selectedB b.val).chainProof b.proof)

end
end Determinant.Relations
