/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Normalized
import Mathlib.Data.ZMod.Basic

namespace Determinant.RelationsAudit

theorem generic {R : Type*} [CommRing R] (a b c d : R) :
    Matrix.det !![a,b;c,d] = a*d-b*c := by relations_bird

theorem rational (a b : Rat) :
    Matrix.det !![a/2,b/3;a/5,b/7] = a*b*(1/14-1/15) := by relations_bird

theorem composite (a b c d : ZMod 6) :
    Matrix.det !![a,b;c,d] = a*d-b*c := by relations_bird

theorem quotientRows {R : Type*} [Field R] (a b c d e f u v w x y z : R) :
    Matrix.det !![a/u,b/v,c/w;d/x,e/y,f/z;a/u+d/x,b/v+e/y,c/w+f/z] = 0 := by
  relations_first

theorem scaled {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a*c/u,a*d/u;b*c/v,b*d/v] = 0 := by relations_first

theorem products {R : Type*} [Field R] (a b c d u v w z : R) :
    Matrix.det !![a*c/(u*w),a*d/(u*z);b*c/(v*w),b*d/(v*z)] = 0 := by
  relations_first

theorem scalarIdentity {R : Type*} [Field R] (a b c d : R) :
    Matrix.det !![a/b*(c/d)-a/d*(c/b)] = 0 := by relations_first

theorem targetIdentity {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a/u,b/u;c/v,d/v] = (a*d-b*c)/(u*v) := by relations_bird

theorem zeroDenominator {R : Type*} [Field R] (a b c d : R) :
    Matrix.det !![a*c/0,a*d/0;b*c/0,b*d/0] = 0 := by relations_bird

example {R : Type*} [Field R] (a b : R)
    (h : Matrix.det !![a/b] = 1) : Matrix.det !![a/b] = 1 := by
  fail_if_success relations_bird
  exact h

-- Multiplication by an inverse is not cancellation without a nonzero hypothesis.
example {R : Type*} [Field R] (a : R)
    (h : Matrix.det !![a/a] = 1) : Matrix.det !![a/a] = 1 := by
  fail_if_success relations_bird
  exact h

set_option det.relations.maxWork 1 in
example {R : Type*} [Field R] (a b c d u v : R)
    (h : Matrix.det !![a*c/u,a*d/u;b*c/v,b*d/v] = 0) :
    Matrix.det !![a*c/u,a*d/u;b*c/v,b*d/v] = 0 := by
  fail_if_success relations_first
  exact h

theorem partialMerge {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![a*c/u, -(a*d/u); b*c/v, b*d/v] = 2*(a*c/u)*(b*d/v) := by
  relations_first

theorem powers {R : Type*} [Field R] (a b u v : R) :
    Matrix.det !![a^2/u, a*b/u; a*b/v, b^2/v] = 0 := by relations_first

theorem negative {R : Type*} [Field R] (a b c d u v : R) :
    Matrix.det !![-a*c/u, a*d/u; b*c/v, -b*d/v] = 0 := by relations_first

theorem compact {R : Type*} [Field R] (a b c d u v w x : R) :
    Matrix.det !![a/u, b/v; c/w, d/x] = a/u*(d/x)-b/v*(c/w) := by relations_first

set_option det.relations.trace true in
theorem targetGrowth {R : Type*} [Field R] (a b c d u v w x : R) :
    Matrix.det !![a/u, b/v; c/w, d/x] = a*d/(u*x)-b*c/(v*w) := by relations_first

theorem zeroEntry {R : Type*} [Field R] (a b c d e : R) :
    Matrix.det !![a/b*(c/d)-a/d*(c/b), 0; e, e] = 0 := by relations_first

set_option det.relations.maxHeartbeats 0 in
example {R : Type*} [Field R] (a b c d : R)
    (h : Matrix.det !![a,b;c,d] = a*d-b*c) :
    Matrix.det !![a,b;c,d] = a*d-b*c := by
  fail_if_success relations_bird
  exact h

#print axioms partialMerge
#print axioms powers
#print axioms negative
#print axioms compact
#print axioms zeroEntry
#print axioms targetGrowth
#print axioms generic
#print axioms rational
#print axioms composite
#print axioms quotientRows
#print axioms scaled
#print axioms products
#print axioms scalarIdentity
#print axioms targetIdentity
#print axioms zeroDenominator
end Determinant.RelationsAudit

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant in
run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b =>
      withLocalDeclD `u q(Rat) fun u =>
        withLocalDeclD `v q(Rat) fun v => do
          have a : Q(Rat) := a
          have b : Q(Rat) := b
          have u : Q(Rat) := u
          have v : Q(Rat) := v
          let reified ← reifyBirdDet q(BirdDet.birdDet 2 (#[$a/$u, $b/$v, $a/$u, $b/$v]))
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : Determinant.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let _ ← (Determinant.Compact.certBirdDet true true false false
            (Determinant.Relations.normalize state cache)).run' {} |>.run ctx |>.run .reducible
          logInfo m!"RELATIONS_STATS work={(← state.get).work}, independent={(← state.get).independent}, atoms={(← state.get).basisSize}"
          unless (← state.get).rewrites == 0 do
            throwError "independent quotients expanded despite ordinary cancellation"
          unless (← cache.get).isEmpty do
            throwError "independent quotients generated expansion proofs"
          logInfo "RELATIONS_CHECK independent quotients generated no expansion proofs"
          let reified ← reifyBirdDet q(BirdDet.birdDet 2
            (#[$a*$a/$u, $a*$b/$u, $b*$a/$v, $b*$b/$v]))
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : Determinant.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let result ← (Determinant.Compact.certBirdDet true true false false
            (Determinant.Relations.normalize state cache)).run' {} |>.run ctx |>.run .reducible
          unless result.isZero && (← state.get).rewrites > 0 && !(← cache.get).isEmpty do
            throwError "quotient identities did not produce a cached zero certificate"
          logInfo "RELATIONS_CHECK colliding quotient products expanded and cancelled"
          let reified ← reifyBirdDet q(BirdDet.birdDet 2
            (#[$a/$u*($b/$v)-$a/$v*($b/$u), 0, $a, $b]))
          let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
          let ctx := { reified.ctx with cα, rc := ringCompute cα }
          let state ← IO.mkRef ({} : Determinant.Relations.State)
          let cache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
          let audit : CertM reified.rα Unit := do
            let _ ← Determinant.Compact.coeffEntry true false false 0 0
              (Determinant.Relations.normalize state cache)
            let some entry := (← get).entryCache[(0, 0)]?
              | throwError "normalized entry was not cached"
            unless entry.isZero do throwError "cached entry missed relation-proved zero"
            logInfo "RELATIONS_CHECK cached entry exposes zero before recurrence"
          audit.run' {} |>.run ctx |>.run .reducible

open Lean Meta Qq Mathlib.Tactic.Ring in
run_meta do
  withLocalDeclD `a q(Rat) fun a =>
    withLocalDeclD `b q(Rat) fun b => do
      have a : Q(Rat) := a
      have b : Q(Rat) := b
      let c ← Common.mkCache q(inferInstance : CommSemiring Rat)
      let audit : Mathlib.Tactic.AtomM Unit := do
        let value ← Determinant.Coefficients.eval rcℕ (ringCompute c) c q($a + $b)
        let state ← IO.mkRef ({} : Determinant.Relations.State)
        let _ ← Determinant.Relations.index state value.val
        let first ← state.get
        let _ ← Determinant.Relations.index state value.val
        let second ← state.get
        unless first.work > 0 && first.work == second.work && first.sums.size > 0 do
          throwError "sum index bypassed cache insertion or reuse"
        let _ ← Determinant.Relations.factors state 64 q($a * $b)
        unless ((← state.get).factors.get? (q($a * $b), false, 64)).isSome do
          throwError "factor signature bypassed cache insertion"
        logInfo "RELATIONS_CHECK sum and factor caches populated and reused"
        let limited ← IO.mkRef ({} : Determinant.Relations.State)
        let rejected ← try
          withOptions (fun options => options.set `det.relations.maxWork (1 : Nat)) do
            let _ ← Determinant.Relations.index limited value.val
            pure ()
          pure false
        catch e => pure ((← e.toMessageData.toString) == "relation scalar work budget exhausted (1)")
        unless rejected do throwError "missing exact scalar-work decline"
        logInfo "RELATIONS_CHECK exact scalar-work decline"

      audit.run .reducible

open Lean Meta in
run_meta do
  let options ← getOptions
  let rejected ← try
    withOptions (fun _ => options.set `det.relations.maxHeartbeats (0 : Nat)) <|
      Determinant.Relations.withBudget (pure ())
    pure false
  catch e => pure ((← e.toMessageData.toString) == "relation heartbeat budget must be positive")
  unless rejected do throwError "missing exact heartbeat-budget decline"
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := now, maxHeartbeats := 100000}) do
    Determinant.Relations.withBudget do
      unless (← readThe Core.Context).maxHeartbeats <= 100000 do
        throwError "relation budget raised the outer limit"
  logInfo "RELATIONS_CHECK heartbeat decline and outer ceiling preserved"
