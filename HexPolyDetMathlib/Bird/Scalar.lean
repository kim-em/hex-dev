/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-
Copyright (c) 2018 Mario Carneiro, 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen, Kim Morrison
-/
module

public import Mathlib.Tactic.Ring

/-! Scalar normalization with bounded speculation, adapted from Mathlib's
`Mathlib.Tactic.Ring` traversal at revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Numeric denominators are coefficients. For other quotients, try normalizing
the numerator while refusing any intermediate sum with more than one monomial.
On refusal, restore the atom and Meta state and retain the whole quotient as an atom.
Denominators and inverse arguments use the same bounded normalization, retaining
a compound argument as an atom if it would expand into multiple monomials. No matrix structure is inspected. -/

open Lean Meta Qq Mathlib.Tactic Mathlib.Tactic.Ring Mathlib.Tactic.Ring.Common
public section

namespace HexPolyDetMathlib.Bird.Scalar
meta section

/-- The selected quotient policy keeps compound quotients compact while
allowing a monomial numerator during bounded speculation. -/
inductive Mode where
  | general
  | monomial
  deriving DecidableEq

/-- Recover a scalar capability refusal while preserving runtime resource
exceptions. -/
private def recover? (action : AtomM α) : AtomM (Option α) := do
  let atomState ← get
  let metaState ← Meta.saveState
  try return some (← action)
  catch ex =>
    if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
    if let .internal _ _ := ex then throw ex
    metaState.restore
    set atomState
    return none

variable (rcℕ : RingCompute btℕ sℕ)

def atMostOne {u : Level} {α : Q(Type u)} {bt : Q($α) → Type}
    {sα : Q(CommSemiring $α)} {e : Q($α)} (value : ExSum bt sα e) : Bool :=
  match value with
  | .zero | .add _ .zero => true
  | _ => false

partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) (mode : Mode := .general) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let result : Result (ExSum bt sα) e ← do
    let els := do
      match ← recover? (rc.derive e) with
      | some value => pure value
      | none => evalAtom rc rcℕ e
    let .const n _ := (← withReducible <| whnf e).getAppFn | els
    match n, c.rα, c.dsα with
    | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
      | ~q($a + $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a mode
        let ⟨_, vb, pb⟩ ← eval rc c b mode
        let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
        pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
      | _ => els
    | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
      | ~q($a * $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a mode
        let ⟨_, vb, pb⟩ ← eval rc c b mode
        let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
        pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
      | _ => els
    | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
      | ~q(@HSMul.hSMul $R _ _ (@instHSMul _ _ $inst) $r $a) =>
        try
          let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
          let ⟨_, vb, pb⟩ ← eval rc c a mode
          let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _
          let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vt vb
          pure ⟨_, vc, q(smul_congr $pb $pt $pc)⟩
        catch ex =>
          if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
          if let .internal _ _ := ex then throw ex
          if mode == .monomial then throw ex else els
      | _ => els
    | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
      | ~q($a ^ $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a mode
        let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
        let ⟨b', vb'⟩ := vb.toExSumNat
        have : $b =Q $b' := ⟨⟩
        let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
        pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
      | _ => els
    | ``Neg.neg, some rα, _ => match e with
      | ~q(-$a) =>
        let ⟨_, va, pa⟩ ← eval rc c a mode
        let ⟨b, vb, p⟩ ← evalNeg rc rα va
        pure ⟨b, vb, q(neg_congr $pa $p)⟩
      | _ => els
    | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
      | ~q($a - $b) => do
        let ⟨_, va, pa⟩ ← eval rc c a mode
        let ⟨_, vb, pb⟩ ← eval rc c b mode
        let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
        pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
      | _ => els
    | ``Inv.inv, _, some dsα => match e with
      | ~q($a⁻¹) =>
        let saved ← getThe Mathlib.Tactic.AtomM.State
        let metaSaved ← Meta.saveState
        let argument ← recover? (eval rc c a .monomial)
        let ⟨_, va, pa⟩ ← match argument with
          | some value => pure value
          | none => do
            metaSaved.restore
            set saved
            evalAtom rc rcℕ a
        let ⟨b, vb, p⟩ ← va.evalInv rc rcℕ dsα c.czα
        pure ⟨b, vb, q(inv_congr $pa $p)⟩
      | _ => els
    | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
      | ~q($a / $b) => do
        let denominator ← recover? (rc.derive b)
        match denominator with
        | some ⟨_, vb, pb⟩ =>
          let ⟨_, va, pa⟩ ← eval rc c a mode
          let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
          pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
        | none =>
          let saved ← getThe Mathlib.Tactic.AtomM.State
          let metaSaved ← Meta.saveState
          let numerator ← recover? (eval rc c a .monomial)
          match numerator with
          | none =>
            metaSaved.restore
            set saved
            els
          | some ⟨_, va, pa⟩ =>
            let saved ← getThe Mathlib.Tactic.AtomM.State
            let metaSaved ← Meta.saveState
            let denominator ← recover? (eval rc c b .monomial)
            let ⟨_, vb, pb⟩ ← match denominator with
              | some value => pure value
              | none => do
                metaSaved.restore
                set saved
                evalAtom rc rcℕ b
            let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
            pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
      | _ => els
    | _, _, _ => els
  unless mode == .general || atMostOne result.val do
    throwError "speculative numerator is not a monomial"
  return result


end
end HexPolyDetMathlib.Bird.Scalar
