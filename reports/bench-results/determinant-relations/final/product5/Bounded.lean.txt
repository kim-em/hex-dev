/-
Copyright (c) 2018 Mario Carneiro, 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen, Kim Morrison
-/
import Mathlib.Tactic.Ring

/-! Experimental scalar normalization with bounded speculation.
Numeric denominators are coefficients. For other quotients, try normalizing
the numerator while refusing any intermediate sum with more than one monomial.
On refusal, restore the atom and Meta state and retain the whole quotient as an atom.
Denominators and inverse arguments use the same bounded normalization, retaining
a compound argument as an atom if it would expand into multiple monomials. No matrix structure is inspected. -/

open Lean Meta Qq Mathlib.Tactic Mathlib.Tactic.Ring Mathlib.Tactic.Ring.Common
namespace Determinant.Bounded
meta section
variable (rcℕ : RingCompute btℕ sℕ)

def atMostOne {u : Level} {α : Q(Type u)} {bt : Q($α) → Type}
    {sα : Q(CommSemiring $α)} {e : Q($α)} (value : ExSum bt sα e) : Bool :=
  match value with
  | .zero | .add _ .zero => true
  | _ => false

partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) (single : Bool := false) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let result : Result (ExSum bt sα) e ← do
    let els := do
      try rc.derive e
      catch _ => evalAtom rc rcℕ e
    let .const n _ := (← withReducible <| whnf e).getAppFn | els
    match n, c.rα, c.dsα with
    | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
      | ~q($a + $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a single
        let ⟨_, vb, pb⟩ ← eval rc c b single
        let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
        pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
      | _ => els
    | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
      | ~q($a * $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a single
        let ⟨_, vb, pb⟩ ← eval rc c b single
        let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
        pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
      | _ => els
    | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
      | ~q(@HSMul.hSMul $R _ _ (@instHSMul _ _ $inst) $r $a) =>
        try
          let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
          let ⟨_, vb, pb⟩ ← eval rc c a single
          let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _
          let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vt vb
          pure ⟨_, vc, q(smul_congr $pb $pt $pc)⟩
        catch ex =>
          if single then throw ex else els
      | _ => els
    | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
      | ~q($a ^ $b) =>
        let ⟨_, va, pa⟩ ← eval rc c a single
        let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
        let ⟨b', vb'⟩ := vb.toExSumNat
        have : $b =Q $b' := ⟨⟩
        let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
        pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
      | _ => els
    | ``Neg.neg, some rα, _ => match e with
      | ~q(-$a) =>
        let ⟨_, va, pa⟩ ← eval rc c a single
        let ⟨b, vb, p⟩ ← evalNeg rc rα va
        pure ⟨b, vb, q(neg_congr $pa $p)⟩
      | _ => els
    | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
      | ~q($a - $b) => do
        let ⟨_, va, pa⟩ ← eval rc c a single
        let ⟨_, vb, pb⟩ ← eval rc c b single
        let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
        pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
      | _ => els
    | ``Inv.inv, _, some dsα => match e with
      | ~q($a⁻¹) =>
        let saved ← getThe Mathlib.Tactic.AtomM.State
        let metaSaved ← Meta.saveState
        let argument ← try some <$> eval rc c a true catch _ => pure none
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
        let denominator ← try some <$> rc.derive b catch _ => pure none
        match denominator with
        | some ⟨_, vb, pb⟩ =>
          let ⟨_, va, pa⟩ ← eval rc c a single
          let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
          pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
        | none =>
          let saved ← getThe Mathlib.Tactic.AtomM.State
          let metaSaved ← Meta.saveState
          let numerator ← try some <$> eval rc c a true catch _ => pure none
          match numerator with
          | none =>
            metaSaved.restore
            set saved
            els
          | some ⟨_, va, pa⟩ =>
            let saved ← getThe Mathlib.Tactic.AtomM.State
            let metaSaved ← Meta.saveState
            let denominator ← try some <$> eval rc c b true catch _ => pure none
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
  unless !single || atMostOne result.val do
    throwError "speculative numerator is not a monomial"
  return result


end
end Determinant.Bounded
