/-
Copyright (c) 2018 Mario Carneiro, 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen, Kim Morrison
-/
import Mathlib.Tactic.Ring

/-! Experimental scalar normalization adapted from `Ring.Common.eval`.
Only constant denominators are inverted during polynomial normalization.
Other quotients remain atoms, avoiding distribution of their numerators.
All other arithmetic and proofs are the existing ring implementation.
The determinant frontend can expand residual quotients in a final comparison. -/

open Lean Meta Qq Mathlib.Tactic Mathlib.Tactic.Ring Mathlib.Tactic.Ring.Common
namespace Determinant.Coefficients
meta section
variable (rcℕ : RingCompute btℕ sℕ)

partial def eval  {u : Lean.Level}
    {α : Q(Type u)} {bt : Q($α) → Type} {sα : Q(CommSemiring $α)} (rc : RingCompute bt sα)
    (c : Cache sα) (e : Q($α)) : AtomM (Result (ExSum bt sα) e) := Lean.withIncRecDepth do
  let els := do
    try rc.derive e
    catch _ => evalAtom rc rcℕ e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, c.rα, c.dsα with
  | ``HAdd.hAdd, _, _ | ``Add.add, _, _ => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalAdd rc rcℕ va vb
      pure ⟨c, vc, q(add_congr $pa $pb $p)⟩
    | _ => els
  | ``HMul.hMul, _, _ | ``Mul.mul, _, _ => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalMul rc rcℕ va vb
      pure ⟨c, vc, q(mul_congr $pa $pb $p)⟩
    | _ => els
  | ``HSMul.hSMul, _, _ | ``SMul.smul, _, _ => match e with
    | ~q(@HSMul.hSMul $R _ _ (@instHSMul _ _ $inst) $r $a) =>
      try
        let sR : Q(CommSemiring $R) ← synthInstanceQ q(CommSemiring $R)
        let ⟨_, vb, pb⟩ ← eval rc c a
        let ⟨_, vt, pt⟩ ← rc.cast _ _ q($sR) q(inferInstance) _
        let ⟨_, vc, pc⟩ ← evalMul rc rcℕ vt vb
        return ⟨_, vc, q(smul_congr $pb $pt $pc)⟩
      catch _ => els
    | _ => els
  | ``HPow.hPow, _, _ | ``Pow.pow, _, _ => match e with
    | ~q($a ^ $b) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, pb⟩ ← eval rcℕ .nat b
      let ⟨b', vb'⟩ := vb.toExSumNat
      have : $b =Q $b' := ⟨⟩
      let ⟨c, vc, p⟩ ← evalPow rc rcℕ va vb'
      pure ⟨c, vc, q(pow_congr $pa $pb $p)⟩
    | _ => els
  | ``Neg.neg, some rα, _ => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨b, vb, p⟩ ← evalNeg rc rα va
      pure ⟨b, vb, q(neg_congr $pa $p)⟩
    | _ => els
  | ``HSub.hSub, some rα, _ | ``Sub.sub, some rα, _ => match e with
    | ~q($a - $b) => do
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨_, vb, pb⟩ ← eval rc c b
      let ⟨c, vc, p⟩ ← evalSub rc rcℕ rα va vb
      pure ⟨c, vc, q(sub_congr $pa $pb $p)⟩
    | _ => els
  | ``Inv.inv, _, some dsα => match e with
    | ~q($a⁻¹) =>
      let some ⟨_, va, pa⟩ ← (try some <$> rc.derive a catch _ => pure none) | els
      let constant := match va with
        | .zero | .add (.const _) .zero => true
        | _ => false
      unless constant do return ← els
      let ⟨b, vb, p⟩ ← va.evalInv rc rcℕ dsα c.czα
      pure ⟨b, vb, q(inv_congr $pa $p)⟩
    | _ => els
  | ``HDiv.hDiv, _, some dsα | ``Div.div, _, some dsα => match e with
    | ~q($a / $b) => do
      let some ⟨_, vb, pb⟩ ← (try some <$> rc.derive b catch _ => pure none) | els
      let constant := match vb with
        | .zero | .add (.const _) .zero => true
        | _ => false
      unless constant do return ← els
      let ⟨_, va, pa⟩ ← eval rc c a
      let ⟨c, vc, p⟩ ← evalDiv rc rcℕ dsα c.czα va vb
      pure ⟨c, vc, q(div_congr $pa $pb $p)⟩
    | _ => els
  | _, _, _ => els


end
end Determinant.Coefficients
