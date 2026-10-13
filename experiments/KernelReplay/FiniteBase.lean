/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FiniteBase
public meta import HexRealClosureMathlib.FiniteBase
import all HexRealClosure.BaseContext
import all HexRealClosureMathlib.BaseFinite
import all HexPoly.Dense
import all HexRationalFn.Basic
import all Init.Data.Array.Basic
import all Init.Data.Rat.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe
open BaseContext

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

@[expose] def registry : Registry := fun _ => none
abbrev rational := BaseContext.rational registry
abbrev first := rational.infinitesimal
abbrev base := first.infinitesimal
@[expose] def epsilon : BaseContext.Element base := (BaseContext.Element.infinitesimal rational).embed
@[expose] def delta : BaseContext.Element base := BaseContext.Element.infinitesimal first
@[expose] def left : DensePoly (BaseContext.Element base) := DensePoly.ofCoeffs #[delta, epsilon + delta]
@[expose] def right : DensePoly (BaseContext.Element base) := DensePoly.ofCoeffs #[-delta, -(epsilon + delta)]
@[expose] def inputs : List (BaseContext.Element base) :=
  Transport.Inventory.coefficients left ++ Transport.Inventory.coefficients right ++ [epsilon]

private noncomputable def following : base.chain.Realization registry :=
  .infinitesimal first.chain (.infinitesimal rational.chain
    (.real .base (.rational registry) .base))

local instance : Field (RationalFn (RationalFn Rat)) := HexPolyMathlib.fieldOfGrind

private theorem realized : ∃ interpretation : CoefficientMap (RationalFn (RationalFn Rat)) ℝ,
    Transport.Inventory.Agreement (base.partialRead interpretation)
      (base.partialDomain interpretation) BaseContext.Element.sign
      (fun x : ℝ => (SignType.sign x : Int)) inputs := by
  obtain ⟨interpretation, data, _⟩ := base.partial_exists following inputs
  exact ⟨interpretation, data⟩

noncomputable def interpretation : CoefficientMap (RationalFn (RationalFn Rat)) ℝ :=
  Classical.choose realized

theorem agreement : Transport.Inventory.Agreement (base.partialRead interpretation)
    (base.partialDomain interpretation) BaseContext.Element.sign
    (fun x : ℝ => (SignType.sign x : Int)) inputs :=
  Classical.choose_spec realized

theorem closed : Transport.Closed (base.partialRead interpretation)
    (base.partialDomain interpretation) := base.partialClosed interpretation

public meta section
open Lean Meta Elab Command
syntax (name := finiteBaseProbe) "#finite_base_probe" : command
@[command_elab finiteBaseProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let base ← FiniteData.Base.ofClosed (mkConst ``closed)
  let domains := FiniteData.agreementSupplier (mkConst ``agreement)
  let supplier := base.supply domains domains
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let type ← mkAppM ``Transport.PowerData #[base.read, mkConst ``left, n]
    let proof ← FiniteData.build type supplier
    let statement ← mkForallFVars #[n] type
    let proof ← mkLambdaFVars #[n] proof
    kernelCheck `__finiteBasePower statement proof
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.power,
      levelParams := [], type := statement, value := proof })
  for (target, name, operands) in #[
      (``Transport.Sum, `sum, #[mkConst ``left, mkConst ``right]),
      (``Transport.Product, `product, #[mkConst ``left, mkConst ``right]),
      (``Transport.Difference, `difference, #[mkConst ``left, mkConst ``right]),
      (``Transport.Scaling, `scaling, #[mkConst ``delta, mkConst ``left]),
      (``Transport.Differentiation, `derivative, #[mkConst ``left]),
      (``Transport.Evaluation, `evaluation, #[mkConst ``left, mkConst ``epsilon])] do
    let type ← mkAppM target (#[base.read] ++ operands)
    let proof ← FiniteData.buildClosed type supplier
    addDecl (.thmDecl {
      name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe ++ name,
      levelParams := [], type, value := proof })
  let leading ← mkAppM ``Transport.Leading #[base.read, mkConst ``left]
  let some direct ← domains leading | throwError "leading supplier did not recognize its reader"
  kernelCheck `__finiteBaseLeadingDirect leading direct
  let proof ← FiniteData.buildClosed leading supplier
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.leading,
    levelParams := [], type := leading, value := proof })
  let absent ← mkAppM ``HSub.hSub #[mkConst ``epsilon, mkConst ``delta]
  let missing ← mkAppM ``Transport.Evaluation #[base.read, mkConst ``left, absent]
  try
    let _ ← FiniteData.buildClosed missing supplier
    throwError "base supplier accepted an unretained coefficient guard"
  catch error =>
    unless (← error.toMessageData.toString).startsWith "missing finite replay evidence" do
      throw error
  let size ← mkAppM ``DensePoly.size #[← mkAppM ``HAdd.hAdd #[mkConst ``left, mkConst ``right]]
  kernelCheck `__finiteBaseCancellation (← mkEq size (toExpr (0 : Nat))) (← mkEqRefl size)
  logInfo "guarded base supplier constructed six finite operations and leading guards; unretained coefficient rejected"

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
/-- info: guarded base supplier constructed six finite operations and leading guards; unretained coefficient rejected -/
#guard_msgs in
#finite_base_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.product

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.leading

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteBaseProbe.power
