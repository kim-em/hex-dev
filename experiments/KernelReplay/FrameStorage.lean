/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameOwners
public meta import KernelReplay.FrameOwners

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameOwners

-- Native observations of the unchanged production storage guards.
/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (decide (first.root.raw.head.leadingCoeff = 1),
  first.root.raw.head.toArray.all first.cleanCoeff, first.canReduce,
  decide (second.root.raw.head.leadingCoeff = 1),
  second.root.raw.head.toArray.all second.cleanCoeff, second.canReduce)

/-- info: (1, 0) -/
#guard_msgs in
#eval (beta.polynomial.natDegree, (beta * beta).polynomial.natDegree)

/-- The first selected generator, in the actual retained predecessor. -/
@[expose] def alpha : Element first := Element.ofPoly (DensePoly.ofCoeffs #[0, 1])

/-- info: true -/
#guard_msgs in
#eval DensePoly.beqCoeffs (beta * beta).polynomial (DensePoly.C alpha)

end Hex.RealClosure.Algebraic.KernelReplay.FrameOwners

public meta section
open Lean Meta

-- Inspect actual owner dictionaries only when the named diagnostic is enabled.
run_meta do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    for name in [``Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.first,
        ``Hex.RealClosure.Algebraic.KernelReplay.FrameOwners.second] do
      let type ← inferType (mkConst name)
      for i in [:type.getAppArgs.size] do
        let argument := type.getAppArgs[i]!
        let printed ← withOptions (fun options => pp.maxSteps.set options 80) do
          ppExpr argument
        IO.FS.withFile path .append fun handle => do
          handle.putStrLn s!"owner={name} argument={i} head={argument.getAppFn.constName?} term={printed}"
          handle.flush

end
