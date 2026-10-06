/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledBase
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.ReconciledBase

public section

namespace Hex.RealClosure.Tower.ReconciledBaseTests


private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev second := first.infinitesimal

private def alpha : BaseContext.ConstantKey := ⟨"alpha", 1⟩
private def beta : BaseContext.ConstantKey := ⟨"beta", 1⟩

-- These literal metadata regressions use the exact predicate of the native
-- selector without asserting unavailable provider progress or transcendence.
#guard SharedBase.acceptsKeys [alpha, beta] [[beta, alpha]]
#guard !decide (List.Sublist [beta, alpha] [alpha, beta])
#guard SharedBase.acceptsKeys [alpha, beta] [[alpha], [beta]]
#guard !SharedBase.acceptsKeys [alpha] [[alpha], [beta]]
#guard !SharedBase.acceptsKeys [alpha, beta] [[alpha, alpha]]
#guard !SharedBase.acceptsKeys [alpha, alpha] [[alpha]]

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

def run : IO Unit := do
  let catalog := BaseContext.Catalog.empty registry
  let original := Context.base first
  let epsilon : original.Value := BaseContext.Element.infinitesimal rational
  let x : original.Poly := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate original.sign original.signature
      { context := original.signature, head := x * x - DensePoly.C ((1 + 1) + epsilon),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "infinitesimal selected root failed")
  let child := original.adjoin descriptor
  let other := Context.base second
  let tiny : other.Value := BaseContext.Element.infinitesimal first
  let owners := [child.context, original, other]
  let some ⟨base, shared⟩ := Shared.gatherReconciledFrom? catalog owners
    | throw (IO.userError "automatic reconciled owner gathering failed")
  require (base.signature.constants.isEmpty && base.depth == 2)
    "automatic selection did not use the installed rational prefix and maximum depth"
  require (shared.input.context.signature.roots.length == 1)
    "automatic gathering duplicated algebraic ancestry"
  let root := shared.value 0 child.generator
  let retained := shared.value 1 epsilon
  let parameter := shared.value 2 tiny
  require (shared.input.context.sign root == 1 &&
    shared.input.context.sign (root * root - ((1 + 1) + retained)) == 0 &&
    shared.input.context.compare parameter retained == .lt)
    "automatic gathering changed the selected root or infinitesimal predecessors"
  let selected : Root original := .selected descriptor child rfl
  let request := Live.rootRequest selected ++ [⟨other, { values := [tiny] }⟩]
  let some ⟨liveBase, collection⟩ := request.gatherReconciledFrom? catalog
    | throw (IO.userError "automatic reconciled live root gathering failed")
  require (liveBase.depth == 2 && collection.frames.length == 3 &&
    collection.shared.input.context.signature.roots.length == 1)
    "automatic live gathering changed request order or dependency closure"
  let some predecessor := collection.frames[0]?
    | throw (IO.userError "automatic root predecessor missing")
  let some fresh := predecessor.descriptors[0]?
    | throw (IO.userError "automatic root descriptor missing")
  let some retainedChild := collection.frames[1]?
    | throw (IO.userError "automatic root child missing")
  let some value := retainedChild.values[0]?
    | throw (IO.userError "automatic root generator missing")
  require (fresh.raw.context == collection.shared.input.context.signature &&
    collection.shared.input.context.sign (fresh.raw.head.eval value) == 0 &&
    collection.shared.input.context.sign value == 1)
    "automatic live gathering disagrees with its refreshed selected descriptor"
  require (original.sign (epsilon - epsilon) == 0)
    "automatic selection invalidated the original context"

end Hex.RealClosure.Tower.ReconciledBaseTests

#eval Hex.RealClosure.Tower.ReconciledBaseTests.run
