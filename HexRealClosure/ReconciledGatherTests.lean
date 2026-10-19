/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledGather
public import HexRealClosure.ReconciledLive
public import HexRealClosure.TowerOrder
public meta import HexRealClosure.ReconciledGather
public meta import HexRealClosure.ReconciledLive

public section

namespace Hex.RealClosure.Tower.ReconciledTests

private def registry : BaseContext.Registry := fun _ => none
private abbrev rational := BaseContext.rational registry
private abbrev first := rational.infinitesimal
private abbrev second := first.infinitesimal

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

def run : IO Unit := do
  let base := Context.base rational
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "rational selected root failed")
  let parent := base.adjoin descriptor
  let alpha := parent.generator
  let y : DensePoly parent.context.Value := DensePoly.ofCoeffs #[0, 1]
  let some dependent := SignDet.Descriptor.validate parent.context.sign parent.context.signature
      { context := parent.context.signature, head := y * y - DensePoly.C alpha,
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "dependent selected root failed")
  let child := parent.context.adjoin dependent
  let owners := [child.context, parent.context, Context.base first]
  let some shared := Shared.gatherReconciled? (.pack second) owners
    | throw (IO.userError "reconciled child/parent gathering failed")
  require (shared.input.context.signature.roots.length == 2)
    "reconciled gathering duplicated the cached predecessor"
  let beta := shared.value 0 child.generator
  let a := shared.value 1 alpha
  let epsilon := shared.value 2 (BaseContext.Element.infinitesimal rational)
  require (shared.input.context.equal (beta * beta) a &&
    shared.input.context.equal (a * a) (1 + 1))
    "reconciled roots lost their coefficient dependencies"
  require (shared.input.context.sign beta == 1 &&
    shared.input.context.compare epsilon beta == .lt)
    "reconciled gathering changed the selected roots or infinitesimal order"
  let p : parent.context.Poly := DensePoly.ofCoeffs #[-alpha, 1]
  require (shared.input.context.equal ((shared.polynomial 1 p).eval a) 0)
    "reconciled polynomial lost its original coefficient model"
  let some packet := shared.registerReconciled? child.context
    | throw (IO.userError "repeated reconciled owner failed")
  require (packet.shared.input.context.signature.roots.length == 2)
    "repeated reconciled owner adjoined its roots again"
  require (packet.shared.input.context.equal
    (packet.previous.value (beta + epsilon))
    (packet.shared.value ⟨3, by simp [owners]⟩ child.generator +
      packet.shared.value ⟨2, by simp [owners]⟩
        (BaseContext.Element.infinitesimal rational)))
    "reconciled registration lost a computed previous-target value"
  require ((shared.addReconciled? (Context.base second.infinitesimal)).isNone)
    "reconciled gathering accepted insufficient target infinitesimal depth"
  require (parent.context.equal (alpha * alpha) (1 + 1))
    "reconciled gathering invalidated the original owner"
  require (match shared.input.context.read (parent.context.write alpha) with
    | .error _ => true | .ok _ => false)
    "reconciled shared target accepted a stale serialized value"
  let root : Root parent.context := .selected dependent child rfl
  let request := Live.rootRequest root
  let some collection := request.gatherReconciled? (.pack second)
    | throw (IO.userError "reconciled live root request failed")
  require (collection.shared.input.context.signature.roots.length == 2 &&
    collection.frames.length == 2)
    "reconciled live request duplicated ancestry or changed frame order"
  let some parentFrame := collection.frames[0]?
    | throw (IO.userError "reconciled predecessor frame missing")
  let some fresh := parentFrame.descriptors[0]?
    | throw (IO.userError "reconciled selected descriptor missing")
  let some childFrame := collection.frames[1]?
    | throw (IO.userError "reconciled child frame missing")
  let some retained := childFrame.values[0]?
    | throw (IO.userError "reconciled selected generator missing")
  require (fresh.raw.context == collection.shared.input.context.signature &&
    collection.shared.input.context.sign (fresh.raw.head.eval retained) == 0 &&
    collection.shared.input.context.sign retained == 1)
    "reconciled live root disagrees with its refreshed predecessor descriptor"

end Hex.RealClosure.Tower.ReconciledTests

#eval Hex.RealClosure.Tower.ReconciledTests.run
