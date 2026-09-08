/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPermGroup
import LeanBench

/-!
The thirteen required permutation-group benchmark families. Inputs are rebuilt
inside each target when construction is the operation under test; prepared
groups are shared only by query families. `verify` executes every registration
and therefore checks each result as well as the wiring.
-/

namespace Hex.PermGroupBench

open Hex Hex.PermGroup

private def swap4 : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
private def cycle4 : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
private def reverse4 : Perm 4 := ⟨#v[0, 3, 2, 1], by decide, by decide⟩
private def s4 : Group 4 := Group.ofGenerators #[swap4, cycle4]
private def d4 : Group 4 := Group.ofGenerators #[cycle4, reverse4]
private initialize s4Ref : IO.Ref (Option (Group 4)) ← IO.mkRef (some s4)
private initialize d4Ref : IO.Ref (Option (Group 4)) ← IO.mkRef (some d4)
private initialize generatorsRef : IO.Ref (Array (Perm 4)) ←
  IO.mkRef #[swap4, cycle4, swap4, Perm.id 4]
private initialize c2Ref : IO.Ref (Option (Group 2)) ←
  IO.mkRef (some (Group.ofGenerators #[⟨#v[1, 0], by decide, by decide⟩]))

@[noinline] private def readGroup (ref : IO.Ref (Option (Group n))) : IO (Group n) := do
  let some G ← ref.get | throw (IO.userError "missing prepared benchmark group")
  return G

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `degree-generators`: construction with declared fixed points and redundant inputs. -/
def degreeGenerators : Unit → IO Nat := fun _ => do
  let generators ← generatorsRef.get
  let G := Group.ofGenerators generators
  require (G.order == 24) "degree-generators: wrong order"
  return G.order

/-- `chain-shape`: different orbit and stabilizer depths. -/
def chainShape : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let H ← readGroup d4Ref
  require (G.order == 24 && H.order == 8) "chain-shape: wrong group"
  return G.chain.length + H.chain.length

/-- `membership`: positive words and an intransitive negative query. -/
def membership : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let positive := G.contains (swap4.comp cycle4)
  let fixed : Group 4 := Group.ofGenerators #[swap4]
  let negative := fixed.contains cycle4
  require (positive && !negative) "membership: wrong verdict"
  return G.order

/-- `stabilizers`: point and pointwise stabilizers. -/
def stabilizers : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let point := G.stabilizer ⟨0, by decide⟩
  let pair := G.pointwise [⟨0, by decide⟩, ⟨1, by decide⟩]
  require (point.order == 6 && pair.order == 2) "stabilizers: wrong order"
  return point.order + pair.order

/-- `containment`: equality, strict inclusion, and a failed inclusion. -/
def containment : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let h := Group.ofGenerators #[swap4]
  require (h.isSubgroup G && G.isSubgroup G && !G.isSubgroup h)
    "containment: wrong verdict"
  return h.order

/-- `enumeration`: exact output and rejected short cap. -/
def enumeration : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  match G.elementsWith 24, G.elementsWith 23 with
  | .ok xs, .error limit =>
      require (xs.size == 24 && limit.required == 24) "enumeration: cap contract"
      return xs.size
  | _, _ => throw (IO.userError "enumeration: wrong status")

/-- `element-access`: rank/unrank and supplied-index access. -/
def elementAccess : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let some p := G.unrank? 17
    | throw (IO.userError "element-access: index rejected")
  require ((G.rank p).val == 17) "element-access: inverse law"
  return (G.rank p).val

/-- `finite-actions`: natural, tuple, subset, and partition-domain work. -/
def finiteActions : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let natural := G.orbit ⟨0, by decide⟩
  let tuples := Action.tuples G 2
  let base : Vector (Fin 4) 2 := #v[0, 0]
  let .ok orbit := tuples.breadthFirst base 16
    | throw (IO.userError "finite-actions: tuple cap")
  require (natural.size == 4 && orbit.val.objects.size == 4) "finite-actions: orbit"
  return natural.size + orbit.val.objects.size

/-- `subgroup-search`: complete intersection with replay. -/
def subgroupSearch : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let K ← readGroup d4Ref
  let H := G.intersection K
  require (H.order == 8) "subgroup-search: intersection"
  return H.order

/-- `blocks`: seeded invariant equivalence and primitivity. -/
def blocks : Unit → IO Nat := fun _ => do
  let G ← readGroup d4Ref
  let p := G.blocks [(⟨0, by decide⟩, ⟨2, by decide⟩)]
  require (p.blockSize ⟨0, by decide⟩ == 2 && !G.isPrimitive)
    "blocks: partition or primitivity"
  return p.blockSize ⟨0, by decide⟩

/-- `normal-structure`: joins, normal closure, core, and derived subgroup. -/
def normalStructure : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let closure := G.normalClosure G (fun _ hp => hp)
  require (closure.order == 24 && G.derived.order == 12) "normal-structure: wrong order"
  return closure.order + G.derived.order

/-- `products`: direct and imprimitive wreath products. -/
def products : Unit → IO Nat := fun _ => do
  let c2 ← readGroup c2Ref
  let direct := c2.directProduct c2
  let wreath := c2.wreathProduct c2 (by decide)
  require (direct.order == 4 && wreath.order == 8) "products: wrong order"
  return direct.order + wreath.order

/-- `certificate-replay`: construction and replay are separate operations. -/
def certificateReplay : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  require (checkChain G.generators G.chain) "certificate-replay: rejected chain"
  return G.chain.length

/- The group degree is part of the Lean type, while the other families vary
several independent dimensions. These are mode-3 canonical cases: each checks
its complete mathematical result and carries an operation-specific ceiling.
The scientific report records the controlled dimensions and separate profiles.
The ceilings exceed the clean calibration medians by at least 100x while still
rejecting an order-of-magnitude algorithmic regression. -/
private def fixed (expected : UInt64) (cap : Float) : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := cap
  expectedHash := some expected

setup_fixed_benchmark degreeGenerators where fixed 0x18 0.01
setup_fixed_benchmark chainShape where fixed 0x8 0.01
setup_fixed_benchmark membership where fixed 0x18 0.01
setup_fixed_benchmark stabilizers where fixed 0x8 0.02
setup_fixed_benchmark containment where fixed 0x2 0.01
setup_fixed_benchmark enumeration where fixed 0x18 0.01
setup_fixed_benchmark elementAccess where fixed 0x11 0.01
setup_fixed_benchmark finiteActions where fixed 0x8 0.01
setup_fixed_benchmark subgroupSearch where fixed 0x8 0.1
setup_fixed_benchmark blocks where fixed 0x2 0.01
setup_fixed_benchmark normalStructure where fixed 0x24 0.05
setup_fixed_benchmark products where fixed 0xc 0.02
setup_fixed_benchmark certificateReplay where fixed 0x4 0.01

end Hex.PermGroupBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
