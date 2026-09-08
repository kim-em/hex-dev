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
private def swapBoth4 : Perm 4 := ⟨#v[1, 0, 3, 2], by decide, by decide⟩
private def three4 : Perm 4 := ⟨#v[1, 2, 0, 3], by decide, by decide⟩
private def five5 : Perm 5 := ⟨#v[1, 2, 3, 4, 0], by decide, by decide⟩
private def three5 : Perm 5 := ⟨#v[1, 2, 0, 3, 4], by decide, by decide⟩
private def swap5 : Perm 5 := ⟨#v[1, 0, 2, 3, 4], by decide, by decide⟩
private def reflect5 : Perm 5 := ⟨#v[0, 4, 3, 2, 1], by decide, by decide⟩
private def swap3 : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def cycle3 : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩
private def s4 : Group 4 := Group.ofGenerators #[swap4, cycle4]
private def d4 : Group 4 := Group.ofGenerators #[cycle4, reverse4]
private def a4 : Group 4 := Group.ofGenerators #[three4, swapBoth4]
private def c5 : Group 5 := Group.ofGenerators #[five5]
private def d5 : Group 5 := Group.ofGenerators #[five5, reflect5]
private def a5 : Group 5 := Group.ofGenerators #[five5, three5]
private def s3 : Group 3 := Group.ofGenerators #[swap3, cycle3]
private initialize s4Ref : IO.Ref (Option (Group 4)) ← IO.mkRef (some s4)
private initialize d4Ref : IO.Ref (Option (Group 4)) ← IO.mkRef (some d4)
private initialize a4Ref : IO.Ref (Option (Group 4)) ← IO.mkRef (some a4)
private initialize c5Ref : IO.Ref (Option (Group 5)) ← IO.mkRef (some c5)
private initialize d5Ref : IO.Ref (Option (Group 5)) ← IO.mkRef (some d5)
private initialize a5Ref : IO.Ref (Option (Group 5)) ← IO.mkRef (some a5)
private initialize s3Ref : IO.Ref (Option (Group 3)) ← IO.mkRef (some s3)
private initialize generatorsRef : IO.Ref (Array (Perm 4)) ←
  IO.mkRef #[swap4, cycle4, swap4, Perm.id 4]
private initialize c2Ref : IO.Ref (Option (Group 2)) ←
  IO.mkRef (some (Group.ofGenerators #[⟨#v[1, 0], by decide, by decide⟩]))

private def cycleImages (lengths : List Nat) : List Nat :=
  (lengths.foldl (fun (offset, result) length =>
    (offset + length, result ++ (List.range length).map fun i =>
      offset + (i + 1) % length)) (0, [])).2

private def largeCycleLengths : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private initialize largeRef : IO.Ref (Option (Group 381)) ← do
  let some p := Perm.ofNatArray? 381 (cycleImages largeCycleLengths).toArray
    | throw (IO.userError "large cyclic benchmark input rejected")
  IO.mkRef (some (Group.ofGenerators #[p]))

@[noinline] private def readGroup (ref : IO.Ref (Option (Group n))) : IO (Group n) := do
  let some G ← ref.get | throw (IO.userError "missing prepared benchmark group")
  return G

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- `degree-generators`: construction with declared fixed points and redundant inputs. -/
def degreeGenerators : Unit → IO Nat := fun _ => do
  let generators ← generatorsRef.get
  let degree4 := Group.ofGenerators generators
  let degree3 := Group.ofGenerators #[swap3, cycle3, swap3, cycle3.inv, Perm.id 3]
  let degree5 := Group.ofGenerators #[swap5, five5, swap5, swap5, Perm.id 5]
  require (degree3.order == 6 && degree4.order == 24 && degree5.order == 120)
    "degree-generators: wrong order"
  return degree3.order + degree4.order + degree5.order

/-- `chain-shape`: different orbit and stabilizer depths. -/
def chainShape : Unit → IO Nat := fun _ => do
  let cyclic ← readGroup c5Ref
  let dihedral ← readGroup d5Ref
  let symmetric ← readGroup s4Ref
  let alternating ← readGroup a4Ref
  let intransitive := Group.ofGenerators #[swapBoth4]
  require (cyclic.order == 5 && dihedral.order == 10 && symmetric.order == 24 &&
      alternating.order == 12 && intransitive.order == 2) "chain-shape: wrong group"
  return cyclic.chain.length + dihedral.chain.length + symmetric.chain.length +
    alternating.chain.length + intransitive.chain.length

/-- `membership`: positive words and an intransitive negative query. -/
def membership : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let positive := G.contains (swap4.comp cycle4)
  let fixed : Group 4 := Group.ofGenerators #[swap4]
  let earlyNegative := fixed.contains cycle4
  let lateNegative := fixed.contains swapBoth4
  require (positive && !earlyNegative && !lateNegative) "membership: wrong verdict"
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

/-- `enumeration`: exact element and coset outputs with rejected short caps. -/
def enumeration : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let H := Group.ofGenerators #[cycle4]
  let .ok xs := G.elementsWith 24 | throw (IO.userError "enumeration: exact cap")
  let .error elementLimit := G.elementsWith 23
    | throw (IO.userError "enumeration: short element cap")
  if h : H.isSubgroup G = true then
    let inclusion := (Group.isSubgroup_iff H G).mp h
    let .ok cosets := G.leftCosetsWith 6 H inclusion
      | throw (IO.userError "enumeration: exact coset cap")
    let .error cosetLimit := G.leftCosetsWith 5 H inclusion
      | throw (IO.userError "enumeration: short coset cap")
    require (xs.size == 24 && elementLimit.required == 24 && cosets.reps.size == 6 &&
      cosetLimit.required == 6) "enumeration: cap contract"
    return xs.size + cosets.reps.size
  else throw (IO.userError "enumeration: cyclic subgroup escaped S4")

/-- `element-access`: rank/unrank and supplied-index access. -/
def elementAccess : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let large ← readGroup largeRef
  let some p := G.unrank? 17
    | throw (IO.userError "element-access: index rejected")
  let samples : List (Element G) := Group.sampleWith (fun bound _ => List.finRange bound) G
  let some largeGenerator := large.generators[0]?
    | throw (IO.userError "element-access: missing large cyclic generator")
  require ((G.rank p).val == 17 && samples.map (fun q => (G.rank q).val) == List.range 24 &&
      swap4.sign == -1 && (swap4.comp cycle4).sign == swap4.sign * cycle4.sign &&
      swap4.cycleType == #[1, 1, 2] && large.order > 18446744073709551615 &&
      largeGenerator.cycleType.toList == largeCycleLengths)
    "element-access: rank, sampling, cycle, sign, or large-order contract"
  return (G.rank p).val + samples.length + largeGenerator.cycleType.size

/-- `finite-actions`: tuple, subset, partition, image, and kernel work. -/
def finiteActions : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let tuples := Action.tuples G 2
  let base : Vector (Fin 4) 2 := #v[0, 0]
  let .ok orbit := tuples.breadthFirst base 16
    | throw (IO.userError "finite-actions: tuple cap")
  let subset : Vector Bool 4 := #v[true, true, false, false]
  let .ok subsetOrbit := (Action.subsets G).breadthFirst subset 6
    | throw (IO.userError "finite-actions: subset cap")
  let p := Partition.ofValues #v[(0 : Nat), 0, 1, 1]
  let q := Partition.ofValues #v[(0 : Nat), 1, 0, 1]
  let r := Partition.ofValues #v[(0 : Nat), 1, 1, 0]
  let partitions : Array (Partition 4) := #[p, q, r]
  let .ok partitionOrbit := (Action.partitions G).breadthFirst p 3
    | throw (IO.userError "finite-actions: partition cap")
  let .ok image := (Action.partitions G).actionImage 3 partitions
    | throw (IO.userError "finite-actions: image domain")
  let .ok kernel := (Action.partitions G).actionKernel 3 partitions
    | throw (IO.userError "finite-actions: kernel domain")
  require (orbit.val.objects.size == 4 && subsetOrbit.val.objects.size == 6 &&
      partitionOrbit.val.objects.size == 3 && image.group.order == 6 && kernel.group.order == 4)
    "finite-actions: orbit, image, or kernel"
  return orbit.val.objects.size + subsetOrbit.val.objects.size +
    partitionOrbit.val.objects.size + image.group.order + kernel.group.order

/-- `subgroup-search`: all complete search APIs with positive and negative pruning. -/
def subgroupSearch : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let K ← readGroup d4Ref
  let H := G.intersection K
  let source : Vector Bool 4 := #v[true, true, false, false]
  let target : Vector Bool 4 := #v[false, false, true, true]
  let impossible : Vector Bool 4 := #v[true, false, false, false]
  let positive := G.setTransporter? source target
  let negative := G.setTransporter? source impossible
  let stabilizer := G.setStabilizer source
  let centralizer := G.centralizer K
  let normalizer := G.normalizer K
  require (H.order == 8 && positive.isSome && negative.isNone && stabilizer.order == 4 &&
      centralizer.order == 2 && normalizer.order == 8) "subgroup-search: wrong result"
  return H.order + stabilizer.order + centralizer.order + normalizer.order

/-- `blocks`: seeded invariant equivalence and primitivity. -/
def blocks : Unit → IO Nat := fun _ => do
  let G ← readGroup d4Ref
  let p := G.blocks [(⟨0, by decide⟩, ⟨2, by decide⟩)]
  let cyclic := Group.ofGenerators #[cycle4]
  let closed := cyclic.blocks [(0, 1), (1, 0), (0, 0)]
  let trivial := Group.ofGenerators (#[] : Array (Perm 4))
  let pairs := trivial.blocks [(0, 1), (2, 3)]
  let S ← readGroup s4Ref
  require (p.blockSize ⟨0, by decide⟩ == 2 && closed.blockSize 0 == 4 &&
      pairs.blockSize 0 == 2 && !G.isPrimitive && S.isPrimitive)
    "blocks: partition or primitivity"
  return p.blockSize 0 + closed.blockSize 0 + pairs.blockSize 0

/-- `normal-structure`: all normal APIs on soluble and perfect groups. -/
def normalStructure : Unit → IO Nat := fun _ => do
  let G ← readGroup s3Ref
  let A ← readGroup a5Ref
  let S ← readGroup s4Ref
  let H := Group.ofGenerators #[swap3]
  if h : H.isSubgroup G = true then
    let inclusion := (Group.isSubgroup_iff H G).mp h
    let closure := G.normalClosure H inclusion
    let core := G.core H inclusion
    let joined := H.join (Group.ofGenerators #[cycle3])
    let s4Orders := S.derivedSeries.certificate.orders S
    let a5Orders := A.derivedSeries.certificate.orders A
    require (joined.order == 6 && H.isAbelian && !G.isAbelian && !H.isNormal G inclusion &&
        closure.order == 6 && core.order == 1 && s4Orders == [24, 12, 4, 1] &&
        a5Orders == [60, 60] && !A.isSolvable) "normal-structure: wrong result"
    return joined.order + closure.order + core.order + s4Orders.length + a5Orders.length
  else throw (IO.userError "normal-structure: subgroup escaped S3")

/-- `products`: direct and imprimitive wreath products. -/
def products : Unit → IO Nat := fun _ => do
  let c2 ← readGroup c2Ref
  let c3 := Group.ofGenerators #[cycle3]
  let direct := c2.directProduct c2
  let wreath := c2.wreathProduct c2 (by decide)
  let mixed := c2.directProduct c3
  let empty := Group.ofGenerators (#[] : Array (Perm 0))
  let withEmpty := empty.directProduct c2
  let nonabelian := s3.wreathProduct c2 (by decide)
  let top4 := Group.ofGenerators #[swap4]
  let fixedBlocks := c2.wreathProduct top4 (by decide)
  require (direct.order == 4 && wreath.order == 8 && mixed.order == 6 &&
      withEmpty.order == 2 && nonabelian.order == 72 && fixedBlocks.order == 32 &&
      fixedBlocks.generators.size == 5) "products: wrong order or generator count"
  return direct.order + wreath.order + mixed.order + withEmpty.order +
    nonabelian.order + fixedBlocks.order

/-- `certificate-replay`: construction and replay are separate operations. -/
def certificateReplay : Unit → IO Nat := fun _ => do
  let G ← readGroup s4Ref
  let small := Group.ofGenerators #[swap4]
  let target := swap4.comp cycle4
  let some word := G.word? target
    | throw (IO.userError "certificate-replay: program generation failed")
  let p := Partition.ofValues #v[(0 : Nat), 0, 1, 1]
  let q := Partition.ofValues #v[(0 : Nat), 1, 0, 1]
  let r := Partition.ofValues #v[(0 : Nat), 1, 1, 0]
  let domain : Array (Partition 4) := #[p, q, r]
  let .ok kernel := (Action.partitions G).actionKernel 3 domain
    | throw (IO.userError "certificate-replay: kernel construction failed")
  require (checkChain small.generators small.chain && checkChain G.generators G.chain &&
      checkWord G.generators target word &&
      checkChain kernel.group.generators kernel.group.chain && word.nodes.size > 0)
    "certificate-replay: rejected chain, program, or kernel"
  return small.chain.length + G.chain.length + kernel.group.chain.length + word.nodes.size

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

setup_fixed_benchmark degreeGenerators where fixed 0x96 0.02
setup_fixed_benchmark chainShape where fixed 0x16 0.01
setup_fixed_benchmark membership where fixed 0x18 0.01
setup_fixed_benchmark stabilizers where fixed 0x8 0.02
setup_fixed_benchmark containment where fixed 0x2 0.01
setup_fixed_benchmark enumeration where fixed 0x1e 0.01
setup_fixed_benchmark elementAccess where fixed 0x39 0.02
setup_fixed_benchmark finiteActions where fixed 0x17 0.02
setup_fixed_benchmark subgroupSearch where fixed 0x16 0.2
setup_fixed_benchmark blocks where fixed 0x8 0.01
setup_fixed_benchmark normalStructure where fixed 0x13 0.2
setup_fixed_benchmark products where fixed 0x7c 0.1
setup_fixed_benchmark certificateReplay where fixed 0x60 0.02

end Hex.PermGroupBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
