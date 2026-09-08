/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPermGroup

/-! Reproducible, presentation-preserving Hex results for the GAP oracle. -/

open Lean
open Hex Hex.PermGroup

private def images (p : Perm n) : List Nat :=
  p.vec.toArray.toList.map Fin.val

private def generatorImages (G : Group n) : List (List Nat) :=
  G.generators.toList.map images

private def pointLists (xs : Array (Array (Fin n))) : List (List Nat) :=
  xs.toList.map fun orbit => orbit.toList.map Fin.val

private def partitionBlocks (p : Partition n) : List (List Nat) :=
  (List.finRange n).filterMap fun root =>
    if p.labels[root.val] = root then
      some ((List.finRange n).filter (fun x => p.labels[x.val] = root) |>.map Fin.val)
    else none

private def fixedPoints (G : Group n) : List Nat :=
  (List.finRange n).filter (fun x => G.generators.all fun p => p.get x = x) |>.map Fin.val

private def record (id operation status : String) (degree : Nat)
    (generators : List (List Nat)) (fields : List (String × Json)) : Json :=
  Json.mkObj <| [("schema_version", toJson (1 : Nat)), ("id", toJson id),
    ("operation", toJson operation), ("degree", toJson degree),
    ("generators", toJson generators), ("status", toJson status)] ++ fields

private def swap3 : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def cycle3 : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩
private def rotate4 : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
private def reflect4 : Perm 4 := ⟨#v[0, 3, 2, 1], by decide, by decide⟩
private def swap4 : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
private def three4 : Perm 4 := ⟨#v[1, 2, 0, 3], by decide, by decide⟩
private def double4 : Perm 4 := ⟨#v[1, 0, 3, 2], by decide, by decide⟩
private def five5 : Perm 5 := ⟨#v[1, 2, 3, 4, 0], by decide, by decide⟩
private def three5 : Perm 5 := ⟨#v[1, 2, 0, 3, 4], by decide, by decide⟩
private def swap2 : Perm 2 := ⟨#v[1, 0], by decide, by decide⟩

private def s3Group : Group 3 := Group.ofGenerators #[swap3, cycle3]
private def c2InS3 : Group 3 := Group.ofGenerators #[swap3]
private def d4Group : Group 4 := Group.ofGenerators #[rotate4, reflect4]
private def c2Group : Group 2 := Group.ofGenerators #[swap2]
private def c4Group : Group 4 := Group.ofGenerators #[rotate4]
private def a4Group : Group 4 := Group.ofGenerators #[three4, double4]
private def s4Group : Group 4 := Group.ofGenerators #[swap4, rotate4]
private def a5Group : Group 5 := Group.ofGenerators #[five5, three5]
private def intransitive4 : Group 4 := Group.ofGenerators #[swap4]
private def trivial3 : Group 3 := Group.ofGenerators #[]

private def requireSubgroup (H G : Group n) : IO (PLift (H.IsSubgroup G)) := do
  if h : H.isSubgroup G = true then
    return ⟨(Group.isSubgroup_iff H G).mp h⟩
  else
    throw (IO.userError "fixture subgroup is not contained in its ambient group")

private def cycleImages (lengths : List Nat) : List Nat :=
  (lengths.foldl (fun (offset, result) length =>
    (offset + length, result ++ (List.range length).map fun i =>
      offset + (i + 1) % length)) (0, [])).2

private def largeCycleLengths : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

private def largeGeneratorImages : List (List Nat) :=
  [cycleImages largeCycleLengths]

private def buildLarge : IO (Group 381) := do
  let mut generators : Array (Perm 381) := #[]
  for xs in largeGeneratorImages do
    let some p := Perm.ofNatArray? 381 xs.toArray
      | throw (IO.userError "large-order generator rejected")
    generators := generators.push p
  return Group.ofGenerators generators

private def cases : IO (List Json) := do
  let G := s3Group
  let H := c2InS3
  let hHG := (← requireSubgroup H G).down
  let .ok transversal := G.leftCosetsWith G.order H hHG
    | throw (IO.userError "S3 transversal unexpectedly exceeded its cap")
  let pointStabilizer := G.stabilizer 0

  let natural := Action.natural G
  let naturalDomain : Array (Fin 3) := #[0, 1, 2]
  let .ok actionImage := natural.actionImage naturalDomain.size naturalDomain
    | throw (IO.userError "natural action image rejected its exact domain")
  let .ok actionKernel := natural.actionKernel naturalDomain.size naturalDomain
    | throw (IO.userError "natural action kernel rejected its exact domain")
  let tupleBase : Vector (Fin 3) 2 := #v[0, 0]
  let .ok tupleOrbit := (Action.tuples G 2).breadthFirst tupleBase 3
    | throw (IO.userError "tuple action orbit rejected its exact domain")
  let emptySubset : Vector Bool 3 := #v[false, false, false]
  let .ok emptySubsetOrbit := (Action.subsets G).breadthFirst emptySubset 1
    | throw (IO.userError "empty subset orbit rejected its exact domain")
  let partA := Partition.ofValues #v[(0 : Nat), 0, 1]
  let partB := Partition.ofValues #v[(0 : Nat), 1, 0]
  let partC := Partition.ofValues #v[(0 : Nat), 1, 1]
  let partitionDomain : Array (Partition 3) := #[partA, partB, partC]
  let .ok partitionImage := (Action.partitions G).actionImage 3 partitionDomain
    | throw (IO.userError "partition action image rejected its exact domain")
  let .ok partitionKernel := (Action.partitions G).actionKernel 3 partitionDomain
    | throw (IO.userError "partition action kernel rejected its exact domain")

  let source : Vector Bool 3 := #v[true, true, false]
  let target : Vector Bool 3 := #v[false, true, true]
  let negativeTarget : Vector Bool 3 := #v[true, false, false]
  let transporter := G.setTransporter? source target
  let negativeTransporter := G.setTransporter? source negativeTarget
  let transporterImage := transporter.map fun p => images p.val
  let setStabilizer := G.setStabilizer source
  let .ok subsetOrbit := (Action.subsets G).breadthFirst source 3
    | throw (IO.userError "subset action orbit rejected its exact domain")

  let blocks := d4Group.blocks [(0, 2)]
  let .ok blockAction := d4Group.blockAction blocks
      (d4Group.blocks_invariant [(0, 2)]) blocks.blocks.size
    | throw (IO.userError "block action rejected its canonical domain")

  let normalClosure := G.normalClosure H hHG
  let core := G.core H hHG
  let series := G.derivedSeries
  let direct := c2Group.directProduct c2Group
  let wreath := c2Group.wreathProduct c2Group (by decide)

  let ranks := G.enumerate.toList.map fun p => (G.rank p).val
  let samples : List (Element G) :=
    Group.sampleWith (fun bound _ => List.finRange bound) G
  let sampledRanks := samples.map fun p => (G.rank p).val

  let producerStatus := match Group.buildWith {} #[swap3, cycle3] with
    | .exhausted _ => "limited"
    | .ok _ _ => "complete"
  let malformed : Program := ⟨#[.comp 0 0], 0⟩
  let replayStatus := if checkWord #[swap3, cycle3] swap3 malformed then
      "accepted" else "rejected"

  let large ← buildLarge
  pure <|
    [ record "s3-chain" "chain-cosets" "complete" 3 (generatorImages G)
        [("order", toJson G.order), ("query", toJson (images (swap3.comp cycle3))),
         ("member", toJson (G.contains (swap3.comp cycle3))),
         ("orbits", toJson (pointLists G.orbits)),
         ("stabilizer_order", toJson pointStabilizer.order),
         ("stabilizer_generators", toJson (generatorImages pointStabilizer)),
         ("subgroup_generators", toJson (generatorImages H)),
         ("subgroup_index", toJson transversal.reps.size),
         ("left_representatives", toJson
           (transversal.reps.toList.map fun p => images p.val))]
    , record "s3-elementary" "elementary" "complete" 3 (generatorImages G)
        [("left", toJson (images swap3)), ("right", toJson (images cycle3)),
         ("hex_product", toJson (images (swap3.comp cycle3))),
         ("sign", toJson swap3.sign),
         ("cycle_type", toJson swap3.cycleType.toList),
         ("transitive", toJson G.isTransitive),
         ("abelian", toJson G.isAbelian),
         ("join_order", toJson (H.join (Group.ofGenerators #[cycle3])).order)]
    , record "s3-action" "actions-kernel" "complete" 3 (generatorImages G)
        [("domain", toJson (naturalDomain.toList.map Fin.val)),
         ("domain_identification", toJson (naturalDomain.toList.map Fin.val)),
         ("image_order", toJson actionImage.group.order),
         ("kernel_order", toJson actionKernel.group.order),
         ("tuple", toJson [0, 0]),
         ("tuple_orbit_size", toJson tupleOrbit.val.objects.size),
         ("subset", toJson [0, 1]),
         ("subset_orbit_size", toJson subsetOrbit.val.objects.size),
         ("empty_subset_orbit_size", toJson emptySubsetOrbit.val.objects.size),
         ("partition_domain", toJson
           (partitionDomain.toList.map fun p => p.labels.toArray.toList.map Fin.val)),
         ("partition_image_order", toJson partitionImage.group.order),
         ("partition_kernel_order", toJson partitionKernel.group.order)]
    , record "s3-search" "subgroup-search" "complete" 3 (generatorImages G)
        [("subgroup_generators", toJson (generatorImages H)),
         ("subset", toJson [0, 1]), ("target", toJson [1, 2]),
         ("set_stabilizer_order", toJson setStabilizer.order),
         ("intersection_order", toJson (G.intersection H).order),
         ("centralizer_order", toJson (G.centralizer H).order),
         ("normalizer_order", toJson (G.normalizer H).order),
         ("transporter_exists", toJson transporter.isSome),
         ("transporter", toJson transporterImage),
         ("negative_target", toJson [0]),
         ("negative_transporter_exists", toJson negativeTransporter.isSome)]
    , record "d4-blocks" "blocks" "complete" 4 (generatorImages d4Group)
        [("domain", toJson (List.range 4)), ("seed", toJson [0, 2]),
         ("blocks", toJson (partitionBlocks blocks)),
         ("primitive", toJson d4Group.isPrimitive),
         ("block_image_order", toJson blockAction.image.group.order),
         ("block_kernel_order", toJson blockAction.kernel.group.order)]
    , record "s3-normal" "normal-structure" "complete" 3 (generatorImages G)
        [("subgroup_generators", toJson (generatorImages H)),
         ("normal_closure_order", toJson normalClosure.order),
         ("core_order", toJson core.order),
         ("derived_order", toJson G.derived.order),
         ("derived_series_orders", toJson (series.certificate.orders G)),
         ("solvable", toJson G.isSolvable),
         ("normal", toJson (H.isNormal G hHG))]
    , record "c2-products" "products" "complete" 2 (generatorImages c2Group)
        [("right_degree", toJson (2 : Nat)),
         ("right_generators", toJson (generatorImages c2Group)),
         ("direct_degree", toJson (2 + 2 : Nat)),
         ("direct_generator_count", toJson direct.generators.size),
         ("direct_order", toJson direct.order),
         ("wreath_degree", toJson (2 * 2 : Nat)),
         ("wreath_generator_count", toJson wreath.generators.size),
         ("wreath_order", toJson wreath.order),
         ("domain_identification", toJson
           ((List.range 2).flatMap fun i => (List.range 2).map fun j => [i, j]))]
    , record "s3-rank" "rank-unrank-sampling" "complete" 3 (generatorImages G)
        [("indices", toJson ranks), ("sampled_indices", toJson sampledRanks),
         ("element_count", toJson G.enumerate.size),
         ("sampling_status", toJson
           (if ranks = sampledRanks then "complete" else "mismatch"))]
    , record "limits-corruption" "limits-corruption" "limited" 3 (generatorImages G)
        [("producer_status", toJson producerStatus),
         ("replay_status", toJson replayStatus),
         ("raw_input_retained", toJson
           (decide (generatorImages G = [images swap3, images cycle3])))]
    , record "trivial-fixed" "group-corpus" "complete" 3 (generatorImages trivial3)
        [("order", toJson trivial3.order), ("orbits", toJson (pointLists trivial3.orbits)),
         ("transitive", toJson trivial3.isTransitive),
         ("fixed_points", toJson (fixedPoints trivial3))]
    , record "cyclic-four" "group-corpus" "complete" 4 (generatorImages c4Group)
        [("order", toJson c4Group.order), ("orbits", toJson (pointLists c4Group.orbits)),
         ("transitive", toJson c4Group.isTransitive),
         ("fixed_points", toJson (fixedPoints c4Group))]
    , record "alternating-four" "group-corpus" "complete" 4 (generatorImages a4Group)
        [("order", toJson a4Group.order), ("orbits", toJson (pointLists a4Group.orbits)),
         ("transitive", toJson a4Group.isTransitive),
         ("fixed_points", toJson (fixedPoints a4Group))]
    , record "intransitive-fixed" "group-corpus" "complete" 4
        (generatorImages intransitive4)
        [("order", toJson intransitive4.order),
         ("orbits", toJson (pointLists intransitive4.orbits)),
         ("transitive", toJson intransitive4.isTransitive),
         ("fixed_points", toJson (fixedPoints intransitive4))]
    , record "s3-alternate-presentation" "group-corpus" "complete" 3
        (generatorImages (Group.ofGenerators #[cycle3, swap3, cycle3.inv, swap3]))
        [("order", toJson G.order), ("orbits", toJson (pointLists G.orbits)),
         ("transitive", toJson G.isTransitive), ("fixed_points", toJson (fixedPoints G)),
         ("reference_generators", toJson (generatorImages G))]
    , record "s4-derived" "normal-series" "complete" 4 (generatorImages s4Group)
        [("order", toJson s4Group.order), ("derived_order", toJson s4Group.derived.order),
         ("derived_series_orders", toJson
           (s4Group.derivedSeries.certificate.orders s4Group)),
         ("solvable", toJson s4Group.isSolvable)]
    , record "a5-perfect" "normal-series" "complete" 5 (generatorImages a5Group)
        [("order", toJson a5Group.order), ("derived_order", toJson a5Group.derived.order),
         ("derived_series_orders", toJson
           (a5Group.derivedSeries.certificate.orders a5Group)),
         ("solvable", toJson a5Group.isSolvable)]
    , record "order-over-u64" "large-order" "complete" 381 (generatorImages large)
        [("order_decimal", toJson (toString large.order)),
         ("fixed_points", toJson (fixedPoints large)),
         ("cycle_lengths", toJson largeCycleLengths)] ]

def main (_args : List String) : IO Unit := do
  for fixture in ← cases do IO.println fixture.compress
