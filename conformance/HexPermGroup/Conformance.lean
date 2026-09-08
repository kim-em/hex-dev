/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
import all Init.Data.Array.Basic
import all Init.Data.List.Basic
import all Init.Data.List.Sort.Basic

meta import HexPermGroup.Word
import HexPermGroup.Word
meta import HexPermGroup.Cycles
import HexPermGroup.Cycles
import HexPermGroup.Orbit
import HexPermGroup.Orbit.Schreier
meta import HexPermGroup.Orbit.Build
import HexPermGroup.Orbit.Build
import HexPermGroup.Check
import HexPermGroup.Group
meta import HexPermGroup.Normalize
import HexPermGroup.Normalize
meta import HexPermGroup.Build
import HexPermGroup.Build
meta import HexPermGroup.Conjugate
import HexPermGroup.Conjugate
meta import HexPermGroup.Predicates
import HexPermGroup.Predicates
meta import HexPermGroup.Rank
import HexPermGroup.Rank
meta import HexPermGroup.Enumerate
import HexPermGroup.Enumerate
meta import HexPermGroup.Membership
import HexPermGroup.Membership
meta import HexPermGroup.Action.Image
import HexPermGroup.Action.Image
meta import HexPermGroup.Action.Build
import HexPermGroup.Action.Build
meta import HexPermGroup.Action.Schreier
import HexPermGroup.Action.Schreier
meta import HexPermGroup.Action.Kernel
import HexPermGroup.Action.Kernel
meta import HexPermGroup.Coset.Right
import HexPermGroup.Coset.Right
meta import HexPermGroup.Search.Build
import HexPermGroup.Search.Build
meta import HexPermGroup.Search.Centralizer
import HexPermGroup.Search.Centralizer
meta import HexPermGroup.Search.Intersection
import HexPermGroup.Search.Intersection
meta import HexPermGroup.Search.Normalizer
import HexPermGroup.Search.Normalizer
meta import HexPermGroup.Search.Sets
import HexPermGroup.Search.Sets
meta import HexPermGroup.Search.SetTransporter
import HexPermGroup.Search.SetTransporter
meta import HexPermGroup.Search.Budgeted
import HexPermGroup.Search.Budgeted
meta import HexPermGroup.Search.Size
import HexPermGroup.Search.Size
meta import HexPermGroup.Partition
import HexPermGroup.Partition
meta import HexPermGroup.Blocks
import HexPermGroup.Blocks
meta import HexPermGroup.Blocks.Action
import HexPermGroup.Blocks.Action
meta import HexPermGroup.Blocks.Size
import HexPermGroup.Blocks.Size
meta import HexPermGroup.Primitivity
import HexPermGroup.Primitivity
meta import HexPermGroup.Normal.Closure
import HexPermGroup.Normal.Closure
meta import HexPermGroup.Normal.Cosets
import HexPermGroup.Normal.Cosets
meta import HexPermGroup.Normal.SeriesBounded
import HexPermGroup.Normal.SeriesBounded
meta import HexPermGroup.Product.Order
import HexPermGroup.Product.Order
meta import HexPermGroup.Product.WreathOrder
import HexPermGroup.Product.WreathOrder
meta import HexPermGroup.Word.Build
import HexPermGroup.Word.Build
meta import HexPermGroup.Word.Codec
import HexPermGroup.Word.Codec

/-! Kernel-replayed permutation and membership-program regressions. -/

namespace Hex.PermGroup.Conformance

private def cycle : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩
private def swap : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def generators : Array (Perm 3) := #[cycle, swap]

-- Declared degrees and fixed points are retained; raw input is never reduced.
example : Perm.ofNatArray? 0 #[] = some (Perm.id 0) := by decide
example : Perm.ofNatArray? 3 #[1, 2, 0] = some cycle := by decide
example : Perm.ofNatArray? 3 #[1, 0, 2] = some swap := by decide
example : Perm.ofNatArray? 3 #[1, 0] = none := by decide
example : Perm.ofNatArray? 3 #[1, 0, 3] = none := by decide
example : Perm.ofNatArray? 3 #[1, 1, 0] = none := by decide

-- Noncommuting factors detect accidental reversal of the action convention.
example : (cycle.comp swap).vec = #v[2, 1, 0] := by decide
example : (swap.comp cycle).vec = #v[0, 2, 1] := by decide
example : cycle.inv.vec = #v[2, 0, 1] := by decide

private def product : Program := ⟨#[.generator 0, .generator 1, .comp 0 1], 2⟩
private def inverse : Program := ⟨#[.generator 0, .inv 0], 1⟩
private def shared : Program := ⟨#[.generator 0, .comp 0 0, .comp 1 0], 2⟩

example : checkWord generators (cycle.comp swap) product = true := by decide
example : checkWord generators (swap.comp cycle) product = false := by decide
example : checkWord generators cycle.inv inverse = true := by decide
example : checkWord generators (Perm.id 3) shared = true := by decide
example : Generated generators (cycle.comp swap) := checkWord_sound (by decide :
  checkWord generators (cycle.comp swap) product = true)

-- Bad generator/root indices, cycles, forward references, and dead invalid nodes.
example : (Program.mk #[.generator 2] 0).eval generators = none := by decide
example : (Program.mk #[.id] 1).eval generators = none := by decide
example : (Program.mk #[] 0).eval generators = none := by decide
example : (Program.mk #[.inv 0] 0).eval generators = none := by decide
example : (Program.mk #[.inv 1, .id] 0).eval generators = none := by decide
example : (Program.mk #[.id, .comp 0 2] 0).eval generators = none := by decide
example : checkWord (#[] : Array (Perm 0)) (Perm.id 0) ⟨#[.id], 0⟩ = true := by decide

example : cycle.cycles = #[#[0, 1, 2]] := by decide
example : swap.cycles = #[#[0, 1]] := by decide
example : swap.cycleType = #[1, 2] := by decide +kernel
example : cycle.cycleType = #[3] := by decide +kernel
example : (Perm.id 0).cycleType = #[] := by decide +kernel
example : (Perm.id 3).cycleType = #[1, 1, 1] := by decide +kernel
example : cycle.order = 3 ∧ swap.order = 2 ∧ (Perm.id 0).order = 1 := by decide
example : cycle.sign = 1 ∧ swap.sign = -1 ∧ (Perm.id 0).sign = 1 := by decide
example : (cycle.comp swap).sign = cycle.sign * swap.sign := by decide
example : cycle ^ 3 = 1 ∧ swap ^ 2 = 1 := by decide

#eval do
  unless (Program.decode 1000 3 2 product.encode).toOption = some product do
    throw (IO.userError "program round trip failed")
  for (bytes, nodes, generators, input) in
      [(0, 3, 2, product.encode), (1000, 2, 2, product.encode),
       (1000, 3, 1, product.encode),
       (1000, 3, 2, (Program.mk #[.inv 0] 0).encode),
       (1000, 3, 2, (Program.mk #[.inv 1, .id] 0).encode),
       (1000, 3, 2, (Program.mk #[.id] 1).encode)] do
    if (Program.decode bytes nodes generators input).toOption.isSome then
      throw (IO.userError "malformed or oversized program accepted")

private def insertions (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertions x ys).map (y :: ·)

private def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertions x)

private theorem inverse_pair (p : Perm n) : ∀ q ∈ #[p, p.inv], q.inv ∈ #[p, p.inv] := by
  intro q hq
  simp at hq
  rcases hq with rfl | rfl <;> simp

example : (normalize (#[] : Array (Perm 0))).generators = #[] := by decide +kernel
example : (normalize #[Perm.id 3, Perm.id 3]).generators = #[] := by decide +kernel
example : checkWords #[Perm.id 3, cycle, cycle, cycle.inv, swap]
    (normalize #[Perm.id 3, cycle, cycle, cycle.inv, swap]).generators
    (normalize #[Perm.id 3, cycle, cycle, cycle.inv, swap]).words = true :=
  (normalize _).valid

#eval do
  let input := #[Perm.id 3, cycle, cycle, cycle.inv, swap]
  let result := normalize input
  unless result.generators = #[swap, cycle, cycle.inv] do
    throw (IO.userError "normalization did not sort or deduplicate the signed inputs")
  unless (normalize #[cycle]).generators = #[cycle, cycle.inv] do
    throw (IO.userError "normalization did not add the inverse generator")
  unless decide (Chain.Normalized input result.generators) &&
      checkWords input result.generators result.words do
    throw (IO.userError "normalization failed independent checking")

-- Independent small-degree checks: order by repeated multiplication, sign by
-- inversion parity, and cycle serialization by reconstructing raw images.
#eval do
  for n in List.range 6 do
    for rawList in permutations (List.range n) do
      let raw := rawList.toArray
      let some p := Perm.ofNatArray? n raw
        | throw (IO.userError s!"valid permutation rejected: {raw}")
      let mut residual := Perm.id n
      let mut referenceOrder := 0
      for k in List.range 120 do
        if referenceOrder = 0 then
          residual := p.comp residual
          if residual = Perm.id n then referenceOrder := k + 1
      unless referenceOrder > 0 && p.order = referenceOrder do
        throw (IO.userError s!"order mismatch: {raw}")
      let mut inversions := 0
      for i in List.range n do
        for j in List.range n do
          if i < j && raw[i]! > raw[j]! then inversions := inversions + 1
      let referenceSign : Int := if inversions % 2 = 0 then 1 else -1
      unless p.sign = referenceSign do
        throw (IO.userError s!"sign mismatch: {raw}")
      let mut images := (List.range n).toArray
      let mut seen : Array Nat := #[]
      let mut previous : Option Nat := none
      for cycle in p.cycles do
        let entries := cycle.map Fin.val
        unless entries.size ≥ 2 && entries[0]! = entries.foldl Nat.min n do
          throw (IO.userError s!"noncanonical cycle: {raw}")
        if let some last := previous then
          unless last < entries[0]! do
            throw (IO.userError s!"unsorted cycles: {raw}")
        previous := some entries[0]!
        for i in List.range entries.size do
          let x := entries[i]!
          if seen.contains x then
            throw (IO.userError s!"cycles overlap: {raw}")
          seen := seen.push x
          images := images.set! x entries[(i + 1) % entries.size]!
      unless images = raw do
        throw (IO.userError s!"cycle reconstruction mismatch: {raw}")
      let mut periods : Array Nat := #[]
      for x in List.finRange n do
        let mut current := x
        let mut period := 0
        for k in List.range n do
          if period = 0 then
            current := p.get current
            if current = x then period := k + 1
        periods := periods.push period
      let mut referenceType : Array Nat := #[]
      for k in List.range (n + 1) do
        if k > 0 then
          let count := periods.foldl (fun count period =>
            if period = k then count + 1 else count) 0
          for _ in List.range (count / k) do
            referenceType := referenceType.push k
      unless p.cycleType = referenceType do
        throw (IO.userError s!"cycle type mismatch: {raw}")
      for a in List.finRange n do
        let orbit : Orbit n := (Orbit.ofSymmetric #[p, p.inv] a (inverse_pair p)).val
        let mut image := a.val
        let mut reachable : Array Nat := #[]
        for _ in List.range n do
          reachable := reachable.push image
          image := raw[image]!
        for x in List.finRange n do
          unless orbit.lookup[x.val].isSome == reachable.contains x.val do
            throw (IO.userError s!"orbit mismatch: {raw}, base {a.val}, point {x.val}")
        unless checkOrbit #[p, p.inv] a orbit do
          throw (IO.userError s!"orbit certificate failed replay: {raw}, base {a.val}")

private def swapOrbit : Orbit 3 where
  points := #[0, 1]
  lookup := #v[some 0, some 1, none]
  reps := #v[Perm.id 3, swap]
  words := #v[⟨#[.id], 0⟩, ⟨#[.generator 0], 0⟩]

example : checkOrbit #[swap] 0 swapOrbit = true := by decide +kernel
example : checkOrbit generators 0 swapOrbit = false := by decide +kernel
example : checkOrbit #[swap] 0
    { swapOrbit with lookup := #v[swapOrbit.lookup[0], none, none] } = false := by decide +kernel
example : checkOrbit #[swap] 0
    { swapOrbit with reps := #v[Perm.id 3, Perm.id 3] } = false := by decide +kernel
example : checkOrbit #[swap] 0
    { swapOrbit with words := #v[⟨#[.id], 0⟩, ⟨#[.generator 1], 0⟩] } = false := by decide +kernel
example : ¬ ∃ p : Perm 3, Generated #[swap] p ∧ p.get 0 = 2 := by
  rw [← checkOrbit_sound (by decide +kernel : checkOrbit #[swap] 0 swapOrbit = true)]
  simp [swapOrbit]

private def fullOrbit : Orbit 3 where
  points := #[0, 1, 2]
  lookup := #v[some 0, some 1, some 2]
  reps := #v[Perm.id 3, cycle, cycle.comp cycle]
  words := #v[⟨#[.id], 0⟩, ⟨#[.generator 0], 0⟩,
    ⟨#[.generator 0, .comp 0 0], 1⟩]

private theorem fullOrbit_valid : fullOrbit.Valid generators 0 := by decide +kernel
private def swap12 : Perm 3 := ⟨#v[0, 2, 1], by decide, by decide⟩

-- Neither original generator fixes zero. Filtering that array misses the
-- nonidentity stabilizer element supplied by the complete Schreier family.
example : cycle.get 0 ≠ 0 ∧ swap.get 0 ≠ 0 := by decide
example : swap12 ∈ Orbit.stabilizerGens fullOrbit_valid := by decide +kernel
example : Generated (Orbit.stabilizerGens fullOrbit_valid) swap12 :=
  .generator (by decide +kernel)
example : ¬ Generated (Orbit.stabilizerGens fullOrbit_valid) cycle := by
  rw [Orbit.stabilizerGens_spec]
  intro h
  exact (by decide : cycle.get 0 ≠ 0) h.2

private def squares : (steps : Nat) → (b : Program.Builder generators) →
    Fin b.values.size → (Σ b : Program.Builder generators, Fin b.values.size)
  | 0, b, i => ⟨b, i⟩
  | k + 1, b, i =>
    let next := b.comp i i
    squares k next ⟨b.values.size, by simp [next]⟩

-- Sixty-four repeated squarings share references to the preceding node: the
-- certificate contains 65 nodes rather than expanding a word of length 2^64.
#eval do
  let start := (Program.Builder.empty generators).generator ⟨0, by decide⟩
  let ⟨builder, root⟩ := squares 64 start ⟨0, by simp [start, Program.Builder.empty]⟩
  unless builder.nodes.size = 65 do
    throw (IO.userError "word construction lost shared nodes")
  unless checkWord generators cycle (builder.program root) do
    throw (IO.userError "shared program failed replay")
  let replacements : Vector Program generators.size :=
    #v[⟨#[.generator 1], 0⟩, ⟨#[.generator 0], 0⟩]
  have hr : checkWords #[swap, cycle] generators replacements = true := by decide +kernel
  let translated := Program.substitute #[swap, cycle] generators replacements hr
    (builder.program root) (builder.check_program root)
  unless translated.nodes.size == 68 && checkWord #[swap, cycle] cycle translated do
    throw (IO.userError "substitution expanded shared references or changed generator indices")
  let inverse := builder.inv root
  let inverseRoot : Fin inverse.values.size :=
    ⟨builder.values.size, by simp [inverse, Program.Builder.inv, Program.Builder.push]⟩
  let inverted := Program.substitute #[swap, cycle] generators replacements hr
    (inverse.program inverseRoot) (inverse.check_program inverseRoot)
  unless inverted.nodes.size == 69 && checkWord #[swap, cycle] cycle.inv inverted do
    throw (IO.userError "substitution lost an inverse reference")

example : checkWord (#[] : Array (Perm 0)) (Perm.id 0)
    (Program.substitute (#[] : Array (Perm 0)) #[] #v[] (by decide +kernel)
      ⟨#[.id], 0⟩ (p := Perm.id 0) (by decide +kernel)) = true := Program.check_substitute ..

private def singleton (a : Fin n) : Orbit n where
  points := #[a]
  lookup := Hex.Vector.ofFn' fun x => if x = a then some 0 else none
  reps := #v[Perm.id n]
  words := #v[⟨#[.id], 0⟩]

private def trivialLevel (a : Fin n) : Level n :=
  ⟨#[], #v[], singleton a⟩

private def lastLevel : Chain 3 := .cons (trivialLevel 2) (.leaf #[] #v[])
private def trivialSuffix : Chain 3 := .cons (trivialLevel 1) lastLevel

private def swapChain : Chain 3 :=
  .cons ⟨#[swap], #v[⟨#[.generator 0], 0⟩], swapOrbit⟩ trivialSuffix

private def middle : Level 3 where
  generators := #[swap12]
  words := #v[⟨#[.generator 1, .inv 0, .generator 0, .comp 1 2], 3⟩]
  orbit :=
    { points := #[1, 2]
      lookup := #v[none, some 0, some 1]
      reps := #v[Perm.id 3, swap12]
      words := #v[⟨#[.id], 0⟩, ⟨#[.generator 0], 0⟩] }

private def first : Level 3 where
  generators := #[swap, cycle, cycle.inv]
  words := #v[⟨#[.generator 1], 0⟩, ⟨#[.generator 0], 0⟩,
    ⟨#[.generator 0, .inv 0], 1⟩]
  orbit :=
    { fullOrbit with words := #v[⟨#[.id], 0⟩, ⟨#[.generator 1], 0⟩,
        ⟨#[.generator 1, .comp 0 0], 1⟩] }

private def fullChain : Chain 3 := .cons first (.cons middle lastLevel)

private def indexedGroup : Group 3 := ⟨generators, fullChain, by decide +kernel⟩

private def swapGroup : Group 3 := ⟨#[swap], swapChain, by decide +kernel⟩
private def trivialGroup : Group 3 := ⟨#[], .cons (trivialLevel 0) trivialSuffix, by decide +kernel⟩
private def zeroGroup : Group 0 := ⟨#[], .leaf #[] #v[], by decide +kernel⟩

private def closureChain : Chain 3 :=
  .cons
    { generators := #[swap12, swap]
      words := #v[⟨#[.generator 1], 0⟩, ⟨#[.generator 0], 0⟩]
      orbit := { fullOrbit with words := #v[⟨#[.id], 0⟩,
        ⟨#[.generator 1, .generator 0, .comp 0 1], 2⟩,
        ⟨#[.generator 1, .generator 0, .comp 0 1, .comp 2 2], 3⟩] } }
    (.cons { middle with words := #v[⟨#[.generator 0], 0⟩] } lastLevel)

private def conjugateChain : Chain 3 :=
  .cons ⟨#[swap12], #v[⟨#[.generator 0], 0⟩], singleton 0⟩
    (.cons { middle with words := #v[⟨#[.generator 0], 0⟩] } lastLevel)

private def coreTrace : List (Core.Step 3) :=
  [⟨2, conjugateChain, trivialGroup, .branch #[.covered, .rejected ()]⟩]

-- These are literal certificates: kernel replay invokes no normal-closure or
-- core producer to obtain the answer or the insertion/intersection trace.
example : checkChain #[swap, swap12] closureChain = true := by decide +kernel
example : Normal.checkClosure indexedGroup swapGroup indexedGroup [⟨1, 0, closureChain⟩] = true := by
  decide +kernel
example : Normal.checkClosure indexedGroup swapGroup indexedGroup [] = false := by decide +kernel
example : Normal.checkClosure indexedGroup trivialGroup indexedGroup [] = false := by decide +kernel
example : Core.check indexedGroup swapGroup trivialGroup coreTrace = true := by decide +kernel
example : Core.check indexedGroup swapGroup swapGroup coreTrace = false := by decide +kernel
example : Core.check indexedGroup indexedGroup trivialGroup [] = false := by decide +kernel
example : Series.check indexedGroup .trivial = false := by decide +kernel
example : Series.check trivialGroup .trivial = true := by decide +kernel
example : Series.check zeroGroup .trivial = true := by decide +kernel

private def commuteSwap := Search.Centralizer.constraint indexedGroup swapGroup

-- A checked output chain cannot replace search completeness. At the root no
-- point is assigned, so claiming an impossible forced image is also invalid.
example : Search.checkSearch commuteSwap trivialGroup .covered = false := by decide +kernel
example : Search.checkSearch commuteSwap trivialGroup (.rejected (⟨0, by decide⟩, 0)) = false := by
  decide +kernel
example : Search.checkSearch commuteSwap indexedGroup .covered = false := by decide +kernel
example : Search.checkTree commuteSwap indexedGroup (Search.Node.root indexedGroup) .leaf = false := by
  decide +kernel
example : Search.checkTree (Search.Constraint.none zeroGroup (Search.Predicate.subgroup zeroGroup))
    zeroGroup (Search.Node.root zeroGroup) (.branch #[]) = false := by decide +kernel

-- Equal total cardinalities do not compensate for incompatible counts on a
-- remaining point orbit. No point has been assigned at this root.
example : Search.Sets.reject #v[true, false, false] #v[false, false, true]
    (Search.Node.root swapGroup) (.orbit 0) = true := by decide +kernel
example : Search.Sets.reject #v[true, false, false] #v[false, false, true]
    (Search.Node.root swapGroup) (.color 0) = false := by decide +kernel

example : Search.checkSearch (Search.Constraint.none swapGroup (Search.Predicate.subgroup swapGroup)) swapGroup
    (.branch #[.covered, .covered]) = true := by decide +kernel

private def incompatible : Search.Node indexedGroup :=
  (Search.Node.root indexedGroup).child (by rfl) ⟨2, by decide⟩

example : Search.Centralizer.reject swapGroup incompatible (⟨0, by decide⟩, 0) = true := by decide +kernel
example : Search.Normalizer.reject swapGroup incompatible (.size 0) = true := by decide +kernel
example : Search.Intersection.reject swapGroup incompatible = true := by decide +kernel
example : Search.checkTree commuteSwap trivialGroup incompatible (.rejected (⟨0, by decide⟩, 0)) = true := by
  decide +kernel

private def unequalSets := Search.Sets.transporter swapGroup #v[true, false, false] #v[true, true, false]
example : Search.checkFailure unequalSets (Search.Node.root swapGroup) (.rejected .cardinality) = true := by
  decide +kernel
example : Search.checkFailure unequalSets (Search.Node.root swapGroup)
    (.branch #[.rejected .cardinality, .rejected .cardinality]) = true := by decide +kernel
example : Search.checkFailure unequalSets (Search.Node.root swapGroup) .covered = false := by decide +kernel
example : Search.checkFailure (Search.Sets.transporter swapGroup #v[true, false, false] #v[false, true, false])
    (Search.Node.root swapGroup) (.rejected .cardinality) = false := by decide +kernel
example : Search.checkWitness indexedGroup (Search.Sets.test #v[true, false, false] #v[false, true, false])
    cycle ⟨#[.generator 0], 0⟩ = true := by decide +kernel
example : Search.checkWitness indexedGroup (Search.Sets.test #v[true, false, false] #v[false, true, false])
    cycle ⟨#[.generator 1], 0⟩ = false := by decide +kernel
example : Search.checkWitness indexedGroup (Search.Sets.test #v[true, false, false] #v[false, false, true])
    cycle ⟨#[.generator 0], 0⟩ = false := by decide +kernel

-- These fixed digits distinguish most-significant-first ranking from a
-- different bijection that could still satisfy both round-trip equations.
example : (indexedGroup.rank? cycle).map Fin.val = some 2 := by decide +kernel
example : (indexedGroup.rank? swap).map Fin.val = some 3 := by decide +kernel
example : (indexedGroup.rank? swap12).map Fin.val = some 1 := by decide +kernel

example : checkChain (#[] : Array (Perm 0)) (.leaf #[] #v[]) = true := by decide +kernel
example : checkChain #[swap] swapChain = true := by decide +kernel
example : checkChain generators fullChain = true := by decide +kernel
example : fullChain.orbitProduct = 6 ∧ swapChain.orbitProduct = 2 := by decide
example : fullChain.accepts 0 swap12 = true := by decide +kernel
example : swapChain.accepts 0 cycle = false := by decide +kernel
example : ¬ Generated #[swap] cycle := by
  rw [← sift_iff (by decide +kernel : checkChain #[swap] swapChain = true)]
  decide +kernel

-- The complete top orbit cannot compensate for a missing stabilizer generator.
example : checkChain generators (.cons first trivialSuffix) = false := by decide +kernel
example : checkChain generators swapChain = false := by decide +kernel
example : checkChain generators (.cons first (.leaf #[] #v[])) = false := by decide +kernel
example : checkChain generators (.cons first (.cons middle
    (.cons (trivialLevel 2) (.leaf #[swap12] #v[⟨#[.id], 0⟩])))) = false := by decide +kernel
example : checkChain generators (.cons { first with
    words := #v[⟨#[.generator 9], 0⟩, ⟨#[.generator 0], 0⟩,
      ⟨#[.generator 0, .inv 0], 1⟩] } (.cons middle lastLevel)) = false := by decide +kernel

example : (match swapChain.sift 0 cycle with
    | .missing level image => decide (level = 1 ∧ image = 2)
    | _ => false) = true := by decide +kernel
example : (match fullChain.sift 0 swap12 with
    | .member digits => decide (digits = [0, 1, 0])
    | _ => false) = true := by decide +kernel
example : (match fullChain.sift 3 (Perm.id 3) with
    | .shape level => decide (level = 3)
    | _ => false) = true := by decide +kernel
example : (Group.ofChain? generators fullChain).isSome = true := by decide +kernel
example : (Group.ofChain? generators (.cons first trivialSuffix)).isSome = false := by decide +kernel

private def symmetric : Array (Perm 3) := #[Perm.id 3, cycle.inv, cycle, cycle, swap]
private theorem symmetric_inv : ∀ p ∈ symmetric, p.inv ∈ symmetric := by decide +kernel

-- Identity and repeated generators do not change discovery order or renumber
-- the generator references carried by the first successful parent edges.
example : (Orbit.breadthFirst symmetric 0).val.points = #[0, 2, 1] := by decide +kernel
example : ((Orbit.breadthFirst symmetric 0).val.parents.toArray.map
    fun parent => parent.map fun (k, i) => (k, i.val)) =
    #[none, some (0, 1), some (0, 2)] := by decide +kernel
example : checkOrbit symmetric 0 (Orbit.ofSymmetric symmetric 0 symmetric_inv).val = true :=
  Orbit.ofSymmetric_checks ..
example : (Orbit.ofSymmetric symmetric 0 symmetric_inv).val.reps.toArray =
    #[Perm.id 3, cycle.inv, cycle] := by decide +kernel
example : checkOrbit (#[] : Array (Perm 3)) 2
    (Orbit.ofSymmetric #[] 2 (by simp)).val = true := by decide +kernel

private def left5 : Perm 5 := ⟨#v[1, 0, 3, 2, 4], by decide, by decide⟩
private def right5 : Perm 5 := ⟨#v[0, 2, 1, 4, 3], by decide, by decide⟩
private def path5 : Array (Perm 5) := #[left5, right5]
private theorem path5_inv : ∀ p ∈ path5, p.inv ∈ path5 := by decide +kernel

#eval do
  let tree : Orbit.Tree path5 0 := (Orbit.breadthFirst path5 0).val
  unless tree.points == #[0, 1, 2, 3, 4] do
    throw (IO.userError "BFS did not retain queue order along the five-point path")
  unless (tree.parents.toArray.map fun parent =>
      Option.map (fun (pair : Nat × Fin path5.size) => (pair.1, pair.2.val)) parent) ==
      #[none, some (0, 0), some (1, 1), some (2, 0), some (3, 1)] do
    throw (IO.userError "BFS parent edges do not follow the discovery path")
  let orbit : Orbit 5 := (Orbit.ofSymmetric path5 0 path5_inv).val
  unless checkOrbit path5 0 orbit do
    throw (IO.userError "compiled BFS certificate failed independent replay")
  for word in orbit.words.toArray do
    unless (Program.nodes word).size == 9 do
      throw (IO.userError "transporters did not share one node arena")
  let fixed : Orbit 3 := (Orbit.ofSymmetric #[swap] 2 (by decide +kernel)).val
  unless fixed.points == #[2] &&
      (fixed.lookup.toArray.map (Option.map Fin.val)) == #[none, none, some 0] do
    throw (IO.userError "fixed-point orbit included an unreachable point")
  unless checkOrbit #[swap] 2 fixed do
    throw (IO.userError "fixed-point certificate failed replay")
  let some longCycle := Perm.ofNatArray? 512
      ((List.range 512).map fun i => (i + 1) % 512).toArray
    | throw (IO.userError "long cycle construction failed")
  let longOrbit : Orbit 512 :=
    (Orbit.ofSymmetric #[longCycle, longCycle.inv] 0 (inverse_pair longCycle)).val
  unless longOrbit.points.size == 512 do
    throw (IO.userError "long cycle orbit is incomplete")
  let some lastWord := longOrbit.words.toArray.back?
    | throw (IO.userError "long cycle orbit has no transporter")
  unless lastWord.nodes.size == 1023 && (lastWord.eval #[longCycle, longCycle.inv]).isSome do
    throw (IO.userError "long cycle did not produce a compact, replayable program")

-- Exhaustive closure is only a small-degree test oracle. It multiplies raw image
-- arrays independently of `Perm.comp`; the production builder never enumerates
-- group elements when establishing membership or order.
private def closure (n : Nat) (generators : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut values := #[(List.range n).toArray]
  let mut cursor := 0
  for _ in List.range ((List.range n).foldl (fun product i => product * (i + 1)) 1) do
    if cursor < values.size then
      let current := values[cursor]!
      for generator in generators do
        let next := current.map fun i => generator[i]!
        unless values.contains next do values := values.push next
      cursor := cursor + 1
  return values

private def composeImages (p q : Array Nat) : Array Nat := q.map fun i => p[i]!

private def inverseImages (p : Array Nat) : Array Nat :=
  ((List.range p.size).map fun i => p.toList.idxOf i).toArray

private def sumImages (p q : Array Nat) : Array Nat := p ++ q.map (p.size + ·)

private def checkDirectProduct (G : Group n) (H : Group m) : IO Unit := do
  let left := closure n (G.generators.map fun p => p.vec.toArray.map Fin.val)
  let right := closure m (H.generators.map fun q => q.vec.toArray.map Fin.val)
  let expected := left.flatMap fun p => right.map (sumImages p)
  let product := G.directProduct H
  unless product.order == expected.size && checkChain product.generators product.chain &&
      product.generators.size == G.generators.size + H.generators.size do
    throw (IO.userError "direct product order, generator count or chain check failed")
  for raw in expected do
    let some p := Perm.ofNatArray? (n + m) raw
      | throw (IO.userError "independent direct product permutation rejected")
    unless product.contains p do throw (IO.userError "direct product omitted a factor pair")
  let elements := product.enumerate
  for r in elements do
    let raw := r.val.vec.toArray.map Fin.val
    let a := DirectProduct.fst r
    let b := DirectProduct.snd r
    let rawA := a.val.vec.toArray.map Fin.val
    let rawB := b.val.vec.toArray.map Fin.val
    unless expected.contains raw && left.contains rawA && right.contains rawB &&
        raw == sumImages rawA rawB && DirectProduct.pair a b == r &&
        (DirectProduct.inl H a).comp (DirectProduct.inr G b) == r &&
        (DirectProduct.inr G b).comp (DirectProduct.inl H a) == r do
      throw (IO.userError "direct product projections, embeddings or unique decomposition failed")
    for s in elements do
      let rawC := (DirectProduct.fst s).val.vec.toArray.map Fin.val
      let rawD := (DirectProduct.snd s).val.vec.toArray.map Fin.val
      unless (r.comp s).val.vec.toArray.map Fin.val ==
          sumImages (composeImages rawA rawC) (composeImages rawB rawD) do
        throw (IO.userError "direct product multiplication disagrees with independent factor composition")
  if n > 0 && m > 0 then
    let raw := ((List.range (n + m)).toArray.set! (n - 1) n).set! n (n - 1)
    let some p := Perm.ofNatArray? (n + m) raw
      | throw (IO.userError "mixed-support transposition rejected as malformed")
    if product.contains p then throw (IO.userError "direct product mixed its consecutive supports")

private def rawTuples (values : Array (Array Nat)) : Nat → Array (Array (Array Nat))
  | 0 => #[#[]]
  | m + 1 => (rawTuples values m).flatMap fun tail => values.map fun p => tail.push p

private def wreathImages (n m : Nat) (base : Array (Array Nat)) (top : Array Nat) : Array Nat :=
  ((List.range (n * m)).map fun x =>
    let destination := top[x / n]!
    destination * n + base[destination]![x % n]!).toArray

private def checkWreathProduct (G : Group n) (H : Group m) : IO Unit := do
  if hn : 0 < n then
    let left := closure n (G.generators.map fun p => p.vec.toArray.map Fin.val)
    let right := closure m (H.generators.map fun p => p.vec.toArray.map Fin.val)
    let expected := (rawTuples left m).flatMap fun f => right.map (wreathImages n m f)
    let .ok product := G.wreathProduct? H
      | throw (IO.userError "wreath product rejected nonempty blocks")
    unless product.order == expected.size && product.order == left.size ^ m * right.size &&
        product.generators.size == m * G.generators.size + H.generators.size &&
        checkChain product.generators product.chain do
      throw (IO.userError "wreath product order, generator count or chain check failed")
    for raw in (permutations (List.range (n * m))).map List.toArray do
      let some p := Perm.ofNatArray? (n * m) raw
        | throw (IO.userError "wreath reference candidate rejected")
      unless product.contains p == expected.contains raw do
        throw (IO.userError "wreath product membership disagrees with independent base/top enumeration")
    let exact := G.wreathProduct H hn
    let elements := exact.enumerate
    for r in elements do
      let f := WreathProduct.base hn r
      let h := WreathProduct.top hn r
      let rawBase := (List.finRange m).toArray.map fun j => (f j).val.vec.toArray.map Fin.val
      let rawTop := h.val.vec.toArray.map Fin.val
      unless rawBase.all left.contains && right.contains rawTop &&
          r.val.vec.toArray.map Fin.val == wreathImages n m rawBase rawTop &&
          WreathProduct.pair hn f h == r &&
          (WreathProduct.inl H hn f).comp (WreathProduct.inr G hn h) == r do
        throw (IO.userError "wreath projections or unique decomposition failed")
      let fixesBlocks := (List.range (n * m)).all fun x =>
        (r.val.vec.toArray.map Fin.val)[x]! / n == x / n
      unless (h == Element.id H) == fixesBlocks do
        throw (IO.userError "top projection kernel failed to identify the base group")
      for s in elements do
        let g := WreathProduct.base hn s
        let k := WreathProduct.top hn s
        let rawOther := (List.finRange m).toArray.map fun j => (g j).val.vec.toArray.map Fin.val
        let invTop := inverseImages rawTop
        let newBase := (List.range m).toArray.map fun j => composeImages rawBase[j]! rawOther[invTop[j]!]!
        let newTop := composeImages rawTop (k.val.vec.toArray.map Fin.val)
        unless (r.comp s).val.vec.toArray.map Fin.val == wreathImages n m newBase newTop do
          throw (IO.userError "wreath multiplication used the wrong base-factor index")
      for j in List.finRange m do
        for p in G.enumerate do
          let lifted := WreathProduct.inr G hn h
          unless lifted.comp ((WreathProduct.copy H hn j p).comp lifted.inv) ==
              WreathProduct.copy H hn (h.val.get j) p do
            throw (IO.userError "top conjugation failed to permute the base factors")
  else
    match G.wreathProduct? H with
    | .error .emptyBlocks => pure ()
    | .ok _ => throw (IO.userError "empty-block wreath request was accepted")

private def referenceDerived (n : Nat) (reference : Array (Array Nat)) : Array (Array Nat) :=
  closure n (reference.flatMap fun p => reference.map fun q =>
    composeImages p (composeImages q (composeImages (inverseImages p) (inverseImages q))))

private def checkDerivedStep (G K : Group n) (reference : Array (Array Nat))
    (candidates : List (Array Nat)) (c : Derived.Certificate n) : IO (Array (Array Nat)) := do
  let expected := referenceDerived n reference
  unless Derived.check G K c && K.order == expected.size && K.isSubgroup G && Normal.check G K do
    throw (IO.userError "derived subgroup replay, order, containment or normality failed")
  for raw in candidates do
    let some p := Perm.ofNatArray? n raw
      | throw (IO.userError "derived subgroup candidate rejected")
    unless K.contains p == expected.contains raw do
      throw (IO.userError "derived subgroup disagrees with all-element commutator closure")
  if K.order < G.order && Derived.check G G c then
    throw (IO.userError "derived checker accepted extraneous elements")
  return expected

private def checkSeries (G : Group n) (reference : Array (Array Nat))
    (candidates : List (Array Nat)) (c : Series.Certificate n) : IO Unit := do
  unless Series.check G c do throw (IO.userError "derived-series replay failed")
  match c with
  | .trivial =>
    unless reference.size == 1 do throw (IO.userError "nontrivial reference group was declared trivial")
  | .perfect K d =>
    let expected ← checkDerivedStep G K reference candidates d
    unless expected.size == reference.size && expected.size > 1 do
      throw (IO.userError "nonsolvability certificate is not a nontrivial perfect group")
  | .step K d tail =>
    let expected ← checkDerivedStep G K reference candidates d
    unless expected.size < reference.size do throw (IO.userError "derived-series step was not strict")
    if Series.check G tail || Series.check G (.perfect G d) then
      throw (IO.userError "derived-series checker accepted a missing step or false fixed point")
    checkSeries K expected candidates tail

private def checkDerivedSeries (G : Group n) (reference : Array (Array Nat))
    (candidates : List (Array Nat)) : IO Unit := do
  let d := Derived.build G
  let _ ← checkDerivedStep G d.group reference candidates d.certificate
  let s := G.derivedSeries
  checkSeries G reference candidates s.certificate
  unless 2 ^ s.certificate.depth * (s.certificate.terminal G).order ≤ G.order do
    throw (IO.userError "derived-series strict-decrease bound failed")
  let cost := (s.certificate.orders G).length - 1
  for cap in List.range (cost + 2) do
    let bounded := G.derivedSeriesWith cap
    unless bounded.certificate.check G do throw (IO.userError "bounded derived-series prefix failed replay")
    let expected := if cost ≤ cap then some s.accepted else none
    unless bounded.answer? == expected do
      throw (IO.userError "derived-series exhaustion or terminal answer violated the term cap")

private def checkNormalStructure (G H : Group n) (ambient subgroup : Array (Array Nat))
    (candidates : List (Array Nat)) : IO Unit := do
  if h : H.isSubgroup G = true then
    let c := G.normalClosureCert H ((H.isSubgroup_iff G).mp h)
    let mut conjugates := #[]
    for g in ambient do
      for p in subgroup do
        conjugates := conjugates.push (composeImages g (composeImages p (inverseImages g)))
    let expected := closure n conjugates
    unless c.group.order == expected.size && Normal.checkClosure G H c.group c.trace &&
        c.group.isSubgroup G && H.isSubgroup c.group &&
        2 ^ c.trace.length * H.order ≤ G.order do
      throw (IO.userError "normal closure order, replay, inclusion or growth bound failed")
    for raw in candidates do
      let some p := Perm.ofNatArray? n raw
        | throw (IO.userError "normal closure candidate rejected")
      unless c.group.contains p == expected.contains raw do
        throw (IO.userError "normal closure disagrees with all-element conjugation reference")
    if c.group.order < G.order && Normal.checkClosure G H G c.trace then
      throw (IO.userError "normal closure checker accepted extraneous normal elements")
    match c.trace with
    | [] => pure ()
    | s :: rest =>
      if Normal.checkClosure G H c.group c.trace.dropLast ||
          Normal.checkClosure G H c.group ({ s with conjugator := G.chain.generators.size } :: rest) ||
          Normal.checkClosure G H c.group ({ s with source := H.generators.size } :: rest) ||
          Normal.checkClosure G H c.group ({ s with chain := H.chain } :: rest) ||
          Normal.checkClosure G H c.group (s :: s :: rest) then
        throw (IO.userError "normal closure checker accepted a corrupted insertion trace")
    let k := G.coreCert H ((H.isSubgroup_iff G).mp h)
    let coreReference := subgroup.filter fun p => ambient.all fun g =>
      subgroup.contains (composeImages g (composeImages p (inverseImages g)))
    unless k.group.order == coreReference.size && Core.check G H k.group k.trace &&
        k.group.isSubgroup H && 2 ^ k.trace.length * k.group.order ≤ H.order do
      throw (IO.userError "core order, replay, inclusion or growth bound failed")
    let trivial := Group.ofGenerators (#[] : Array (Perm n))
    if k.group.order > 1 && Core.check G H trivial k.trace then
      throw (IO.userError "core checker accepted a normal subgroup omitting valid elements")
    match k.trace with
    | [] => pure ()
    | s :: rest =>
      if Core.check G H k.group k.trace.dropLast ||
          Core.check G H k.group ({ s with conjugator := G.chain.generators.size } :: rest) ||
          Core.check G H k.group ({ s with conjugate := trivial.chain } :: rest) ||
          Core.check G H k.group ({ s with group := H } :: rest) ||
          Core.check G H k.group ({ s with certificate := .leaf } :: rest) ||
          Core.check G H k.group (s :: s :: rest) then
        throw (IO.userError "core checker accepted a corrupted intersection trace")
    let index := G.index H ((H.isSubgroup_iff G).mp h)
    let .ok action := G.cosetAction H ((H.isSubgroup_iff G).mp h) index
      | throw (IO.userError "coset action rejected its exact domain cap")
    unless action.transversal.reps.size == index && action.kernel.group.sameGroup k.group &&
        action.image.group.order * k.group.order == G.order do
      throw (IO.userError "coset action domain, kernel or image order failed")
    match G.cosetAction H ((H.isSubgroup_iff G).mp h) (index - 1) with
    | .ok _ => throw (IO.userError "coset action ignored its domain cap")
    | .error limit =>
      unless limit.required == index && limit.capacity == index - 1 do
        throw (IO.userError "coset action reported the wrong domain limit")
    for raw in candidates do
      let some p := Perm.ofNatArray? n raw
        | throw (IO.userError "core candidate rejected")
      unless k.group.contains p == coreReference.contains raw &&
          action.kernel.group.contains p == coreReference.contains raw do
        throw (IO.userError "core or coset kernel disagrees with all-element conjugation reference")
  else
    throw (IO.userError "normal closure test input is not an ambient subgroup")

-- Enumerate partitions by placing the next point in an existing block or in
-- a new singleton. This reference never merges blocks or follows a group chain.
private def rawPartitions (n : Nat) : Array (Array Nat) := Id.run do
  let mut partitions : Array (Array Nat) := #[#[]]
  for i in List.range n do
    let mut next := #[]
    for labels in partitions do
      for root in labels.toList.eraseDups ++ [i] do
        next := next.push (labels.push root)
    partitions := next
  return partitions

private def checkBlockAction (G : Group n) (reference : Array (Array Nat)) (labels : Array Nat) : IO Unit := do
  let partition := Partition.ofValues (Hex.Vector.ofFn' fun i : Fin n => labels[i.val]!)
  unless partition.labels.toArray.map Fin.val == labels do
    throw (IO.userError "canonical partition constructor changed reference labels")
  if hp : partition.isInvariant G = true then
    let invariant := (partition.isInvariant_iff G).mp hp
    let roots := ((List.range n).filter fun x => labels[x]! == x).toArray
    unless partition.blocks.map (fun b => b.val.val) == roots do
      throw (IO.userError "block action did not retain canonical least-point order")
    let .ok action := G.blockAction partition invariant roots.size
      | throw (IO.userError "valid block action was rejected at its exact domain cap")
    let mut images : Array (Array Nat) := #[]
    let mut kernelSize := 0
    for g in reference do
      let induced := roots.map fun x => roots.toList.idxOf labels[g[x]!]!
      unless images.contains induced do images := images.push induced
      let fixes := (List.range n).all fun x => labels[g[x]!]! == labels[x]!
      if fixes then kernelSize := kernelSize + 1
      let some value := Perm.ofNatArray? n g
        | throw (IO.userError "independent group element failed raw permutation validation")
      let some element := Element.ofPerm? G value
        | throw (IO.userError "independent group element failed complete membership")
      unless (action.image.map element).val.vec.toArray.map Fin.val == induced &&
          action.kernel.group.contains value == fixes do
        throw (IO.userError "block action image or kernel disagrees with independent element images")
    unless action.image.group.order == images.size && action.kernel.group.order == kernelSize &&
        action.image.group.order * action.kernel.group.order == G.order do
      throw (IO.userError "block action lost its exact image/kernel order factorization")
    for x in List.finRange n do
      let size := (List.range n).countP fun y => labels[x.val]! == labels[y]!
      unless partition.blockSize x == size do
        throw (IO.userError "block cardinality disagrees with independent labels")
    if roots.size > 0 then
      match G.blockAction partition invariant (roots.size - 1) with
      | .error (.sizeLimit limit) =>
        unless limit.required == roots.size && limit.capacity == roots.size - 1 do
          throw (IO.userError "block action reported the wrong domain limit")
      | _ => throw (IO.userError "block action failed to enforce its domain cap")
  else throw (IO.userError "independently invariant partition was rejected")

private def checkBlocks (G : Group n) (reference : Array (Array Nat)) : IO Nat := do
  let points := List.finRange n
  let partitions := (rawPartitions n).filter fun labels => reference.all fun g =>
    points.all fun x => points.all fun y =>
      labels[x.val]! != labels[y.val]! || labels[g[x.val]!]! == labels[g[y.val]!]!
  for labels in partitions do checkBlockAction G reference labels
  let transitive := n >= 2 && points.all fun b => reference.any fun g => g[0]! == b.val
  let primitive := transitive && partitions.all fun labels =>
    labels == (List.range n).toArray || labels == (List.replicate n 0).toArray
  let verdict := G.primitivity
  unless verdict.accepted == primitive do
    throw (IO.userError "primitivity disagrees with exhaustive invariant partitions")
  match verdict with
  | .small _ =>
    unless n < 2 do throw (IO.userError "spurious small-degree primitivity obstruction")
  | .intransitive a b _ =>
    unless reference.all (fun g => g[a.val]! != b.val) do
      throw (IO.userError "intransitivity obstruction has an independent transporter")
  | .imprimitive a failure =>
    let labels := failure.solution.partition.labels.toArray.map Fin.val
    unless partitions.contains labels && labels != (List.range n).toArray &&
        labels != (List.replicate n 0).toArray &&
        Blocks.check G.chain.generators [(a, failure.point)] failure.solution.partition failure.solution.trace do
      throw (IO.userError "imprimitivity witness is trivial, not invariant, or failed replay")
  | .primitive _ _ a checks =>
    unless Primitivity.check G a checks.traces do
      throw (IO.userError "complete primitivity traces failed independent replay")
  let edges := (points.flatMap fun x => (points.filter (x < ·)).map fun y => (x, y)).toArray
  for mask in List.range (2 ^ edges.size) do
    let seeds := ((List.finRange edges.size).filter fun i => mask / 2 ^ i.val % 2 = 1).map
      fun i => edges[i.val]
    let admitted := partitions.filter fun labels => seeds.all fun (x, y) => labels[x.val]! == labels[y.val]!
    let solution := G.blocksCert seeds
    unless Blocks.check G.chain.generators seeds solution.partition solution.trace &&
        solution.trace.length <= n - 1 && !admitted.isEmpty do
      throw (IO.userError "block-system certificate or effective-union bound failed")
    let labels := solution.partition.labels.toArray.map Fin.val
    for x in points do
      for y in points do
        let expected := admitted.all fun q => q[x.val]! == q[y.val]!
        unless (labels[x.val]! == labels[y.val]!) == expected do
          throw (IO.userError s!"minimal block system disagrees with partition reference: degree {n}, seeds {seeds.map fun q => (q.1.val, q.2.val)}, labels {labels}")
  return 2 ^ edges.size

private def searchBudget : Search.Budget :=
  { nodes := 100000, refinements := 1000000, sifts := 1000000, certificates := 100000 }

private def checkBudget {G : Group n} {P : Search.Predicate n} (C : Search.Constraint G P)
    (budget : Search.Budget) (answer : Search.Outcome C budget) (expected : Group n) : IO Search.Work := do
  match answer with
  | .incomplete _ _ => throw (IO.userError "subgroup search exhausted a generous budget")
  | .complete result meter =>
    unless Search.checkSearch C result.group result.certificate && result.group.sameGroup expected do
      throw (IO.userError "budgeted subgroup search changed its exact result or failed certificate replay")
    unless meter.used.certificates == result.certificate.nodes && meter.used.nodes == result.certificate.nodes do
      throw (IO.userError "completed search miscounted visited or certificate nodes")
    for resource in [Search.Resource.nodes, .refinements, .sifts, .certificates] do
      unless meter.used.get resource <= budget.get resource do
        throw (IO.userError "completed search exceeded a resource allowance")
    return meter.used

private def checkAnswerBudget {G : Group n} {test : Perm n → Bool} (C : Search.Pruner G test)
    (budget : Search.Budget) (answer : Search.AnswerOutcome C budget) (expected : Array (Array Nat)) :
    IO (Search.Work × Nat) := do
  match answer with
  | .incomplete _ => throw (IO.userError "transporter search exhausted a generous budget")
  | .complete result meter =>
    for resource in [Search.Resource.nodes, .refinements, .sifts, .certificates] do
      unless meter.used.get resource <= budget.get resource do
        throw (IO.userError "completed transporter search exceeded a resource allowance")
    match result with
    | .found witness =>
      unless Search.checkWitness G test witness.value witness.word &&
          expected.contains (witness.value.vec.toArray.map Fin.val) &&
          witness.word.nodes.size <= meter.used.certificates do
        throw (IO.userError "budgeted transporter witness changed its result or escaped certificate accounting")
      return (meter.used, witness.word.nodes.size)
    | .absent certificate _ =>
      unless expected.isEmpty && Search.checkFailure C (Search.Node.root G) certificate &&
          meter.used.nodes == certificate.nodes && meter.used.certificates == certificate.nodes do
        throw (IO.userError "budgeted negative transporter lost completeness or miscounted certificate nodes")
      return (meter.used, 0)

example : checkChain (#[] : Array (Perm 0)) (Group.ofGenerators #[]).chain = true :=
  Group.ofGenerators_checks _
example : (Group.ofGenerators generators).contains cycle = true :=
  (Group.contains_ofGenerators generators cycle).mpr (.generator (by simp [generators]))

#eval do
  let mut count := 0
  let mut blockCases := 0
  for n in List.range 5 do
    let raws := (permutations (List.range n)).map List.toArray
    for left in raws do
      for right in raws do
        let some p := Perm.ofNatArray? n left
          | throw (IO.userError "left generator rejected")
        let some q := Perm.ofNatArray? n right
          | throw (IO.userError "right generator rejected")
        let input := #[Perm.id n, p, q, p]
        let group := Group.ofGenerators input
        let reference := closure n #[left, right]
        checkDerivedSeries group reference raws
        blockCases := blockCases + (← checkBlocks group reference)
        unless group.generators = input do
          throw (IO.userError "group construction changed the original input array")
        unless group.order == reference.size do
          throw (IO.userError s!"group order mismatch: {left}, {right}, got {group.order}, expected {reference.size}")
        unless checkChain input group.chain do
          throw (IO.userError s!"constructed chain failed replay: {left}, {right}")
        let .ok naturalImage := (Action.natural group).actionImage n (List.finRange n).toArray
          | throw (IO.userError "natural action domain was rejected")
        unless naturalImage.group.order == group.order do
          throw (IO.userError "natural action image changed the group order")
        for i in List.finRange naturalImage.group.generators.size do
          unless checkWord input (naturalImage.preimage i).val (naturalImage.preimageWord i) &&
              (naturalImage.map (naturalImage.preimage i)).val == naturalImage.group.generators[i.val] do
            throw (IO.userError "image generator lost its checked preimage")
        let mut ranked : Array (Array Nat) := #[]
        for k in List.finRange group.order do
          let element := group.unrank k
          let raw := element.val.vec.toArray.map Fin.val
          unless (naturalImage.map element).val.vec.toArray.map Fin.val == raw do
            throw (IO.userError "natural action used the wrong index permutation")
          unless reference.contains raw && group.rank element == k do
            throw (IO.userError "unrank/rank failed to recover its in-range index")
          if ranked.contains raw then throw (IO.userError "unranking produced a duplicate element")
          ranked := ranked.push raw
        unless ranked.size == reference.size && (group.unrank? group.order).isNone &&
            (group.unrank? (group.order + 1)).isNone do
          throw (IO.userError "unrank coverage or raw-index bounds failed")
        let .ok listed := group.elementsWith group.order
          | throw (IO.userError "enumeration rejected a sufficient allocation cap")
        unless listed.size == reference.size &&
            decide (listed.toList.Pairwise fun (p q : Element group) => Chain.before p.val q.val) do
          throw (IO.userError "enumeration has the wrong size or is not strictly sorted")
        for element in listed do
          unless reference.contains ((element : Element group).val.vec.toArray.map Fin.val) do
            throw (IO.userError "enumeration escaped the generated subgroup")
        match group.elementsWith (group.order - 1) with
        | .ok _ => throw (IO.userError "enumeration ignored its allocation cap")
        | .error limit =>
          unless limit.required == group.order && limit.capacity == group.order - 1 do
            throw (IO.userError "enumeration reported incorrect size-limit information")
        for raw in raws do
          let some candidate := Perm.ofNatArray? n raw
            | throw (IO.userError "candidate permutation rejected")
          unless group.contains candidate == reference.contains raw do
            throw (IO.userError s!"membership mismatch: {left}, {right}, candidate {raw}")
          match group.word? candidate with
          | none =>
            if reference.contains raw then throw (IO.userError "membership program rejected a group element")
          | some word =>
            unless reference.contains raw && checkWord input candidate word do
              throw (IO.userError "membership program failed independent replay in the original generators")
          match group.rank? candidate with
          | none =>
            if reference.contains raw then throw (IO.userError "ranking rejected a group element")
          | some k =>
            unless (group.unrank k).val = candidate do
              throw (IO.userError "rank/unrank failed to recover its input permutation")
        let cyclic := Group.ofGenerators #[p]
        let cyclicReference := closure n #[left]
        checkNormalStructure group cyclic reference cyclicReference raws
        let constraint := Search.Constraint.none group (Search.Predicate.subgroup cyclic)
        let found := Search.solve constraint
        unless Search.checkSearch constraint found.group found.certificate && found.group.sameGroup cyclic do
          throw (IO.userError "complete subgroup search disagrees with independent cyclic closure")
        match found.certificate with
        | .branch children =>
          if Search.checkSearch constraint found.group (.branch children.pop) ||
              Search.checkSearch constraint found.group (.branch (children.push .covered)) ||
              Search.checkSearch constraint found.group .leaf then
            throw (IO.userError "search checker accepted a missing/extra child or a premature leaf")
        | _ => pure ()
        let centralConstraint := Search.Centralizer.constraint group cyclic
        let central := group.centralizerSearch cyclic
        unless Search.checkSearch centralConstraint central.group central.certificate do
          throw (IO.userError "centralizer certificate failed independent replay")
        let _ ← checkBudget centralConstraint searchBudget (group.centralizerWith searchBudget cyclic) central.group
        for raw in raws do
          let some candidate := Perm.ofNatArray? n raw
            | throw (IO.userError "centralizer reference permutation rejected")
          let expected := reference.contains raw && cyclicReference.all fun h => composeImages raw h == composeImages h raw
          unless central.group.contains candidate == expected do
            throw (IO.userError "centralizer search disagrees with independent closure")
        let other := Group.ofGenerators #[q]
        let otherReference := closure n #[right]
        let intersection := cyclic.intersectionSearch other
        unless Search.checkSearch (Search.Intersection.constraint cyclic other)
            intersection.group intersection.certificate do
          throw (IO.userError "intersection certificate failed independent replay")
        let _ ← checkBudget (Search.Intersection.constraint cyclic other) searchBudget
          (cyclic.intersectionWith searchBudget other) intersection.group
        for raw in raws do
          let some candidate := Perm.ofNatArray? n raw
            | throw (IO.userError "intersection reference permutation rejected")
          unless intersection.group.contains candidate ==
              (cyclicReference.contains raw && otherReference.contains raw) do
            throw (IO.userError "intersection search disagrees with independent closure")
        let normalizer := group.normalizerSearch other
        unless Search.checkSearch (Search.Normalizer.constraint group other)
            normalizer.group normalizer.certificate do
          throw (IO.userError "normalizer certificate failed independent replay")
        let _ ← checkBudget (Search.Normalizer.constraint group other) searchBudget
          (group.normalizerWith searchBudget other) normalizer.group
        for raw in raws do
          let some candidate := Perm.ofNatArray? n raw
            | throw (IO.userError "normalizer reference permutation rejected")
          let expected := reference.contains raw && otherReference.all fun h =>
            otherReference.contains (composeImages raw (composeImages h (inverseImages raw)))
          unless normalizer.group.contains candidate == expected do
            throw (IO.userError "normalizer search disagrees with independent conjugation closure")
        for mask in List.range (2 ^ n) do
          let subset : Vector Bool n := Hex.Vector.ofFn' fun x => decide (mask / 2 ^ x.val % 2 = 1)
          let stabilizer := group.setStabilizerSearch subset
          unless Search.checkSearch (Search.Sets.constraint group subset)
              stabilizer.group stabilizer.certificate do
            throw (IO.userError "set stabilizer certificate failed independent replay")
          let _ ← checkBudget (Search.Sets.constraint group subset) searchBudget
            (group.setStabilizerWith searchBudget subset) stabilizer.group
          for raw in raws do
            let some candidate := Perm.ofNatArray? n raw
              | throw (IO.userError "set stabilizer reference permutation rejected")
            let expected := reference.contains raw && (List.range n).all fun i =>
              mask / 2 ^ i % 2 == mask / 2 ^ raw[i]! % 2
            unless stabilizer.group.contains candidate == expected do
              throw (IO.userError "set stabilizer search disagrees with independent subset images")
          for targetMask in List.range (2 ^ n) do
            let target : Vector Bool n := Hex.Vector.ofFn' fun x => decide (targetMask / 2 ^ x.val % 2 = 1)
            let expected := reference.filter fun raw => (List.range n).all fun i =>
              mask / 2 ^ i % 2 == targetMask / 2 ^ raw[i]! % 2
            let constraint := Search.Sets.transporter group subset target
            let _ ← checkAnswerBudget constraint searchBudget
              (group.setTransporterWith searchBudget subset target) expected
            match group.setTransporterSearch subset target with
            | .found witness =>
              unless Search.checkWitness group (Search.Sets.test subset target) witness.value witness.word &&
                  expected.contains (witness.value.vec.toArray.map Fin.val) do
                throw (IO.userError "set transporter word or subset image disagrees with independent closure")
            | .absent certificate _ =>
              unless expected.isEmpty && Search.checkFailure constraint (Search.Node.root group) certificate do
                throw (IO.userError "negative set transporter certificate disagrees with independent closure")
              match certificate with
              | .branch children =>
                if Search.checkFailure constraint (Search.Node.root group) (.branch children.pop) ||
                    Search.checkFailure constraint (Search.Node.root group) (.branch (children.push .leaf)) then
                  throw (IO.userError "negative transporter checker accepted missing or extra branches")
              | _ => pure ()
        unless cyclic.isSubgroup group &&
            group.isSubgroup cyclic == (reference.size == cyclicReference.size) do
          throw (IO.userError "subgroup containment disagrees with closure")
        unless (group.subgroupFailure? cyclic).isNone == group.isSubgroup cyclic do
          throw (IO.userError "containment failure certificate disagrees with decision")
        match cyclic.subgroupWords? group with
        | none => throw (IO.userError "positive containment certificate was rejected")
        | some words =>
          unless checkWords group.generators cyclic.generators words do
            throw (IO.userError "positive containment certificate failed replay")
        unless (group.subgroupWords? cyclic).isSome == group.isSubgroup cyclic do
          throw (IO.userError "containment certificate availability disagrees with decision")
        let abelian := reference.all fun p => reference.all fun q => composeImages p q == composeImages q p
        unless group.isAbelian == abelian && group.abelianFailure?.isNone == abelian do
          throw (IO.userError "abelianness or its failure certificate disagrees with closure")
        let transitive := n > 0 && (List.range n).all fun i => reference.any fun p => p[0]! == i
        unless group.isTransitive == transitive do
          throw (IO.userError "transitivity disagrees with the declared action domain")
        if hc : cyclic.isSubgroup group = true then
          let normal := reference.all fun p => cyclicReference.all fun q =>
            cyclicReference.contains (composeImages p (composeImages q (inverseImages p)))
          unless cyclic.isNormal group ((Group.isSubgroup_iff _ _).mp hc) == normal &&
              (cyclic.normalFailure? group).isNone == normal do
            throw (IO.userError "normality or its failure certificate disagrees with closure")
          let inclusion := (Group.isSubgroup_iff _ _).mp hc
          let expectedIndex := reference.size / cyclicReference.size
          let .ok left := group.leftCosetsWith expectedIndex cyclic inclusion
            | throw (IO.userError "left cosets rejected a sufficient exact cap")
          unless left.reps.size == expectedIndex && group.index cyclic inclusion == expectedIndex do
            throw (IO.userError "left coset count differs from independent closure cardinalities")
          let mut leftSeen : Array (Array Nat) := #[]
          for i in List.finRange left.reps.size do
            let i : Fin left.reps.size := i
            let rep := left.reps[i.val].val.vec.toArray.map Fin.val
            unless checkWord input left.reps[i.val].val left.words[i.val] do
              throw (IO.userError "left representative program failed replay")
            for h in cyclicReference do
              let value := composeImages rep h
              unless reference.contains value && !leftSeen.contains value do
                throw (IO.userError "left cosets overlap or escape the original group")
              leftSeen := leftSeen.push value
          unless leftSeen.size == reference.size do
            throw (IO.userError "left cosets do not cover the original group")
          let right := left.inverse
          let mut rightSeen : Array (Array Nat) := #[]
          for i in List.finRange right.reps.size do
            let i : Fin right.reps.size := i
            let rep := right.reps[i.val].val.vec.toArray.map Fin.val
            unless checkWord input right.reps[i.val].val right.words[i.val] do
              throw (IO.userError "inverted representative program failed replay")
            for h in cyclicReference do
              let value := composeImages h rep
              unless reference.contains value && !rightSeen.contains value do
                throw (IO.userError "inverted transversal has overlapping or escaping right cosets")
              rightSeen := rightSeen.push value
          unless rightSeen.size == reference.size do
            throw (IO.userError "inverted right cosets do not cover the original group")
          match group.leftCosetsWith (expectedIndex - 1) cyclic inclusion with
          | .ok _ => throw (IO.userError "left cosets ignored an insufficient cap")
          | .error limit =>
            unless limit.required == expectedIndex && limit.capacity == expectedIndex - 1 do
              throw (IO.userError "left cosets reported incorrect size-limit information")
        else throw (IO.userError "cyclic generator subgroup unexpectedly not contained")
        let joined := cyclic.join (Group.ofGenerators #[q])
        unless joined.sameGroup group do
          throw (IO.userError "join changed the generated subgroup")
        let mut expectedOrbits : Array (Array Nat) := #[]
        let mut visited : Array Nat := #[]
        for a in List.range n do
          unless visited.contains a do
            let points := ((List.range n).filter fun b => reference.any fun raw => raw[a]! == b).toArray
            expectedOrbits := expectedOrbits.push points
            visited := visited ++ points
        unless (group.orbits.map fun points => (points : Array (Fin n)).map Fin.val) == expectedOrbits do
          throw (IO.userError "orbit partition is incomplete, overlapping, or unsorted")
        for a in List.finRange n do
          let orbit := group.orbit a
          let expectedOrbit := ((List.range n).filter fun x =>
            reference.any fun raw => raw[a.val]! == x).toArray
          unless orbit.map Fin.val == expectedOrbit do
            throw (IO.userError "point orbit disagrees with closure or is unsorted")
          let .ok actionOrbit := (Action.natural group).breadthFirst a expectedOrbit.size
            | throw (IO.userError "generic orbit BFS rejected an exact object budget")
          unless Action.checkOrbit (Action.natural group) a actionOrbit.val &&
              actionOrbit.val.objects.size == expectedOrbit.size do
            throw (IO.userError "generic orbit certificate failed replay or has the wrong size")
          for b in List.finRange n do
            unless actionOrbit.val.objects.contains b == expectedOrbit.contains b.val do
              throw (IO.userError "generic orbit differs from independent closure")
          let stabilizer := group.stabilizer a
          let expected := reference.filter fun raw => raw[a.val]! == a.val
          unless stabilizer.order == expected.size && stabilizer.isSubgroup group do
            throw (IO.userError "point stabilizer has the wrong order or escapes the group")
          for raw in raws do
            let some candidate := Perm.ofNatArray? n raw
              | throw (IO.userError "stabilizer candidate rejected")
            unless stabilizer.contains candidate == expected.contains raw do
              throw (IO.userError "point stabilizer disagrees with closure")
          for b in List.finRange n do
            match group.transporter? a b with
            | none =>
              if expectedOrbit.contains b.val then
                throw (IO.userError "transporter missed an orbit point")
            | some t =>
              unless t.val.get a == b && group.contains t.val do
                throw (IO.userError "transporter has wrong image or membership")
        count := count + 1
  unless count == 618 do throw (IO.userError s!"unexpected small-group case count: {count}")
  unless blockCases == 37162 do throw (IO.userError s!"unexpected block-system case count: {blockCases}")
  let empty := Group.ofGenerators (#[] : Array (Perm 5))
  unless empty.order == 1 && empty.chain.length == 5 && checkChain #[] empty.chain do
    throw (IO.userError "empty generator array failed to produce a complete trivial chain")
  let s3 := Group.ofGenerators generators
  unless s3.order == 6 && s3.contains swap12 do
    throw (IO.userError "S3 construction missed its nontrivial point stabilizer")
  let samples : List (Element s3) := Group.sampleWith (fun bound _ => List.finRange bound) s3
  unless samples.map (fun p => (s3.rank p).val) == List.range s3.order do
    throw (IO.userError "supplied-index sampling failed exhaustive bijectivity")
  let failed : Except String (Element s3) := Group.sampleWith (fun _ _ => Except.error "source failed") s3
  match failed with
  | .error "source failed" => pure ()
  | _ => throw (IO.userError "sampling did not preserve source failure")
  let draw : (bound : Nat) → 0 < bound → StateM Nat (Fin bound) := fun bound hb => do
    modify (· + 1)
    pure ⟨bound - 1, by omega⟩
  let (sample, calls) := (Group.sampleWith draw s3).run 0
  unless calls == 1 && (s3.rank sample).val == s3.order - 1 do
    throw (IO.userError "sampling did not use exactly one supplied index")
  unless (s3.pointwise [0, 0]).sameGroup (s3.stabilizer 0) &&
      (s3.pointwise [0, 1, 0]).order == 1 do
    throw (IO.userError "pointwise stabilizer mishandled repeated points")
  let c2 := Group.ofGenerators #[swap]
  let conjugated := Group.conjugate cycle c2
  unless conjugated.order == 2 && conjugated.contains swap12 && !conjugated.sameGroup c2 do
    throw (IO.userError "conjugation used the wrong multiplication order")
  if hc : c2.isSubgroup s3 = true then
    let .ok cosets := s3.leftCosetsWith 3 c2 ((Group.isSubgroup_iff _ _).mp hc)
      | throw (IO.userError "S3 left transversal was rejected")
    unless cosets.reps.map (fun p => (p : Element s3).val) == #[Perm.id 3, cycle, cycle.inv] do
      throw (IO.userError "S3 coset BFS discovery order changed")
    let left := #[cycle, cycle.comp swap]
    let right := #[cycle, swap.comp cycle]
    unless left != right && decide (LeftCoset.mk c2 cycle = LeftCoset.mk c2 (cycle.comp swap)) &&
        !decide (LeftCoset.mk c2 cycle = LeftCoset.mk c2 (swap.comp cycle)) do
      throw (IO.userError "coset equality confused left and right multiplication")
  else throw (IO.userError "S3 does not contain its supplied transposition")
  let profile := Build.build 0 (by decide) generators (by intro _ x h; omega)
  unless profile.rebuilds == 1 do
    throw (IO.userError s!"S3 expected one strict suffix insertion, got {profile.rebuilds}")
  for n in [5, 6, 7] do
    let some rotation := Perm.ofNatArray? n ((List.range n).map fun i => (i + 1) % n).toArray
      | throw (IO.userError "rotation rejected")
    let some adjacent := Perm.ofNatArray? n
        ((List.range n).map fun i => if i = 0 then 1 else if i = 1 then 0 else i).toArray
      | throw (IO.userError "transposition rejected")
    let input := #[rotation, adjacent]
    let group := Group.ofGenerators input
    let expected := (List.range n).foldl (fun product i => product * (i + 1)) 1
    unless group.order == expected && checkChain input group.chain do
      throw (IO.userError s!"symmetric group construction failed at degree {n}")
  let redundant := (List.replicate 2048 cycle).toArray.push (Perm.id 3)
  let normalized := normalize redundant
  unless normalized.generators = #[cycle, cycle.inv] &&
      checkWords redundant normalized.generators normalized.words do
    throw (IO.userError "normalization of heavily redundant input failed")

#eval do
  let group := Group.ofGenerators generators
  let repeated : Array (Vector (Fin 3) 2) := #[#v[2, 2], #v[0, 0], #v[1, 1]]
  let .ok tuples := (Action.tuples group 2).actionImage 3 repeated
    | throw (IO.userError "tuple action rejected repeated entries")
  unless tuples.group.order == 6 do
    throw (IO.userError "tuple action lost the diagonal orbit")
  for i in List.finRange tuples.group.generators.size do
    let p := tuples.preimage i
    for j in List.finRange repeated.size do
      let k := (tuples.map p).val.get j
      unless repeated[k.val] == repeated[j.val].map p.val.get do
        throw (IO.userError "tuple image did not respect the recorded domain order")
  let subsets := Action.subsets group
  let singles : Array (Vector Bool 3) :=
    #[#v[false, false, true], #v[true, false, false], #v[false, true, false]]
  let .ok image := subsets.actionImage 3 singles
    | throw (IO.userError "subset action rejected a complete invariant domain")
  unless image.group.order == 6 do
    throw (IO.userError "subset action has the wrong image")
  for i in List.finRange image.group.generators.size do
    let p := image.preimage i
    for j in List.finRange singles.size do
      let target := singles[(image.map p).val.get j |>.val]
      for x in List.finRange 3 do
        unless target[(p.val.get x).val] == singles[j.val][x.val] do
          throw (IO.userError "subset action reversed the left-action convention")
  let fixed : Array (Vector Bool 3) := #[#v[false, false, false], #v[true, true, true]]
  let .ok trivial := subsets.actionImage 2 fixed
    | throw (IO.userError "empty and full subsets were rejected")
  unless trivial.group.order == 1 do
    throw (IO.userError "nonfaithful subset action was treated as faithful")
  let .ok empty := subsets.actionImage 0 #[]
    | throw (IO.userError "empty action domain was rejected")
  unless empty.group.order == 1 do
    throw (IO.userError "empty-domain image is not trivial")
  match subsets.actionImage 2 singles with
  | .error (.sizeLimit limit) =>
    unless limit.required == 3 && limit.capacity == 2 do
      throw (IO.userError "action image reported the wrong allocation bound")
  | _ => throw (IO.userError "action image ignored its domain cap")
  match subsets.actionImage 2 #[#v[true, false, false], #v[true, false, false]] with
  | .error .invalidDomain => pure ()
  | _ => throw (IO.userError "action image accepted duplicate domain objects")
  match subsets.actionImage 1 #[#v[true, false, false]] with
  | .error .invalidDomain => pure ()
  | _ => throw (IO.userError "action image accepted a domain not closed under generators")
  let some swap01 := Perm.ofNatArray? 4 #[1, 0, 2, 3]
    | throw (IO.userError "first disjoint transposition rejected")
  let some swap23 := Perm.ofNatArray? 4 #[0, 1, 3, 2]
    | throw (IO.userError "second disjoint transposition rejected")
  let klein := Group.ofGenerators #[swap01, swap23]
  let .ok orbitImage := (Action.natural klein).actionImage 2 #[0, 1]
    | throw (IO.userError "nonfaithful point action was rejected")
  let mut kernelCount := 0
  for p in klein.enumerate do
    if (orbitImage.map p).val == Perm.id 2 then kernelCount := kernelCount + 1
  unless klein.order == 4 && orbitImage.group.order == 2 && kernelCount == 2 do
    throw (IO.userError "proper action kernel or image order is wrong")

private def checkAction {G : Group n} {α : Type} [DecidableEq α]
    (a : Action G α) (base : α) (probes : Array α) : IO Unit := do
  let elements := G.enumerate
  let mut expected : Array α := #[]
  for p in elements do
    let y := a.act p base
    unless expected.contains y do expected := expected.push y
  let .ok result := a.breadthFirst base expected.size
    | throw (IO.userError "action orbit rejected a sufficient exact budget")
  let orbit := result.val
  let valid := result.property.1
  unless Action.checkOrbit a base orbit && orbit.objects.size == expected.size do
    throw (IO.userError "action orbit failed independent certificate replay")
  let malformed : Program := ⟨#[.comp 0 0], 0⟩
  let corrupted := { orbit with words := Vector.replicate orbit.objects.size malformed }
  if Action.checkOrbit a base corrupted then
    throw (IO.userError "action orbit checker accepted a malformed membership program")
  unless Action.checkOrbit a base (Action.Queue.root a base).orbit == (expected.size == 1) do
    throw (IO.userError "action orbit checker confused reachability with complete closure")
  for y in probes ++ expected do
    unless orbit.objects.contains y == expected.contains y do
      throw (IO.userError "action orbit disagrees with exhaustive action images")
    match Action.Orbit.transporter? valid y with
    | none =>
      if expected.contains y then throw (IO.userError "action transporter rejected a reachable object")
    | some p =>
      unless a.act p base == y do throw (IO.userError "action transporter has the wrong image")
  for i in List.finRange orbit.objects.size do
    unless orbit.words[i.val].nodes.size ≤ 3 * expected.size &&
        checkWord G.generators orbit.reps[i.val].val orbit.words[i.val] do
      throw (IO.userError "action transporter word lost sharing or failed replay")
    for j in List.finRange G.generators.size do
      let p : Element G := ⟨G.generators[j.val], .generator (Array.getElem_mem j.isLt)⟩
      unless checkWord G.generators (Action.Orbit.schreier valid p i).val
          (Action.Orbit.schreierWord valid j i) do
        throw (IO.userError "action Schreier generator word failed replay")
  let stabilizer := Action.Orbit.stabilizer valid
  let mut fixedCount := 0
  for p in elements do
    let fixed := decide (a.act p base = base)
    if fixed then fixedCount := fixedCount + 1
    unless stabilizer.contains p.val == fixed do
      throw (IO.userError "action stabilizer missed an element or included a non-fixer")
  unless stabilizer.order == fixedCount && stabilizer.isSubgroup G do
    throw (IO.userError "action stabilizer has the wrong order or escapes the original group")
  match a.breadthFirst base (expected.size - 1) with
  | .ok _ => throw (IO.userError "orbit BFS ignored an insufficient budget")
  | .error (.zero _) =>
    unless expected.size == 1 do throw (IO.userError "non-singleton orbit reported zero capacity")
  | .error (.full e) =>
    unless e.queue.objects.size == expected.size - 1 do
      throw (IO.userError "orbit BFS stopped before filling its object budget")
    for y in e.queue.objects do
      unless expected.contains y do throw (IO.userError "incomplete orbit contains an unreachable object")
  let .ok larger := a.breadthFirst base (expected.size + 5)
    | throw (IO.userError "orbit BFS rejected a larger sufficient budget")
  unless larger.val.objects == orbit.objects do
    throw (IO.userError "orbit discovery order depends on unused capacity")
  let .ok kernel := a.actionKernel expected.size orbit.objects
    | throw (IO.userError "action kernel rejected a complete orbit domain")
  let .ok image := a.actionImage expected.size orbit.objects
    | throw (IO.userError "action image rejected its own complete orbit domain")
  let mut kernelCount := 0
  for p in elements do
    let fixesDomain := orbit.objects.all fun y => decide (a.act p y = y)
    if fixesDomain then kernelCount := kernelCount + 1
    unless kernel.group.contains p.val == fixesDomain do
      throw (IO.userError "computed action kernel has incorrect membership")
  unless kernel.group.order == kernelCount && kernel.group.isSubgroup G &&
      kernel.group.order * image.group.order == G.order do
    throw (IO.userError "computed action kernel/image order factorization failed")
  let .ok reordered := a.actionKernel expected.size orbit.objects.reverse
    | throw (IO.userError "kernel rejected a reordered invariant domain")
  unless reordered.group.sameGroup kernel.group do
    throw (IO.userError "kernel membership depends on domain enumeration order")
  let .ok empty := a.actionKernel 0 #[]
    | throw (IO.userError "kernel rejected an empty domain")
  unless empty.group.sameGroup G do
    throw (IO.userError "empty-domain kernel is not the original group")
  match a.actionKernel (expected.size - 1) orbit.objects with
  | .error (.sizeLimit limit) =>
    unless limit.required == expected.size do
      throw (IO.userError "kernel reported the wrong domain allocation requirement")
  | _ => throw (IO.userError "kernel ignored its domain budget")
  match a.actionKernel 2 #[base, base] with
  | .error .invalidDomain => pure ()
  | _ => throw (IO.userError "kernel accepted duplicate domain objects")
  if expected.size > 1 then
    match a.actionKernel 1 #[base] with
    | .error .invalidDomain => pure ()
    | _ => throw (IO.userError "kernel accepted a non-invariant domain")

example : (Partition.ofValues (#v[] : Vector Nat 0)).labels = #v[] := by decide +kernel
example : (Partition.ofLabels? #v[(0 : Fin 2), 0]).isSome = true := by decide +kernel
example : (Partition.ofLabels? #v[(1 : Fin 2), 1]).isSome = false := by decide +kernel

#eval do
  let some rotation := Perm.ofNatArray? 4 #[1, 2, 3, 0]
    | throw (IO.userError "partition-action rotation rejected")
  let some swap01 := Perm.ofNatArray? 4 #[1, 0, 2, 3]
    | throw (IO.userError "partition-action transposition rejected")
  let group := Group.ofGenerators #[rotation, swap01]
  let p := Partition.ofValues (#v[17, 17, 9, 9] : Vector Nat 4)
  let q := Partition.ofValues (#v[3, 8, 3, 8] : Vector Nat 4)
  let r := Partition.ofValues (#v[5, 1, 1, 5] : Vector Nat 4)
  unless p.labels.toArray.map Fin.val == #[0, 0, 2, 2] &&
      p == Partition.ofValues (#v[9, 9, 17, 17] : Vector Nat 4) do
    throw (IO.userError "partition normalization retained arbitrary block names")
  let domain := #[p, q, r]
  let .ok image := (Action.partitions group).actionImage 3 domain
    | throw (IO.userError "unordered partition domain was rejected")
  let mut kernelCount := 0
  for element in group.enumerate do
    if (image.map element).val == Perm.id 3 then kernelCount := kernelCount + 1
    for part in domain do
      let moved := (Action.partitions group).act element part
      for x in List.finRange 4 do
        for y in List.finRange 4 do
          unless decide (moved.Same (element.val.get x) (element.val.get y)) == decide (part.Same x y) do
            throw (IO.userError "partition action changed the transported equivalence relation")
  unless group.order == 24 && image.group.order == 6 && kernelCount == 4 do
    throw (IO.userError "S4 action on pair partitions has the wrong image or kernel")
  let some raw := Perm.ofNatArray? 4 #[2, 3, 0, 1]
    | throw (IO.userError "block exchange rejected")
  let some exchange := Element.ofPerm? group raw
    | throw (IO.userError "block exchange was absent from S4")
  let ordered : Vector (Vector Bool 4) 2 := #v[#v[true, true, false, false], #v[false, false, true, true]]
  unless (Action.partitions group).act exchange p == p &&
      ((Action.subsets group).vectors 2).act exchange ordered != ordered do
    throw (IO.userError "unordered partitions were confused with ordered tuples of subsets")
  checkAction (Action.partitions group) p #[p, q, r]
  checkAction ((Action.subsets group).vectors 2) ordered #[ordered]
  let small := Group.ofGenerators generators
  checkAction (Action.tuples small 64) (Vector.replicate 64 0)
    #[(Vector.replicate 64 0), (Vector.replicate 64 1), (Vector.replicate 64 2)]
  checkAction (Action.tuples small 2) #v[0, 1] #[#v[0, 0], #v[1, 1], #v[2, 2], #v[1, 0]]
  checkAction (Action.subsets small) #v[true, false, true]
    #[#v[false, false, false], #v[true, true, true]]
  checkAction (Action.subsets small) #v[false, false, false] #[#v[true, true, true]]
  let trivial := Group.ofGenerators (#[] : Array (Perm 0))
  checkAction (Action.partitions trivial) (Partition.ofValues (#v[] : Vector Nat 0)) #[]

#eval do
  let some rotation := Perm.ofNatArray? 64 ((List.range 64).map fun i => (i + 1) % 64).toArray
    | throw (IO.userError "long action-orbit rotation rejected")
  let group := Group.ofGenerators #[rotation]
  let action := Action.tuples group 64
  let base : Vector (Fin 64) 64 := Vector.replicate 64 0
  let .ok result := action.breadthFirst base 64
    | throw (IO.userError "long tuple orbit exhausted a sufficient budget")
  let orbit := result.val
  unless orbit.objects.size == 64 do
    throw (IO.userError "long tuple orbit has the wrong size")
  if hs : 2 < orbit.objects.size then
    unless orbit.objects[0][0].val == 0 && orbit.objects[1][0].val == 1 &&
        orbit.objects[2][0].val == 63 do
      throw (IO.userError "signed generator BFS order changed")
    let shared := orbit.words[0].nodes
    unless shared.size == 158 do
      throw (IO.userError "long transporter paths expanded instead of sharing nodes")
    for word in orbit.words.toArray do
      unless (word : Program).nodes == shared do
        throw (IO.userError "action orbit certificates do not share one arena")
    unless checkWord group.generators orbit.reps[0].val orbit.words[0] do
      throw (IO.userError "long shared action program failed independent replay")
  else throw (IO.userError "long tuple orbit is unexpectedly empty")

-- A checked chain for 65 disjoint transpositions has order 2^65. Supplying the
-- certificate directly isolates large-index arithmetic from the recursive
-- rebuild algorithm's cost on this family; the independent checker still
-- establishes membership and exact order before any rank operation is exposed.
#eval do
  let mut input : Array (Perm 130) := #[]
  for k in (List.range 65).reverse do
    let raw := ((List.range 130).map fun i =>
      if i = 2 * k then i + 1 else if i = 2 * k + 1 then i - 1 else i).toArray
    let some p := Perm.ofNatArray? 130 raw
      | throw (IO.userError "disjoint transposition rejected")
    input := input.push p
  let mut chain : Chain 130 := .leaf #[] #v[]
  for base in (List.range 130).reverse do
    if hb : base < 130 then
      let a : Fin 130 := ⟨base, hb⟩
      let generators := input.extract 0 (65 - (base + 1) / 2)
      let words : Vector Program generators.size :=
        Hex.Vector.ofFn' fun i => ⟨#[.generator i.val], 0⟩
      let mut orbit := singleton a
      if base % 2 = 0 then
        if hn : base + 1 < 130 then
          let b : Fin 130 := ⟨base + 1, hn⟩
          let some swap := generators.back?
            | throw (IO.userError "missing transposition in the large-order chain")
          orbit :=
            { points := #[a, b]
              lookup := Hex.Vector.ofFn' fun x => if x = a then some 0 else if x = b then some 1 else none
              reps := #v[Perm.id 130, swap]
              words := #v[⟨#[.id], 0⟩, ⟨#[.generator (generators.size - 1)], 0⟩] }
        else throw (IO.userError "large-order orbit endpoint is out of bounds")
      chain := .cons ⟨generators, words, orbit⟩ chain
    else throw (IO.userError "large-order base point is out of bounds")
  let some group := Group.ofChain? input chain
    | throw (IO.userError "large-order chain failed independent checking")
  unless group.order == 2 ^ 65 do
    throw (IO.userError "large group order was truncated")
  for k in [0, 2 ^ 64, 2 ^ 65 - 1] do
    let some p := group.unrank? k
      | throw (IO.userError "large in-range index was rejected")
    unless (group.rank p).val == k do
      throw (IO.userError "large-index round trip was truncated")
  match group.elementsWith 100 with
  | .error limit =>
    unless limit.required == 2 ^ 65 do
      throw (IO.userError "large enumeration bound was truncated")
  | .ok _ => throw (IO.userError "large enumeration ignored its cap")
  let trivial := Group.ofGenerators (#[] : Array (Perm 130))
  if ht : trivial.isSubgroup group = true then
    match group.leftCosetsWith 100 trivial ((Group.isSubgroup_iff _ _).mp ht) with
    | .error limit =>
      unless limit.required == 2 ^ 65 && limit.capacity == 100 do
        throw (IO.userError "large coset index was truncated")
    | .ok _ => throw (IO.userError "large coset traversal ignored its cap")
  else throw (IO.userError "large group rejected the trivial subgroup")

#eval do
  let rotations := Group.ofGenerators #[cycle]
  let A : Vector Bool 3 := #v[true, false, false]
  let B : Vector Bool 3 := #v[false, true, false]
  let some transporter := indexedGroup.setTransporter? A B
    | throw (IO.userError "set transporter rejected a reachable subset")
  unless transporter.val == cycle do
    throw (IO.userError "set transporter did not follow stored child order")
  let stabilizer := indexedGroup.setStabilizer A
  let .ok elements := stabilizer.elementsWith 6
    | throw (IO.userError "source stabilizer exceeded the ambient order")
  let coset := elements.map fun p : Element stabilizer => transporter.val.comp p.val
  unless coset.size == 2 && coset.contains cycle && coset.contains swap do
    throw (IO.userError "set transporter coset uses the wrong multiplication direction")
  unless !(Search.Sets.test A B (swap12.comp transporter.val)) do
    throw (IO.userError "set transporter direction regression did not distinguish right multiplication")
  -- Both individual orbit tests succeed, but no even permutation realizes
  -- the first two images of this transposition simultaneously.
  for points in [[0], [1]] do
    if (Search.transport rotations swap points).failed then
      throw (IO.userError "single assigned image in a transitive group was rejected")
  unless (Search.transport rotations swap [1, 0]).failed do
    throw (IO.userError "intersection refinement used independent point orbits")
  match Search.transport rotations cycle [2, 1, 0] with
  | .impossible _ => throw (IO.userError "simultaneous transporter rejected a group element")
  | .found t =>
    unless t.rep.val == cycle && t.group.order == 1 do
      throw (IO.userError "simultaneous transporter reversed multiplication or retained a nontrivial stabilizer")
  unless (rotations.centralizer swapGroup).order == 1 do
    throw (IO.userError "centralizer required the second group to lie in the first")
  let _ ← checkBudget (Search.Centralizer.constraint rotations rotations) searchBudget
    (rotations.centerWith searchBudget) rotations
  let generatedSwap := Group.ofGenerators #[swap]
  let _ ← checkBudget (Search.Centralizer.constraint rotations generatedSwap) searchBudget
    (rotations.centralizerPermWith searchBudget swap) trivialGroup
  let exchange : Perm 4 := ⟨#v[2, 3, 0, 1], by decide, by decide⟩
  let left : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
  let right : Perm 4 := ⟨#v[0, 1, 3, 2], by decide, by decide⟩
  let exchanging := Group.ofGenerators #[exchange]
  let blocks := Group.ofGenerators #[left, right]
  unless (exchanging.normalizer blocks).sameGroup exchanging do
    throw (IO.userError "normalizer refinement gave fixed colors to interchangeable orbits")
  let _ ← checkBudget (Search.Normalizer.constraint exchanging blocks) searchBudget
    (exchanging.normalizerWith searchBudget blocks) exchanging
  let rotation : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
  let symmetric := Group.ofGenerators #[rotation, left]
  let cyclic := Group.ofGenerators #[rotation]
  let normalizer := symmetric.normalizer cyclic
  unless normalizer.order == 8 && !normalizer.contains left do
    throw (IO.userError "normalizer accepted orbit agreement without checking generator conjugates")

#eval do
  let trials := Search.Trials.range 5
  for capacity in [0, 3, 4, 10] do
    let run := trials.scan (fun x => decide (x.val = 3)) 0 capacity
    unless run.used == min capacity 4 do
      throw (IO.userError "refinement scan miscounted tests before the first rejection")
    match run.result with
    | .found i _ _ _ =>
      unless capacity >= 4 && i.val == 3 do
        throw (IO.userError "refinement scan changed candidate order or exceeded its allowance")
    | .clear _ => throw (IO.userError "refinement scan missed a rejecting test")
    | .incomplete =>
      unless capacity < 4 do throw (IO.userError "refinement scan exhausted a sufficient allowance")
  let exhausted := trials.scan (fun _ => false) 0 4
  unless exhausted.used == 4 do throw (IO.userError "negative refinement scan miscounted work")
  match exhausted.result with
  | .incomplete => pure ()
  | _ => throw (IO.userError "refinement exhaustion became a complete negative answer")
  let complete := trials.scan (fun _ => false) 0 5
  unless complete.used == 5 do throw (IO.userError "complete refinement scan miscounted work")
  match complete.result with
  | .clear _ => pure ()
  | _ => throw (IO.userError "complete refinement scan failed to certify all tests")
  let empty := ((Search.Trials.range 0).product (Search.Trials.range 5)).scan (fun _ => false) 0 0
  match empty.result with
  | .clear _ => unless empty.used == 0 do throw (IO.userError "empty refinement scan charged work")
  | _ => throw (IO.userError "zero-size refinement product failed without indexing any candidate")
  let count : Nat := 2 ^ 64
  let candidates : Search.Trials (Fin count × Fin 3) :=
    (Search.Trials.range count).product (Search.Trials.range 3)
  let huge := candidates.scan (fun _ : Fin count × Fin 3 => false) 0 1
  match huge.result with
  | .incomplete => unless huge.used == 1 do throw (IO.userError "large refinement allowance was truncated")
  | _ => throw (IO.userError "large refinement family was treated as complete after one test")
  let constraint := Search.Sets.transporter swapGroup #v[true, false, false] #v[false, false, true]
  for capacity in [3, 4] do
    let run := constraint.findWith (Search.Node.root swapGroup) capacity
    unless run.used == capacity do throw (IO.userError "set refinement did not count individual color/orbit tests")
    match run.result with
    | .found _ _ _ _ => unless capacity == 4 do throw (IO.userError "set refinement used an unavailable orbit test")
    | .incomplete => unless capacity == 3 do throw (IO.userError "set refinement missed an available orbit rejection")
    | .clear _ => throw (IO.userError "set refinement missed unequal suffix-orbit counts")

#eval do
  let constraint := Search.Intersection.constraint indexedGroup swapGroup
  let used ← checkBudget constraint searchBudget (indexedGroup.intersectionWith searchBudget swapGroup) swapGroup
  for resource in [Search.Resource.nodes, .refinements, .sifts, .certificates] do
    unless used.get resource > 0 do throw (IO.userError "budget regression did not exercise every resource")
    let capacity := used.get resource - 1
    let budget : Search.Budget := match resource with
      | .nodes => { searchBudget with nodes := capacity }
      | .refinements => { searchBudget with refinements := capacity }
      | .sifts => { searchBudget with sifts := capacity }
      | .certificates => { searchBudget with certificates := capacity }
    match indexedGroup.intersectionWith budget swapGroup with
    | .complete _ _ => throw (IO.userError "subgroup search ignored a resource limit")
    | .incomplete lowerBound failure =>
      unless failure.resource == resource && failure.meter.used.get resource == capacity &&
          failure.requested == 1 && lowerBound.group.isSubgroup swapGroup &&
          checkChain lowerBound.group.generators lowerBound.group.chain do
        throw (IO.userError "subgroup exhaustion lost its counters or verified lower bound")
      if resource == Search.Resource.certificates then
        unless lowerBound.group.sameGroup swapGroup do
          throw (IO.userError "certificate exhaustion discarded the subgroup found before the final node")
  let zeroNodes : Search.Budget := { searchBudget with nodes := 0 }
  match indexedGroup.intersectionWith zeroNodes swapGroup with
  | .complete _ _ => throw (IO.userError "zero-node search claimed completion")
  | .incomplete lowerBound failure =>
    unless failure.resource == Search.Resource.nodes && failure.meter.used == ({} : Search.Work) && lowerBound.group.order == 1 do
      throw (IO.userError "zero-node search performed work or returned an invalid initial lower bound")
  for capacity in [1, 2] do
    let budget : Search.Budget := { sifts := capacity }
    match Search.Tester.normalizer swapGroup (Perm.id 3) (Search.Meter.empty budget) with
    | .exhausted failure =>
      unless capacity == 1 && failure.resource == Search.Resource.sifts && failure.meter.used.sifts == 1 do
        throw (IO.userError "normalizer leaf exhaustion did not preserve the completed forward sift")
    | .ok result meter =>
      unless capacity == 2 && result.val && meter.used.sifts == 2 do
        throw (IO.userError "normalizer leaf omitted a conjugation direction or miscounted sifts")

#eval do
  let A : Vector Bool 3 := #v[true, false, false]
  let B : Vector Bool 3 := #v[false, true, false]
  let constraint := Search.Sets.transporter indexedGroup A B
  let expected := #[cycle.vec.toArray.map Fin.val, swap.vec.toArray.map Fin.val]
  let (used, wordSize) ← checkAnswerBudget constraint searchBudget
    (indexedGroup.setTransporterWith searchBudget A B) expected
  unless wordSize > 0 do throw (IO.userError "positive transporter did not retain its word size")
  for resource in [Search.Resource.nodes, .refinements, .sifts, .certificates] do
    unless used.get resource > 0 do throw (IO.userError "positive transporter did not exercise every budget")
    let capacity := used.get resource - 1
    let budget : Search.Budget := match resource with
      | .nodes => { searchBudget with nodes := capacity }
      | .refinements => { searchBudget with refinements := capacity }
      | .sifts => { searchBudget with sifts := capacity }
      | .certificates => { searchBudget with certificates := capacity }
    match indexedGroup.setTransporterWith budget A B with
    | .complete _ _ => throw (IO.userError "positive transporter ignored a resource limit")
    | .incomplete failure =>
      unless failure.resource == resource && failure.meter.used.get resource <= capacity do
        throw (IO.userError "positive transporter lost the exhausted resource or exceeded its allowance")
      if resource == Search.Resource.certificates then
        unless failure.requested == wordSize && failure.meter.used.certificates == used.certificates - wordSize do
          throw (IO.userError "positive transporter allocated a partial word before checking its exact size")
  let target : Vector Bool 3 := #v[false, false, true]
  let budget : Search.Budget := { nodes := 1, refinements := 4, certificates := 1 }
  let (negative, _) ← checkAnswerBudget (Search.Sets.transporter swapGroup A target) budget
    (swapGroup.setTransporterWith budget A target) #[]
  unless negative == ({ nodes := 1, refinements := 4, sifts := 0, certificates := 1 } : Search.Work) do
    throw (IO.userError "negative transporter charged a witness sift or missed an orbit-count test")
  let short : Search.Budget := { budget with refinements := 3 }
  match swapGroup.setTransporterWith short A target with
  | .incomplete failure =>
    unless failure.resource == Search.Resource.refinements && failure.meter.used.refinements == 3 do
      throw (IO.userError "negative transporter failed to stop before its unavailable orbit test")
  | .complete _ _ => throw (IO.userError "unfinished negative transporter was reported as complete")

private def blockCycle : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
private def oppositeBlocks : Partition 4 := ⟨#v[0, 1, 0, 1], by decide, by decide⟩
private def partialBlocks : Partition 4 := ⟨#v[0, 1, 0, 3], by decide, by decide⟩

example : Primitivity.check indexedGroup 0
    #v[[], [(0, 1), (1, 2)], [(0, 2), (1, 0)]] = true := by decide +kernel
example : Primitivity.check indexedGroup 0
    #v[[], [(0, 1), (1, 2)], []] = false := by decide +kernel
example : indexedGroup.IsPrimitive := Primitivity.check_sound
  (by decide) (by decide +kernel)
  (by decide +kernel : Primitivity.check indexedGroup 0
    #v[[], [(0, 1), (1, 2)], [(0, 2), (1, 0)]] = true)

-- Literal kernel replay checks forced merges and final closure independently.
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] oppositeBlocks
    [(0, 2), (1, 3)] = true := by decide +kernel
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] oppositeBlocks
    [(1, 3), (0, 2)] = false := by decide +kernel
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] partialBlocks
    [(0, 2)] = false := by decide +kernel
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] (Partition.indiscrete 4)
    [(0, 2), (1, 3), (0, 1)] = false := by decide +kernel
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] oppositeBlocks
    [(0, 2), (0, 2), (1, 3)] = false := by decide +kernel
example : Blocks.check #[blockCycle, blockCycle.inv] [(0, 2)] (Partition.discrete 4)
    [] = false := by decide +kernel
example : Blocks.check #[] [] (Partition.discrete 0) [] = true := by decide +kernel
example : Blocks.check #[] [(0, 0)] (Partition.discrete 1) [] = true := by decide +kernel

#eval do
  let cyclic := Group.ofGenerators #[blockCycle]
  let result := cyclic.blocksCert [(0, 1), (1, 0), (0, 0)]
  unless result.partition = Partition.indiscrete 4 && result.trace.length == 3 do
    throw (IO.userError "cyclic block propagation failed to close several rounds of merges")
  let trivial := Group.ofGenerators (#[] : Array (Perm 4))
  let pairs : Partition 4 := ⟨#v[0, 0, 2, 2], by decide, by decide⟩
  unless trivial.blocks [(0, 1), (2, 3)] = pairs do
    throw (IO.userError "independent seed pairs were incorrectly joined into one block")
  let unequal : Partition 4 := ⟨#v[0, 0, 2, 3], by decide, by decide⟩
  unless trivial.blocks [(0, 1)] = unequal do
    throw (IO.userError "intransitive block system lost unequal block sizes")

-- Generator commutators alone miss part of the derived subgroup of S₄.
#eval do
  let transposition : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
  let group := Group.ofGenerators #[blockCycle, transposition]
  unless (Derived.seedGroup group).order < group.derived.order &&
      group.derivedSeries.certificate.orders group == [24, 12, 4, 1] do
    throw (IO.userError "S4 derived series omitted normal closure or has the wrong terms")

-- A₅ is a nontrivial perfect group; S₅ reaches that fixed point after one step.
#eval do
  let five : Perm 5 := ⟨#v[1, 2, 3, 4, 0], by decide, by decide⟩
  let three : Perm 5 := ⟨#v[1, 2, 0, 3, 4], by decide, by decide⟩
  let swap : Perm 5 := ⟨#v[1, 0, 2, 3, 4], by decide, by decide⟩
  let candidates := (permutations (List.range 5)).map List.toArray
  for (input, orders) in [(#[five, three], [60, 60]), (#[five, swap], [120, 60, 60])] do
    let group := Group.ofGenerators input
    let reference := closure 5 (input.map fun p : Perm 5 => p.vec.toArray.map Fin.val)
    checkDerivedSeries group reference candidates
    unless group.derivedSeries.certificate.orders group == orders && !group.isSolvable do
      throw (IO.userError "nontrivial perfect terminal group was not certified")

#eval do
  let mut count := 0
  for n in List.range 4 do
    for m in List.range 4 do
      for p in permutations (List.range n) do
        for q in permutations (List.range m) do
          let some a := Perm.ofNatArray? n (List.toArray p)
            | throw (IO.userError "direct product left input rejected")
          let some b := Perm.ofNatArray? m (List.toArray q)
            | throw (IO.userError "direct product right input rejected")
          checkDirectProduct (Group.ofGenerators #[a]) (Group.ofGenerators #[b])
          count := count + 1
  unless count == 100 do throw (IO.userError "direct product degree-zero or small-factor cases were omitted")
  checkDirectProduct indexedGroup indexedGroup
  let fixedSwap : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
  checkDirectProduct (Group.ofGenerators #[fixedSwap]) swapGroup

-- Destination-indexed action: the swap in block zero acts after the top swap.
private def swap2 : Perm 2 := ⟨#v[1, 0], by decide, by decide⟩
example : (Perm.Wreath.perm (by decide : 0 < 2)
    (fun j : Fin 2 => if j = 0 then swap2 else Perm.id 2) swap2).vec = #v[2, 3, 1, 0] := by decide +kernel

#eval do
  let two := Group.ofGenerators #[swap2]
  let three := Group.ofGenerators #[cycle]
  let singleton := Group.ofGenerators (#[] : Array (Perm 1))
  checkWreathProduct two two
  checkWreathProduct three two
  checkWreathProduct two three
  checkWreathProduct indexedGroup two
  checkWreathProduct two swapGroup
  checkWreathProduct two trivialGroup
  checkWreathProduct swapGroup two
  checkWreathProduct singleton indexedGroup
  checkWreathProduct two singleton
  checkWreathProduct two zeroGroup
  checkWreathProduct zeroGroup indexedGroup
  checkWreathProduct zeroGroup zeroGroup

end Hex.PermGroup.Conformance
