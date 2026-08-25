/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Division

public section
set_option backward.proofsInPublic true

/-!
Balanced product trees.

The representation is private: clients observe the original leaves, the
balanced levels, and the root product through the accessors below. Adjacent
nodes are multiplied with the supplied lawful plan; an unpaired final node is
carried to the next level unchanged.
-/

namespace Hex.DensePoly

universe u

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Multiply adjacent entries, carrying an unpaired final entry unchanged. -/
private def pairProducts (plan : MulPlan R) : List (DensePoly R) → List (DensePoly R)
  | [] => []
  | [p] => [p]
  | p :: q :: rest => mulWith plan p q :: pairProducts plan rest

/-- Product of a list through a lawful multiplication plan. -/
private def plannedProduct (plan : MulPlan R) (xs : List (DensePoly R)) : DensePoly R :=
  xs.foldl (fun acc p => mulWith plan acc p) 1

private theorem plannedProduct_cons (plan : MulPlan R) (p : DensePoly R)
    (xs : List (DensePoly R)) :
    plannedProduct plan (p :: xs) = p * plannedProduct plan xs := by
  unfold plannedProduct
  simp only [List.foldl_cons]
  have hfun : (fun acc q => mulWith plan acc q) = (fun acc q => acc * q) := by
    funext acc q
    exact mulWith_eq plan acc q
  rw [mulWith_eq, DensePoly.mul_comm_poly (1 : DensePoly R) p,
    DensePoly.mul_one_right_poly, hfun]
  simpa using List.foldl_mul_eq_mul_foldl xs id p

private theorem plannedProduct_pairProducts (plan : MulPlan R) :
    ∀ xs, plannedProduct plan (pairProducts plan xs) = plannedProduct plan xs := by
  intro xs
  induction hlen : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil => rfl
      | cons p rest =>
          cases rest with
          | nil => rfl
          | cons q rest =>
              rw [pairProducts, plannedProduct_cons, mulWith_eq,
                plannedProduct_cons, plannedProduct_cons,
                ih rest.length (by simp at hlen; omega) rest rfl,
                DensePoly.mul_assoc_poly]

/-- Build all nonempty balanced levels and return their root. Fuel is only a
totality guard; construction supplies the leaf count. -/
private def buildLevels (plan : MulPlan R) :
    Nat → List (DensePoly R) → List (List (DensePoly R)) × DensePoly R
  | 0, xs => ([xs], plannedProduct plan xs)
  | _ + 1, [] => ([[1]], 1)
  | _ + 1, [p] => ([[p]], p)
  | fuel + 1, p :: q :: rest =>
      let current := p :: q :: rest
      let next := pairProducts plan current
      let built := buildLevels plan fuel next
      (current :: built.1, built.2)

private theorem buildLevels_root (plan : MulPlan R) : ∀ fuel xs,
    (buildLevels plan fuel xs).2 = plannedProduct plan xs := by
  intro fuel
  induction fuel with
  | zero => intro xs; rfl
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil => simp [buildLevels, plannedProduct, mulWith_eq]
      | cons p rest =>
          cases rest with
          | nil =>
              simp [buildLevels, plannedProduct, mulWith_eq,
                DensePoly.mul_comm_poly (1 : DensePoly R) p,
                DensePoly.mul_one_right_poly]
          | cons q rest =>
              rw [buildLevels]
              dsimp only
              rw [ih, plannedProduct_pairProducts]

/-- An opaque balanced product tree. -/
structure ProductTree (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  private planData : MulPlan R
  private leafData : Array (DensePoly R)
  private levelData : Array (Array (DensePoly R))
  private rootData : DensePoly R

namespace ProductTree

/-- Build a balanced product tree. The empty tree has root `1` and one
singleton internal level containing that root. -/
def build (plan : MulPlan R) (leaves : Array (DensePoly R)) : ProductTree R :=
  let built := buildLevels plan leaves.size leaves.toList
  { planData := plan
    leafData := leaves
    levelData := (built.1.map List.toArray).toArray
    rootData := built.2 }

/-- The leaf sequence in its original order. -/
def leaves (tree : ProductTree R) : Array (DensePoly R) := tree.leafData

/-- Number of stored nonempty levels. -/
def levelCount (tree : ProductTree R) : Nat := tree.levelData.size

/-- Lawful multiplication plan used to build the tree. -/
def plan (tree : ProductTree R) : MulPlan R := tree.planData

/-- A stored balanced level, from leaves upward. -/
def level? (tree : ProductTree R) (i : Nat) : Option (Array (DensePoly R)) :=
  tree.levelData[i]?

/-- The product represented by the root node. -/
def root (tree : ProductTree R) : DensePoly R := tree.rootData

/-- The ordered leaf block represented by a node. Invalid level/node pairs
represent the empty block; use `nodeProduct?` when validity matters. -/
def nodeLeaves (tree : ProductTree R) (level index : Nat) : Array (DensePoly R) :=
  let width := 2 ^ level
  let lo := index * width
  tree.leafData.extract lo (min tree.leafData.size (lo + width))

/-- Product represented by a valid stored node. The observation is semantic:
it folds exactly that node's leaf block, independently of the internal level
layout. -/
def nodeProduct? (tree : ProductTree R) (level index : Nat) : Option (DensePoly R) :=
  if level < tree.levelCount &&
      ((tree.leafData.isEmpty && level = 0 && index = 0) ||
        index * 2 ^ level < tree.leafData.size) then
    some ((tree.nodeLeaves level index).foldl
      (fun acc p => mulWith tree.plan acc p) 1)
  else
    none

/-- Every observed node product is the planned product of precisely its
represented leaf block. -/
theorem nodeProduct?_eq (tree : ProductTree R) (level index : Nat)
    (p : DensePoly R) (h : tree.nodeProduct? level index = some p) :
    p = (tree.nodeLeaves level index).foldl
      (fun acc q => mulWith tree.plan acc q) 1 := by
  unfold nodeProduct? at h
  split at h
  · exact Option.some.inj h |>.symm
  · contradiction

/-- Building preserves the supplied leaf sequence. -/
@[simp] theorem leaves_build (plan : MulPlan R) (leaves : Array (DensePoly R)) :
    ProductTree.leaves (build plan leaves) = leaves := by
  rfl

/-- The root is the planned product of all leaves in order. -/
theorem root_build (plan : MulPlan R) (leaves : Array (DensePoly R)) :
    (build plan leaves).root =
      leaves.toList.foldl (fun acc p => mulWith plan acc p) 1 := by
  unfold build root
  dsimp only
  exact buildLevels_root plan leaves.size leaves.toList

/-- The root is independent of the selected lawful multiplication kernel. -/
theorem root_build_eq_foldl (plan : MulPlan R) (leaves : Array (DensePoly R)) :
    (build plan leaves).root = leaves.foldl (fun acc p => acc * p) 1 := by
  rw [root_build]
  rw [← Array.foldl_toList]
  have hfun : (fun acc p => mulWith plan acc p) = (fun acc p => acc * p) := by
    funext acc p
    exact mulWith_eq plan acc p
  rw [hfun]

end ProductTree

end Hex.DensePoly
