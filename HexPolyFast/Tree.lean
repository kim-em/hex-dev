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

The representation is private: clients observe the original leaves, balanced
levels, and the root product through the accessors below. The root is cached;
level observations are reconstructed on demand. Adjacent nodes are multiplied
with the supplied lawful plan; an unpaired final node is carried to the next
level unchanged.
-/

namespace Hex.DensePoly

universe u

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

omit [DecidableEq R] in
private theorem eqZeroOfOneEqZero (h : (1 : R) = 0) (a : R) : a = 0 := by
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
    _ = a * 0 := by rw [h]
    _ = 0 := Lean.Grind.Semiring.mul_zero a

/-- A monic polynomial over a nontrivial commutative ring is nonzero. -/
theorem Monic.neOfOneNe {p : DensePoly R} (hp : p.Monic)
    (hone : (1 : R) ≠ 0) : p ≠ 0 := by
  intro hz
  rw [hz, monic_iff_leadingCoeff_eq_one, leadingCoeff_zero] at hp
  exact hone hp.symm

/-- A product of monic polynomials over a commutative ring is monic. -/
theorem Monic.mul {p q : DensePoly R} (hp : p.Monic) (hq : q.Monic) :
    (p * q).Monic := by
  by_cases h : (1 : R) = 0
  · rw [monic_iff_leadingCoeff_eq_one, h]
    exact eqZeroOfOneEqZero h _
  · have hpne := hp.neOfOneNe h
    have hqne := hq.neOfOneNe h
    have hppos : 0 < p.size := by
      apply Nat.pos_of_ne_zero
      intro hs
      exact hpne ((size_eq_zero_iff p).mp hs)
    have hqpos : 0 < q.size := by
      apply Nat.pos_of_ne_zero
      intro hs
      exact hqne ((size_eq_zero_iff q).mp hs)
    have hone : (1 : R) * 1 ≠ 0 := by
      rw [Lean.Grind.Semiring.one_mul]
      exact h
    have hprod : p.leadingCoeff * q.leadingCoeff ≠ (0 : R) := by
      rw [hp, hq]
      exact hone
    rw [monic_iff_leadingCoeff_eq_one,
      leadingCoeff_mul p q hppos hqpos hprod, hp, hq]
    grind

/-- Root split used by adjacent-pair product levels: the largest power of two
strictly below `n`. -/
def treeSplit (n : Nat) : Nat := 2 ^ Nat.log2 (n - 1)

theorem treeSplit_pos (n : Nat) : 0 < treeSplit n := by
  unfold treeSplit
  exact Nat.pow_pos (by omega)

theorem treeSplit_lt (n : Nat) (hn : 2 ≤ n) : treeSplit n < n := by
  have hm : n - 1 ≠ 0 := by omega
  have hle : 2 ^ Nat.log2 (n - 1) ≤ n - 1 :=
    Nat.log2_self_le hm
  unfold treeSplit
  omega

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

/-- Build the root of a balanced product tree. Fuel is only a totality guard;
construction supplies the leaf count. -/
private def buildRoot (plan : MulPlan R) :
    Nat → List (DensePoly R) → DensePoly R
  | 0, xs => plannedProduct plan xs
  | _ + 1, [] => 1
  | _ + 1, [p] => p
  | fuel + 1, p :: q :: rest =>
      let current := p :: q :: rest
      let next := pairProducts plan current
      buildRoot plan fuel next

private theorem buildRoot_eq (plan : MulPlan R) : ∀ fuel xs,
    buildRoot plan fuel xs = plannedProduct plan xs := by
  intro fuel
  induction fuel with
  | zero => intro xs; rfl
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil => simp [buildRoot, plannedProduct, mulWith_eq]
      | cons p rest =>
          cases rest with
          | nil =>
              simp [buildRoot, plannedProduct, mulWith_eq,
                DensePoly.mul_comm_poly (1 : DensePoly R) p,
                DensePoly.mul_one_right_poly]
          | cons q rest =>
              rw [buildRoot]
              rw [ih, plannedProduct_pairProducts]

/-- Reconstruct one balanced level from the leaves. The empty tree uses the
singleton level `[1]`. -/
private def buildLevel (plan : MulPlan R) :
    Nat → List (DensePoly R) → List (DensePoly R)
  | 0, [] => [1]
  | 0, xs => xs
  | level + 1, xs => pairProducts plan (buildLevel plan level xs)

/-- An opaque balanced product tree with a cached root and on-demand levels. -/
structure ProductTree (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  private planData : MulPlan R
  private leafData : Array (DensePoly R)
  private rootData : DensePoly R

namespace ProductTree

/-- Build a balanced product tree without retaining intermediate levels. The
empty tree has root `1` and one singleton level containing that root. -/
def build (plan : MulPlan R) (leaves : Array (DensePoly R)) : ProductTree R :=
  { planData := plan
    leafData := leaves
    rootData := buildRoot plan leaves.size leaves.toList }

/-- The leaf sequence in its original order. -/
def leaves (tree : ProductTree R) : Array (DensePoly R) := tree.leafData

/-- Number of nonempty balanced levels, including the leaf and root levels. -/
def levelCount (tree : ProductTree R) : Nat :=
  if tree.leafData.size ≤ 1 then 1 else Nat.log2 (tree.leafData.size - 1) + 2

/-- Lawful multiplication plan used to build the tree. -/
def plan (tree : ProductTree R) : MulPlan R := tree.planData

/-- A balanced level reconstructed from the leaves, from leaves upward. The
empty tree has the singleton level `[1]`. -/
def level? (tree : ProductTree R) (i : Nat) : Option (Array (DensePoly R)) :=
  if i < tree.levelCount then
    some (buildLevel tree.planData i tree.leafData.toList |>.toArray)
  else
    none

/-- The product represented by the root node. -/
def root (tree : ProductTree R) : DensePoly R := tree.rootData

/-- The ordered leaf block represented by a node. Invalid level/node pairs
represent the empty block; use `nodeProduct?` when validity matters. -/
def nodeLeaves (tree : ProductTree R) (level index : Nat) : Array (DensePoly R) :=
  let width := 2 ^ level
  let lo := index * width
  tree.leafData.extract lo (min tree.leafData.size (lo + width))

/-- Product represented by a valid balanced node. The observation is semantic:
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
  exact buildRoot_eq plan leaves.size leaves.toList

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
