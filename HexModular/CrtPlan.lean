/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt

public section

/-!
Balanced, reusable Chinese-remainder plans.

Unlike `Crt` and `CrtVec`, a `CrtPlan` knows every modulus in advance.  It
therefore computes a balanced product tree and all sibling inverses once,
then reuses them for every scalar or vector reconstruction.
-/
namespace Hex

namespace Modular

namespace CrtPlan

/-- Executable pairwise-coprimality check. -/
def checkPairwise : List Nat → Bool
  | [] => true
  | modulus :: moduli =>
      moduli.all (fun other => decide (Nat.gcd modulus other = 1)) &&
        checkPairwise moduli

/-- Executable validation check for a batch CRT plan. -/
def check (moduli : Array Nat) : Bool :=
  moduli.toList.all (fun modulus => decide (1 < modulus)) &&
    checkPairwise moduli.toList

/-- The validation condition for a batch CRT plan. -/
def Valid (moduli : Array Nat) : Prop :=
  check moduli = true

instance (moduli : Array Nat) : Decidable (Valid moduli) :=
  inferInstanceAs (Decidable (check moduli = true))

private theorem checkPairwise_eq_true {moduli : List Nat} :
    checkPairwise moduli = true ↔
      moduli.Pairwise (fun left right => Nat.gcd left right = 1) := by
  induction moduli with
  | nil => simp [checkPairwise]
  | cons modulus moduli ih =>
      simp [checkPairwise, List.all_eq_true, ih]

/-- Validation means precisely that every modulus is greater than one and
that the moduli are pairwise coprime. -/
theorem valid_iff {moduli : Array Nat} :
    Valid moduli ↔
      (∀ m ∈ moduli.toList, 1 < m) ∧
        moduli.toList.Pairwise (fun left right => Nat.gcd left right = 1) := by
  unfold Valid check
  rw [Bool.and_eq_true, checkPairwise_eq_true]
  constructor
  · rintro ⟨hall, hpair⟩
    refine ⟨?_, hpair⟩
    intro modulus hmodulus
    exact of_decide_eq_true (List.all_eq_true.mp hall modulus hmodulus)
  · rintro ⟨hall, hpair⟩
    refine ⟨?_, hpair⟩
    apply List.all_eq_true.mpr
    intro modulus hmodulus
    exact decide_eq_true (hall modulus hmodulus)

/-- A balanced modulus-product tree.  A branch stores the inverse of the
left product modulo the right product. -/
inductive Tree where
  | empty
  | leaf (modulus : Nat)
  | branch (left right : Tree) (inverse : Int)
  deriving Inhabited

namespace Tree

/-- Product of all leaf moduli below a CRT tree. -/
def product : Tree → Nat
  | .empty => 1
  | .leaf modulus => modulus
  | .branch left right _ => left.product * right.product

/-- Join two adjacent product trees, computing their sibling inverse once. -/
def merge (left right : Tree) : Tree :=
  let leftModulus := left.product
  let rightModulus := right.product
  let inverse := (HexArith.Int.extGcd
    (Int.ofNat (leftModulus % rightModulus))
    (Int.ofNat rightModulus)).2.1
  .branch left right inverse

/-- Merge adjacent nodes of one product-tree level. -/
def mergeLevel : List Tree → List Tree
  | [] => []
  | [tree] => [tree]
  | left :: right :: rest => left.merge right :: mergeLevel rest

/-- Repeatedly merge levels.  The initial leaf count is sufficient fuel:
every nontrivial level strictly decreases the number of nodes. -/
def finish : Nat → List Tree → Tree
  | 0, [] => .empty
  | 0, tree :: _ => tree
  | _ + 1, [] => .empty
  | _ + 1, [tree] => tree
  | fuel + 1, trees => finish fuel (mergeLevel trees)

/-- Build the balanced tree for a list of moduli. -/
def ofList (moduli : List Nat) : Tree :=
  finish moduli.length (moduli.map .leaf)

/-- Combine two symmetric representatives using a precomputed sibling
inverse. -/
def combine (left right inverse : Int) (leftModulus rightModulus : Nat) : Int :=
  let delta := symMod ((right - left) * inverse) rightModulus
  symMod (left + Int.ofNat leftModulus * delta)
    (leftModulus * rightModulus)

/-- Evaluate a scalar reconstruction tree, consuming one residue per leaf. -/
def eval : Tree → List Int → Int × List Int
  | .empty, residues => (0, residues)
  | .leaf _, [] => (0, [])
  | .leaf modulus, residue :: residues => (symMod residue modulus, residues)
  | .branch left right inverse, residues =>
      let (leftValue, residues) := left.eval residues
      let (rightValue, residues) := right.eval residues
      (combine leftValue rightValue inverse left.product right.product, residues)

/-- Evaluate all lanes of a reconstruction tree together.  Every branch uses
its stored inverse once for the whole vector. -/
def evalVec (k : Nat) : Tree → List (Vector Int k) →
    Vector Int k × List (Vector Int k)
  | .empty, residues => (Vector.replicate k 0, residues)
  | .leaf _, [] => (Vector.replicate k 0, [])
  | .leaf modulus, residue :: residues =>
      (Vector.map (fun value => symMod value modulus) residue, residues)
  | .branch left right inverse, residues =>
      let (leftValue, residues) := left.evalVec k residues
      let (rightValue, residues) := right.evalVec k residues
      (Vector.zipWith
        (fun l r => combine l r inverse left.product right.product)
        leftValue rightValue,
        residues)

end Tree

private theorem prod_pos_of_gt_one {moduli : List Nat}
    (h : ∀ m ∈ moduli, 1 < m) :
    0 < moduli.prod := by
  induction moduli with
  | nil => simp
  | cons modulus moduli ih =>
      rw [List.prod_cons]
      apply Nat.mul_pos
      · have := h modulus (by simp)
        omega
      · apply ih
        intro m hm
        exact h m (by simp [hm])

end CrtPlan

/-- A validated balanced product tree of pairwise-coprime moduli greater than
one.  The tree contains all extended-GCD work needed by reconstruction. -/
structure CrtPlan where
  /-- Moduli in residue input order. -/
  moduli : Array Nat
  /-- Balanced product tree with precomputed sibling inverses. -/
  tree : CrtPlan.Tree
  /-- All moduli are greater than one and pairwise coprime. -/
  valid : CrtPlan.Valid moduli

namespace CrtPlan

/-- Product of every modulus in a CRT plan. -/
def modulus (plan : CrtPlan) : Nat :=
  plan.moduli.toList.prod

/-- The root modulus of a validated plan is positive. -/
theorem modulus_pos (plan : CrtPlan) : 0 < plan.modulus := by
  exact prod_pos_of_gt_one (valid_iff.mp plan.valid).1

/-- Validate moduli and precompute a balanced product tree. -/
def build? (moduli : Array Nat) : Option CrtPlan :=
  if h : Valid moduli then
    some
      { moduli
        tree := Tree.ofList moduli.toList
        valid := h }
  else
    none

/-- Plan construction succeeds exactly for moduli greater than one that are
pairwise coprime. -/
theorem build?_isSome (moduli : Array Nat) :
    (build? moduli).isSome = decide (Valid moduli) := by
  unfold build?
  split
  · simp_all
  · simp_all

/-- A successful build records the requested modulus array unchanged. -/
theorem build?_moduli {moduli : Array Nat} {plan : CrtPlan}
    (h : build? moduli = some plan) :
    plan.moduli = moduli := by
  unfold build? at h
  split at h <;> try contradiction
  cases h
  rfl

/-- Reconstruct one residue for every modulus.  A count mismatch is rejected;
the final linear congruence check makes the public result self-validating. -/
def reconstruct? (plan : CrtPlan) (residues : Array Int) : Option Int :=
  if hsize : residues.size = plan.moduli.size then
    let raw := (plan.tree.eval residues.toList).1
    let value := symMod raw plan.modulus
    if _hcongr : ∀ i : Fin plan.moduli.size,
        value % (plan.moduli[i] : Int) =
          residues.getD i.val 0 % (plan.moduli[i] : Int) then
      some value
    else
      none
  else
    none

/-- Reconstruct `k` lanes sharing one plan.  Tree inverses are reused across
every lane; reconstruction does not invoke extended GCD. -/
def reconstructVec? (plan : CrtPlan)
    (residues : Array (Vector Int k)) : Option (Vector Int k) :=
  if hsize : residues.size = plan.moduli.size then
    let raw := (plan.tree.evalVec k residues.toList).1
    let value := Vector.map (fun x => symMod x plan.modulus) raw
    let zero : Vector Int k := Vector.replicate k 0
    if _hcongr : ∀ i : Fin plan.moduli.size, ∀ j : Fin k,
        value[j] % (plan.moduli[i] : Int) =
          (residues.getD i.val zero)[j] % (plan.moduli[i] : Int) then
      some value
    else
      none
  else
    none

/-- Scalar reconstruction rejects a residue-count mismatch. -/
theorem reconstruct?_eq_none_of_size_ne (plan : CrtPlan) (residues : Array Int)
    (h : residues.size ≠ plan.moduli.size) :
    plan.reconstruct? residues = none := by
  simp [reconstruct?, h]

/-- Vector reconstruction rejects a residue-count mismatch. -/
theorem reconstructVec?_eq_none_of_size_ne (plan : CrtPlan)
    (residues : Array (Vector Int k))
    (h : residues.size ≠ plan.moduli.size) :
    plan.reconstructVec? residues = none := by
  simp [reconstructVec?, h]

/-- A successful scalar reconstruction is congruent to every input residue. -/
theorem reconstruct?_congr {plan : CrtPlan} {residues : Array Int} {value : Int}
    (h : plan.reconstruct? residues = some value) :
    residues.size = plan.moduli.size ∧
      ∀ i : Fin plan.moduli.size,
        value % (plan.moduli[i] : Int) =
          residues.getD i.val 0 % (plan.moduli[i] : Int) := by
  unfold reconstruct? at h
  split at h <;> try contradiction
  next hsize =>
    dsimp only at h
    split at h <;> try contradiction
    next hcongr =>
      cases h
      exact ⟨hsize, hcongr⟩

/-- Every lane of a successful vector reconstruction is congruent to its
input residue at every modulus. -/
theorem reconstructVec?_congr {plan : CrtPlan}
    {residues : Array (Vector Int k)} {value : Vector Int k}
    (h : plan.reconstructVec? residues = some value) :
    residues.size = plan.moduli.size ∧
      ∀ i : Fin plan.moduli.size, ∀ j : Fin k,
        value[j] % (plan.moduli[i] : Int) =
          (residues.getD i.val (Vector.replicate k 0))[j] %
            (plan.moduli[i] : Int) := by
  unfold reconstructVec? at h
  split at h <;> try contradiction
  next hsize =>
    dsimp only at h
    split at h <;> try contradiction
    next hcongr =>
      cases h
      exact ⟨hsize, hcongr⟩

/-- A scalar result lies in the symmetric interval of the root product. -/
theorem reconstruct?_le {plan : CrtPlan} {residues : Array Int} {value : Int}
    (h : plan.reconstruct? residues = some value) :
    2 * value.natAbs ≤ plan.modulus := by
  unfold reconstruct? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h
  exact symMod_le plan.modulus_pos

/-- Every vector result lies in the symmetric interval of the root product. -/
theorem reconstructVec?_le {plan : CrtPlan}
    {residues : Array (Vector Int k)} {value : Vector Int k}
    (h : plan.reconstructVec? residues = some value) :
    ∀ j : Fin k, 2 * value[j].natAbs ≤ plan.modulus := by
  unfold reconstructVec? at h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h
  intro j
  change 2 * (Vector.map (fun x => symMod x plan.modulus) _)[j.val].natAbs ≤ _
  simp only [Vector.getElem_map]
  exact symMod_le plan.modulus_pos

end CrtPlan

end Modular

end Hex
