/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Tree

public section
set_option backward.proofsInPublic true

/-!
# General cached remainder trees

`RemainderTree` caches one finite-capacity reciprocal plan at every node of a
balanced tree of nonzero monic leaves.  Traversal returns `none` if the chosen
capacity is insufficient at any node; a successful traversal returns the
canonical-size remainder at every leaf in the original order.
-/

namespace Hex.DensePoly

universe u

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- A nonzero monic polynomial suitable as a remainder-tree leaf. -/
structure MonicLeaf (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  /-- Leaf divisor. -/
  poly : DensePoly R
  /-- The divisor is monic. -/
  monic : poly.Monic
  /-- The divisor is nonzero. -/
  ne : poly ≠ 0

/-- `RemainderSpec origin leaves results` states that `results` contains, in
order, the canonical-size remainder of `origin` at every corresponding leaf.
The divisibility and size conditions uniquely characterize a monic
remainder. -/
inductive RemainderSpec (origin : DensePoly R) :
    List (MonicLeaf R) → List (DensePoly R) → Prop where
  | nil : RemainderSpec origin [] []
  | cons {leaf : MonicLeaf R} {r : DensePoly R} {leaves results}
      (head : leaf.poly ∣ origin - r ∧ r.size ≤ leaf.poly.size - 1)
      (tail : RemainderSpec origin leaves results) :
      RemainderSpec origin (leaf :: leaves) (r :: results)

private theorem RemainderSpec.append {origin : DensePoly R}
    {as bs : List (MonicLeaf R)} {xs ys : List (DensePoly R)}
    (h₁ : RemainderSpec origin as xs) (h₂ : RemainderSpec origin bs ys) :
    RemainderSpec origin (as ++ bs) (xs ++ ys) := by
  induction h₁ with
  | nil => exact h₂
  | cons head _ ih => exact .cons head ih

/-- Internal balanced tree with a cached division plan at every node. -/
private inductive RemainderNode (R : Type u) [DecidableEq R]
    [Lean.Grind.CommRing R] where
  | leaf (entry : MonicLeaf R) (plan : DivPlan R)
      (planDivisor : plan.divisor = entry.poly) : RemainderNode R
  | branch (root : MonicLeaf R) (plan : DivPlan R)
      (planDivisor : plan.divisor = root.poly)
      (left right : RemainderNode R) : RemainderNode R

namespace RemainderNode

private def root : RemainderNode R → MonicLeaf R
  | .leaf entry _ _ => entry
  | .branch entry _ _ _ _ => entry

private def plan : RemainderNode R → DivPlan R
  | .leaf _ plan _ => plan
  | .branch _ plan _ _ _ => plan

private def leaves : RemainderNode R → List (MonicLeaf R)
  | .leaf entry _ _ => [entry]
  | .branch _ _ _ left right => left.leaves ++ right.leaves

private theorem plan_divisor (node : RemainderNode R) :
    node.plan.divisor = node.root.poly := by
  cases node <;> assumption

private inductive WellFormed : RemainderNode R → Prop where
  | leaf (entry : MonicLeaf R) (plan : DivPlan R) (hplan) :
      WellFormed (.leaf entry plan hplan)
  | branch (root : MonicLeaf R) (plan : DivPlan R) (hplan)
      (left right : RemainderNode R)
      (hleft : left.WellFormed) (hright : right.WellFormed)
      (leftDvd : left.root.poly ∣ root.poly)
      (rightDvd : right.root.poly ∣ root.poly)
      (rootDegree : root.poly.size - 1 =
        (left.root.poly.size - 1) + (right.root.poly.size - 1))
      (leftCapacity : left.plan.capacity = right.root.poly.size - 1)
      (rightCapacity : right.plan.capacity = left.root.poly.size - 1) :
      WellFormed (.branch root plan hplan left right)

end RemainderNode

private theorem foldlDegree_add (leaves : List (MonicLeaf R)) (a b : Nat) :
    leaves.foldl (fun degree leaf => degree + (leaf.poly.size - 1)) (a + b) =
      a + leaves.foldl (fun degree leaf => degree + (leaf.poly.size - 1)) b := by
  induction leaves generalizing b with
  | nil => simp
  | cons leaf leaves ih =>
      simp only [List.foldl_cons, Nat.add_assoc]
      exact ih (b + (leaf.poly.size - 1))

/-- Sum of leaf degrees, hence the degree of their monic product. -/
private def leafDegreeSum (leaves : List (MonicLeaf R)) : Nat :=
  leaves.foldl (fun degree leaf => degree + (leaf.poly.size - 1)) 0

private theorem leafDegreeSum_append (left right : List (MonicLeaf R)) :
    leafDegreeSum (left ++ right) =
      leafDegreeSum left + leafDegreeSum right := by
  simp only [leafDegreeSum, List.foldl_append]
  simpa using foldlDegree_add right
    (left.foldl (fun degree leaf => degree + (leaf.poly.size - 1)) 0) 0

private structure BuiltRemainderNode (capacity : Nat)
    (leaves : List (MonicLeaf R)) where
  node : RemainderNode R
  leaves_eq : node.leaves = leaves
  capacity_eq : node.plan.capacity = capacity
  degree_eq : node.root.poly.size - 1 = leafDegreeSum leaves
  wellFormed : node.WellFormed

private def buildRemainderNode (mul : MulPlan R) (capacity : Nat)
    (hone : (1 : R) ≠ 0) :
    (leaves : List (MonicLeaf R)) → leaves ≠ [] →
      BuiltRemainderNode capacity leaves
  | [], hne => False.elim (hne rfl)
  | [entry], _ =>
      let plan := DivPlan.ofMonic mul entry.poly entry.monic entry.ne capacity
      { node := .leaf entry plan (by simp [plan])
        leaves_eq := rfl
        capacity_eq := by
          change plan.capacity = capacity
          simp [plan]
        degree_eq := by simp [RemainderNode.root, leafDegreeSum]
        wellFormed := .leaf entry plan _ }
  | a :: b :: rest, _ =>
      let leaves := a :: b :: rest
      let split := treeSplit leaves.length
      have splitPos : 0 < split := treeSplit_pos leaves.length
      have splitLt : split < leaves.length := treeSplit_lt leaves.length (by
        dsimp [leaves]
        simp)
      let leftLeaves := leaves.take split
      let rightLeaves := leaves.drop split
      let leftCapacity := leafDegreeSum rightLeaves
      let rightCapacity := leafDegreeSum leftLeaves
      let left := buildRemainderNode mul leftCapacity hone leftLeaves (by
        intro hnil
        have hz := congrArg List.length hnil
        dsimp [leftLeaves] at hz
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt splitLt)] at hz
        omega)
      let right := buildRemainderNode mul rightCapacity hone rightLeaves (by
        intro hnil
        have hz := congrArg List.length hnil
        dsimp [rightLeaves] at hz
        rw [List.length_drop] at hz
        omega)
      let poly := mulWith mul left.node.root.poly right.node.root.poly
      have hmonic : poly.Monic := by
        dsimp [poly]
        rw [mulWith_eq]
        exact left.node.root.monic.mul right.node.root.monic
      have hne : poly ≠ 0 := hmonic.neOfOneNe hone
      let root : MonicLeaf R := { poly, monic := hmonic, ne := hne }
      let plan := DivPlan.ofMonic mul poly hmonic hne capacity
      have hroot : root.poly = left.node.root.poly * right.node.root.poly := by
        simp [root, poly, mulWith_eq]
      have hleftDvd : left.node.root.poly ∣ root.poly := by
        exact ⟨right.node.root.poly, hroot⟩
      have hrightDvd : right.node.root.poly ∣ root.poly := by
        refine ⟨left.node.root.poly, ?_⟩
        rw [hroot, mul_comm_poly]
      have hleftCapacity :
          left.node.plan.capacity = right.node.root.poly.size - 1 := by
        rw [left.capacity_eq, right.degree_eq]
      have hrightCapacity :
          right.node.plan.capacity = left.node.root.poly.size - 1 := by
        rw [right.capacity_eq, left.degree_eq]
      let node : RemainderNode R := .branch root plan (by simp [plan, root])
        left.node right.node
      have hsplit : leftLeaves ++ rightLeaves = leaves :=
        List.take_append_drop split leaves
      have hdegree : root.poly.size - 1 = leafDegreeSum leaves := by
        have hleftPos : 0 < left.node.root.poly.size := by
          apply Nat.pos_of_ne_zero
          intro hz
          exact left.node.root.ne ((size_eq_zero_iff _).mp hz)
        have hrightPos : 0 < right.node.root.poly.size := by
          apply Nat.pos_of_ne_zero
          intro hz
          exact right.node.root.ne ((size_eq_zero_iff _).mp hz)
        have hproduct := size_mul_of_top_ne left.node.root.poly
          right.node.root.poly hleftPos hrightPos (by
          rw [leadingCoeff_eq_one_of_monic left.node.root.monic,
            leadingCoeff_eq_one_of_monic right.node.root.monic]
          have hzero : (Zero.zero : R) = 0 := rfl
          rw [hzero, Lean.Grind.Semiring.one_mul]
          exact hone)
        rw [hroot, hproduct]
        rw [← hsplit, leafDegreeSum_append]
        rw [← left.degree_eq, ← right.degree_eq]
        omega
      have hrootDegree : root.poly.size - 1 =
          (left.node.root.poly.size - 1) +
            (right.node.root.poly.size - 1) := by
        rw [hdegree, ← hsplit, leafDegreeSum_append,
          ← left.degree_eq, ← right.degree_eq]
      { node
        leaves_eq := by
          dsimp [node, RemainderNode.leaves]
          rw [left.leaves_eq, right.leaves_eq, hsplit]
        capacity_eq := by
          change plan.capacity = capacity
          simp [plan]
        degree_eq := hdegree
        wellFormed := .branch root plan _ left.node right.node
          left.wellFormed right.wellFormed hleftDvd hrightDvd
          hrootDegree hleftCapacity hrightCapacity }
  termination_by leaves => leaves.length
  decreasing_by
    all_goals
      simp only [List.length_take, List.length_drop, List.length_cons]
      have hsplitPos := treeSplit_pos (rest.length + 1 + 1)
      have hsplitLt := treeSplit_lt (rest.length + 1 + 1) (by omega)
      omega

/-- An opaque balanced remainder tree whose root has fixed reciprocal capacity
and whose proper nodes use the degree of their sibling subtree. -/
structure RemainderTree (R : Type u) [DecidableEq R]
    [Lean.Grind.CommRing R] where
  private mulData : MulPlan R
  private capacityData : Nat
  private leavesData : Array (MonicLeaf R)
  private nodeData : Option (RemainderNode R)
  private nodeLeaves : ∀ node, nodeData = some node →
    node.leaves = leavesData.toList
  private nodeWellFormed : ∀ node, nodeData = some node → node.WellFormed
  private nodeCapacity : ∀ node, nodeData = some node →
    node.plan.capacity = capacityData
  private nodeDegree : ∀ node, nodeData = some node →
    node.root.poly.size - 1 = leafDegreeSum leavesData.toList
  private noNodeLeaves : nodeData = none → leavesData.toList = []

namespace RemainderTree

/-- Build a cached remainder tree. `capacity` is the reciprocal capacity of the
root; every proper node derives the exact worst-case capacity it needs from its
sibling subtree. The empty leaf sequence is represented without an internal
root. -/
def build (mul : MulPlan R) (capacity : Nat) (leaves : Array (MonicLeaf R))
    (hone : (1 : R) ≠ 0) : RemainderTree R :=
  if hempty : leaves.toList = [] then
    { mulData := mul
      capacityData := capacity
      leavesData := leaves
      nodeData := none
      nodeLeaves := by intro node h; contradiction
      nodeWellFormed := by intro node h; contradiction
      nodeCapacity := by intro node h; contradiction
      nodeDegree := by intro node h; contradiction
      noNodeLeaves := by intro; exact hempty }
  else
    let built := buildRemainderNode mul capacity hone leaves.toList hempty
    { mulData := mul
      capacityData := capacity
      leavesData := leaves
      nodeData := some built.node
      nodeLeaves := by intro node h; cases h; exact built.leaves_eq
      nodeWellFormed := by intro node h; cases h; exact built.wellFormed
      nodeCapacity := by intro node h; cases h; exact built.capacity_eq
      nodeDegree := by intro node h; cases h; exact built.degree_eq
      noNodeLeaves := by intro h; contradiction }

/-- Leaf divisors in their original order. -/
def leaves (tree : RemainderTree R) : Array (DensePoly R) :=
  tree.leavesData.map (MonicLeaf.poly ·)

/-- Proof-carrying leaf entries in their original order. -/
def entries (tree : RemainderTree R) : Array (MonicLeaf R) :=
  tree.leavesData

/-- Number of leaf divisors. -/
def size (tree : RemainderTree R) : Nat := tree.leavesData.size

/-- Reciprocal capacity cached at the root. -/
def capacity (tree : RemainderTree R) : Nat := tree.capacityData

/-- Degree of the root product, computed as the sum of the leaf degrees. -/
def rootDegree (tree : RemainderTree R) : Nat :=
  leafDegreeSum tree.leavesData.toList

private def reduceNode? (node : RemainderNode R)
    (p : DensePoly R) : Option (DensePoly R) :=
  if hcap : quotientLength p node.plan.divisor ≤ node.plan.capacity then
    some (node.plan.mod p hcap)
  else
    none

private theorem reduceNode?_sound (node : RemainderNode R)
    (p r : DensePoly R) (h : reduceNode? node p = some r) :
    node.root.poly ∣ p - r ∧ r.size ≤ node.root.poly.size - 1 := by
  unfold reduceNode? at h
  split at h
  · rename_i hcap
    injection h with hr
    subst r
    constructor
    · refine ⟨node.plan.quotient p hcap, ?_⟩
      rw [node.plan.mod_eq p hcap, mulWith_eq, node.plan_divisor]
      rw [mul_comm_poly node.root.poly (node.plan.quotient p hcap)]
      apply ext_coeff
      intro i
      rw [coeff_sub_ring, coeff_sub_ring]
      grind
    · have hsize := node.plan.size_mod_le p hcap
      rw [node.plan_divisor] at hsize
      exact hsize
  · contradiction

private theorem dvd_trans_poly {a b c : DensePoly R}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  rw [hy, hx, mul_assoc_poly]

private theorem dvd_sub_chain {d a b c : DensePoly R}
    (hab : d ∣ a - b) (hbc : d ∣ b - c) : d ∣ a - c := by
  have hsum : a - c = (a - b) + (b - c) := by
    apply ext_coeff
    intro i
    rw [coeff_sub_ring, coeff_add_semiring, coeff_sub_ring, coeff_sub_ring]
    grind
  rw [hsum]
  exact dvd_add_poly hab hbc

private def runNode? : RemainderNode R →
    DensePoly R → Option (List (DensePoly R))
  | node@(.leaf ..), p => do
      let r ← reduceNode? node p
      pure [r]
  | node@(.branch _ _ _ left right), p => do
      let r ← reduceNode? node p
      let ls ← runNode? left r
      let rs ← runNode? right r
      pure (ls ++ rs)

private theorem quotientLength_le_capacity (p q : DensePoly R) (hq : q ≠ 0)
    {degree capacity : Nat} (hdegree : q.size - 1 = degree)
    (hsize : p.size ≤ degree + capacity) :
    quotientLength p q ≤ capacity := by
  have hqsize : q.size ≠ 0 := by
    intro hz
    exact hq ((size_eq_zero_iff q).mp hz)
  by_cases hp : p.size < q.size
  · simp [quotientLength_eq, hp]
  · rw [quotientLength_eq]
    simp [hqsize, hp]
    omega

private theorem runNode?_exists {node : RemainderNode R}
    (hwf : node.WellFormed) (p : DensePoly R)
    (hcap : quotientLength p node.plan.divisor ≤ node.plan.capacity) :
    ∃ results, runNode? node p = some results := by
  induction hwf generalizing p with
  | leaf entry plan hplan =>
      let current : RemainderNode R := .leaf entry plan hplan
      refine ⟨[current.plan.mod p hcap], ?_⟩
      have hred : reduceNode? current p = some (current.plan.mod p hcap) := by
        unfold reduceNode?
        rw [_root_.dite_eq_left hcap]
      simp [current, runNode?, hred]
  | branch root plan hplan left right hleft hright leftDvd rightDvd
      rootDegree leftCapacity rightCapacity leftIH rightIH =>
      let current : RemainderNode R := .branch root plan hplan left right
      let r := current.plan.mod p hcap
      have hrsize : r.size ≤ root.poly.size - 1 := by
        have hsize := current.plan.size_mod_le p hcap
        simpa [r, current, hplan, RemainderNode.plan] using hsize
      rw [rootDegree] at hrsize
      have hleftPos : 0 < left.root.poly.size := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact left.root.ne ((size_eq_zero_iff _).mp hz)
      have hrightPos : 0 < right.root.poly.size := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact right.root.ne ((size_eq_zero_iff _).mp hz)
      have hleftCap :
          quotientLength r left.plan.divisor ≤ left.plan.capacity := by
        rw [left.plan_divisor, leftCapacity]
        by_cases hr : r.size < left.root.poly.size
        · simp [quotientLength_eq, hr]
        · rw [quotientLength_eq]
          simp [Nat.ne_of_gt hleftPos, hr]
          omega
      have hrightCap :
          quotientLength r right.plan.divisor ≤ right.plan.capacity := by
        rw [right.plan_divisor, rightCapacity]
        by_cases hr : r.size < right.root.poly.size
        · simp [quotientLength_eq, hr]
        · rw [quotientLength_eq]
          simp [Nat.ne_of_gt hrightPos, hr]
          omega
      rcases leftIH r hleftCap with ⟨ls, hls⟩
      rcases rightIH r hrightCap with ⟨rs, hrs⟩
      refine ⟨ls ++ rs, ?_⟩
      have hred : reduceNode? current p = some r := by
        unfold reduceNode?
        rw [_root_.dite_eq_left hcap]
      simp [current, runNode?, hred, hls, hrs]

private theorem runNode?_sound {node : RemainderNode R}
    (hwf : node.WellFormed) (origin parent : DensePoly R)
    (hparent : node.root.poly ∣ origin - parent)
    (results : List (DensePoly R))
    (hrun : runNode? node parent = some results) :
    RemainderSpec origin node.leaves results := by
  induction hwf generalizing origin parent results with
  | leaf entry plan hplan =>
      cases hred : reduceNode? (.leaf entry plan hplan) parent with
      | none => simp [runNode?, hred] at hrun
      | some r =>
          have hresults : results = [r] := by
            simpa [runNode?, hred] using hrun.symm
          subst results
          have hs := reduceNode?_sound (.leaf entry plan hplan) parent r hred
          exact .cons ⟨dvd_sub_chain hparent hs.1, hs.2⟩ .nil
  | branch root plan hplan left right hleft hright leftDvd rightDvd
      rootDegree leftCapacity rightCapacity leftIH rightIH =>
      cases hred : reduceNode? (.branch root plan hplan left right) parent with
      | none => simp [runNode?, hred] at hrun
      | some r =>
          cases hls : runNode? left r with
          | none => simp [runNode?, hred, hls] at hrun
          | some ls =>
              cases hrs : runNode? right r with
              | none => simp [runNode?, hred, hls, hrs] at hrun
              | some rs =>
                  have hresults : results = ls ++ rs := by
                    simpa [runNode?, hred, hls, hrs] using hrun.symm
                  subst results
                  have hs := reduceNode?_sound
                    (.branch root plan hplan left right) parent r hred
                  have hroot : root.poly ∣ origin - r :=
                    dvd_sub_chain hparent hs.1
                  have hl : left.root.poly ∣ origin - r :=
                    dvd_trans_poly leftDvd hroot
                  have hr : right.root.poly ∣ origin - r :=
                    dvd_trans_poly rightDvd hroot
                  exact (leftIH origin r hl ls hls).append
                    (rightIH origin r hr rs hrs)

/-- Compute all leaf remainders with the cached reciprocal plans. Returns
`none` exactly when the input needs more reciprocal precision than the root
capacity. Proper-node capacities are sufficient by construction. -/
def remainders? (tree : RemainderTree R) (p : DensePoly R) :
    Option (Array (DensePoly R)) :=
  match tree.nodeData with
  | none => some #[]
  | some node => runNode? node p |>.map List.toArray

/-- A caller-supplied root capacity covering the input above the root degree
makes the entire traversal succeed. Every proper-node guard follows from the
sibling-degree capacities recorded by construction. -/
theorem remainders?_isSome_of_capacity (tree : RemainderTree R)
    (p : DensePoly R) (hcap : p.size ≤ tree.rootDegree + tree.capacity) :
    (tree.remainders? p).isSome := by
  unfold remainders?
  cases hnode : tree.nodeData with
  | none => simp
  | some node =>
      have hrootCap :
          quotientLength p node.plan.divisor ≤ node.plan.capacity := by
        rw [tree.nodeCapacity node hnode]
        exact quotientLength_le_capacity p node.plan.divisor
          (degree := tree.rootDegree) (capacity := tree.capacity) (by
          rw [node.plan_divisor]
          exact node.root.ne) (by
          rw [node.plan_divisor]
          simpa [rootDegree] using tree.nodeDegree node hnode) hcap
      rcases runNode?_exists (tree.nodeWellFormed node hnode) p hrootCap with
        ⟨results, hresults⟩
      simp [hresults]

/-- Every successful traversal returns, in leaf order, the canonical-size
remainder of the input modulo each leaf polynomial. -/
theorem remainders?_sound (tree : RemainderTree R) (p : DensePoly R)
    (results : Array (DensePoly R))
    (h : tree.remainders? p = some results) :
    RemainderSpec p tree.entries.toList results.toList := by
  unfold remainders? at h
  cases hnode : tree.nodeData with
  | none =>
      rw [hnode] at h
      have hresults : results = #[] := by simpa using h.symm
      subst results
      unfold entries
      rw [tree.noNodeLeaves hnode]
      exact .nil
  | some node =>
      rw [hnode] at h
      cases hrun : runNode? node p with
      | none => simp [hrun] at h
      | some rs =>
          have hresults : results = rs.toArray := by
            simpa [hrun] using h.symm
          subst results
          have hparent : node.root.poly ∣ p - p := by
            rw [Lean.Grind.AddCommGroup.sub_self]
            exact dvd_zero_poly _
          have hs := runNode?_sound (tree.nodeWellFormed node hnode)
            p p hparent rs hrun
          rw [tree.nodeLeaves node hnode] at hs
          simpa [entries] using hs

end RemainderTree

end Hex.DensePoly
