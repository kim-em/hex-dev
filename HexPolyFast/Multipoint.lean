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
Reusable multipoint evaluation plans.

The executable remainder tree stores one reciprocal plan for every proper
node of the point-product tree. Its capacity is the sibling subtree width,
which is the largest possible quotient length when reducing a parent remainder
into that node. Inputs larger than the point count use the total direct Horner
fallback.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- The monic linear factor vanishing at `a`. -/
def pointFactor (a : R) : DensePoly R :=
  ofList [0 - a, 1]

theorem pointFactor_eq (a : R) :
    pointFactor a = monomial 1 1 - C a := by
  apply ext_coeff
  intro i
  rw [pointFactor, coeff_ofList, coeff_sub_ring, coeff_monomial, coeff_C]
  cases i with
  | zero => simp; rfl
  | succ i =>
      cases i with
      | zero => simp; change (1 : R) = 1 - 0; grind
      | succ i => simp; change (0 : R) = 0 - 0; grind

theorem pointFactor_eval_at (a x : R) : (pointFactor a).eval x = x - a := by
  rw [pointFactor_eq, eval_sub_ring, eval_monomial_semiring, eval_C_semiring,
    Lean.Grind.Semiring.pow_one, Lean.Grind.Semiring.one_mul]

@[simp] theorem pointFactor_eval (a : R) : (pointFactor a).eval a = 0 := by
  rw [pointFactor_eval_at]
  grind

theorem pointFactor_size (a : R) (hone : (1 : R) ≠ 0) :
    (pointFactor a).size = 2 := by
  apply Nat.le_antisymm
  · exact size_ofList_le _
  · by_cases hle : 2 ≤ (pointFactor a).size
    · exact hle
    · have hz := coeff_eq_zero_of_size_le (pointFactor a) (i := 1) (by omega)
      rw [pointFactor, coeff_ofList] at hz
      simp at hz
      exact False.elim (hone hz)

omit [DecidableEq R] in
private theorem eqZeroOfOneEqZero (h : (1 : R) = 0) (a : R) : a = 0 := by
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
    _ = a * 0 := by rw [h]
    _ = 0 := Lean.Grind.Semiring.mul_zero a

theorem pointFactor_monic (a : R) : (pointFactor a).Monic := by
  by_cases h : (1 : R) = 0
  · rw [monic_iff_leadingCoeff_eq_one, h]
    exact eqZeroOfOneEqZero h _
  · rw [monic_iff_leadingCoeff_eq_one,
      leadingCoeff_eq_coeff_last _ (by rw [pointFactor_size a h]; omega),
      pointFactor_size a h]
    rw [pointFactor, coeff_ofList]
    simp

/-- Internal balanced remainder-tree shape, indexed by its exact point sequence
and product polynomial. Public clients use it only through opaque plans. -/
inductive PointNode (R : Type u) [DecidableEq R]
    [Lean.Grind.CommRing R] (mul : MulPlan R) :
    List R → DensePoly R → Type u where
  | leaf (a : R) : PointNode R mul [a] (pointFactor a)
  | branch {leftPoints rightPoints : List R}
      {leftPoly rightPoly : DensePoly R}
      (left : PointNode R mul leftPoints leftPoly)
      (right : PointNode R mul rightPoints rightPoly)
      (leftPlan rightPlan : DivPlan R)
      (leftZero : ∀ a, a ∈ leftPoints → leftPlan.divisor.eval a = 0)
      (rightZero : ∀ a, a ∈ rightPoints → rightPlan.divisor.eval a = 0) :
      PointNode R mul (leftPoints ++ rightPoints)
        (mulWith mul leftPoly rightPoly)

/-- A constructed node together with its monic product polynomial. -/
private structure BuiltNode (mul : MulPlan R) (points : List R) where
  poly : DensePoly R
  node : PointNode R mul points poly
  monic : poly.Monic
  ne : poly ≠ 0
  evalZero : ∀ a, a ∈ points → poly.eval a = 0

private def leafNode (mul : MulPlan R) (hone : (1 : R) ≠ 0) (a : R) :
    BuiltNode mul [a] :=
  { poly := pointFactor a
    node := .leaf a
    monic := pointFactor_monic a
    ne := (pointFactor_monic a).neOfOneNe hone
    evalZero := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact pointFactor_eval a }

private def branchNode (mul : MulPlan R) (hone : (1 : R) ≠ 0)
    {leftPoints rightPoints : List R}
    (left : BuiltNode mul leftPoints) (right : BuiltNode mul rightPoints) :
    BuiltNode mul (leftPoints ++ rightPoints) :=
  let leftPlan := DivPlan.ofMonic mul left.poly left.monic left.ne rightPoints.length
  let rightPlan := DivPlan.ofMonic mul right.poly right.monic right.ne leftPoints.length
  let poly := mulWith mul left.poly right.poly
  { poly
    node := .branch left.node right.node leftPlan rightPlan
      (by intro a ha; simpa [leftPlan] using left.evalZero a ha)
      (by intro a ha; simpa [rightPlan] using right.evalZero a ha)
    monic := by
      dsimp [poly]
      rw [mulWith_eq]
      exact left.monic.mul right.monic
    ne := by
      apply Monic.neOfOneNe
      · dsimp [poly]
        rw [mulWith_eq]
        exact left.monic.mul right.monic
      · exact hone
    evalZero := by
      intro a ha
      dsimp [poly]
      rw [mulWith_eq, eval_mul_commring]
      rw [List.mem_append] at ha
      cases ha with
      | inl hleft => rw [left.evalZero a hleft]; grind
      | inr hright => rw [right.evalZero a hright]; grind }

/-- Recursively build a count-balanced cached remainder tree. -/
private def buildNode (mul : MulPlan R) (hone : (1 : R) ≠ 0) :
    (points : List R) → points ≠ [] → BuiltNode mul points
  | [], hne => False.elim (hne rfl)
  | [a], _ => leafNode mul hone a
  | a :: b :: rest, _ =>
      let points := a :: b :: rest
      let split := treeSplit points.length
      have splitPos : 0 < split := treeSplit_pos points.length
      have splitLt : split < points.length := treeSplit_lt points.length (by
        dsimp [points]
        simp)
      let leftPoints := points.take split
      let rightPoints := points.drop split
      let left := buildNode mul hone leftPoints (by
        intro hnil
        have hz := congrArg List.length hnil
        dsimp [leftPoints] at hz
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt splitLt)] at hz
        omega)
      let right := buildNode mul hone rightPoints (by
        intro hnil
        have hz := congrArg List.length hnil
        dsimp [rightPoints] at hz
        rw [List.length_drop] at hz
        omega)
      have hsplit : leftPoints ++ rightPoints = a :: b :: rest := by
        simpa only [leftPoints, rightPoints, points] using
          List.take_append_drop split points
      have built : BuiltNode mul (leftPoints ++ rightPoints) :=
        branchNode mul hone left right
      hsplit ▸ built
  termination_by points => points.length
  decreasing_by
    all_goals
      simp only [List.length_take, List.length_drop, List.length_cons]
      have hsplitPos := treeSplit_pos (rest.length + 1 + 1)
      have hsplitLt := treeSplit_lt (rest.length + 1 + 1) (by omega)
      omega

/-- An opaque reusable multipoint-evaluation plan. -/
structure EvalPlan (R : Type u) [DecidableEq R] [Lean.Grind.CommRing R] where
  private mulData : MulPlan R
  private pointsData : Array R
  /-- Empty and trivial-ring plans use `none`; otherwise the type index ties
  every cached divisor to the exact public point sequence. -/
  private nodeData : Option
    (Sigma fun poly => PointNode R mulData pointsData.toList poly)

namespace EvalPlan

/-- Build the point-product tree and all finite-capacity reciprocal plans. -/
def build (mul : MulPlan R) (points : Array R) : EvalPlan R :=
  { mulData := mul
    pointsData := points
    nodeData := if hone : (1 : R) = 0 then none
      else if hempty : points.toList = [] then none
      else
        let built := buildNode mul hone points.toList hempty
        some ⟨built.poly, built.node⟩ }

/-- The planned point sequence. -/
def points (plan : EvalPlan R) : Array R := plan.pointsData

/-- Building an evaluation plan preserves the supplied point sequence. -/
@[simp] theorem points_build (mul : MulPlan R) (points : Array R) :
    (build mul points).points = points := by
  rfl

/-- Number of planned points. -/
def size (plan : EvalPlan R) : Nat := plan.points.size

/-- Lawful multiplication plan used by the cached tree. -/
def mulPlan (plan : EvalPlan R) : MulPlan R := plan.mulData

/-- The cached indexed tree, when the point sequence and coefficient ring are
nondegenerate. -/
def cachedNode (plan : EvalPlan R) : Option
    (Sigma fun poly => PointNode R plan.mulPlan plan.points.toList poly) :=
  plan.nodeData

/-- A nonempty point sequence over a nontrivial ring has a cached node. -/
theorem cachedNode_build_isSome (mul : MulPlan R) (points : Array R)
    (hone : (1 : R) ≠ 0) (hne : points.toList ≠ []) :
    (build mul points).cachedNode.isSome := by
  simp [cachedNode, mulPlan, build, hone, hne]
  rfl

/-- Rebuild the observational product-tree view. Constructing an evaluation
plan does not eagerly build this redundant level representation. -/
def treeView (plan : EvalPlan R) : ProductTree R :=
  ProductTree.build plan.mulPlan (plan.points.map pointFactor)

/-- Specification of multipoint evaluation.  The compiled implementation
below replaces this direct map by the cached remainder tree. -/
noncomputable def eval (plan : EvalPlan R) (f : DensePoly R) : Array R :=
  plan.points.map (f.eval ·)

/-- Evaluation preserves the planned point count. -/
@[simp] theorem size_eval (plan : EvalPlan R) (f : DensePoly R) :
    (plan.eval f).size = plan.size := by
  unfold eval size
  simp

/-- The points accessor has the advertised plan size. -/
@[simp] theorem size_points (plan : EvalPlan R) : plan.points.size = plan.size := by
  rfl

/-- Semantic expansion of the evaluation specification. -/
theorem eval_eq_map (plan : EvalPlan R) (f : DensePoly R) :
    plan.eval f = plan.points.map (f.eval ·) := by
  rfl

/-- Reduce one parent remainder into a cached child node.  The capacity guard
is executable defensive checking; plans built by `build` satisfy it throughout
the bounded traversal. -/
private def reduceNode (parent : DensePoly R) (node : DivPlan R) : DensePoly R :=
  if hcap : quotientLength parent node.divisor ≤ node.capacity then
    node.mod parent hcap
  else
    parent

/-- Reduction by a divisor vanishing at `a` preserves evaluation at `a`. -/
private theorem eval_reduceNode (parent : DensePoly R) (node : DivPlan R) (a : R)
    (hzero : node.divisor.eval a = 0) :
    (reduceNode parent node).eval a = parent.eval a := by
  unfold reduceNode
  split
  · rename_i hcap
    rw [node.mod_eq parent hcap]
    simp only [eval_sub_ring, mulWith_eq, eval_mul_commring, hzero,
      Lean.Grind.Semiring.mul_zero]
    grind
  · rfl

/-- Execute the balanced remainder tree, preserving left-to-right point order. -/
private def evalNode {points : List R} {poly : DensePoly R} :
    PointNode R plan points poly → DensePoly R → List R
  | .leaf a, f => [f.eval a]
  | .branch left right leftPlan rightPlan _ _, f =>
      evalNode left (reduceNode f leftPlan) ++
        evalNode right (reduceNode f rightPlan)

private theorem evalNode_eq {points : List R} {poly : DensePoly R}
    (node : PointNode R plan points poly)
    (f : DensePoly R) : evalNode node f = points.map (f.eval ·) := by
  induction node generalizing f with
  | leaf a => rfl
  | @branch leftPoints rightPoints leftPoly rightPoly left right leftPlan rightPlan
      leftZero rightZero leftIH rightIH =>
      simp only [evalNode, List.map_append]
      rw [leftIH, rightIH]
      have hleft : leftPoints.map ((reduceNode f leftPlan).eval ·) =
          leftPoints.map (f.eval ·) := by
        apply List.map_congr_left
        intro a ha
        exact eval_reduceNode f leftPlan a (leftZero a ha)
      have hright : rightPoints.map ((reduceNode f rightPlan).eval ·) =
          rightPoints.map (f.eval ·) := by
        apply List.map_congr_left
        intro a ha
        exact eval_reduceNode f rightPlan a (rightZero a ha)
      rw [hleft, hright]

/-- Executable cached remainder-tree evaluation.  Oversized inputs and the
degenerate ring use direct Horner evaluation, exactly as specified. -/
def evalImpl (plan : EvalPlan R) (f : DensePoly R) : Array R :=
  if f.size ≤ plan.size then
    match plan.nodeData with
    | none => plan.points.map (f.eval ·)
    | some built => (evalNode built.2 f).toArray
  else
    plan.points.map (f.eval ·)

/-- The cached implementation agrees exactly with direct evaluation. -/
theorem eval_eq_impl (plan : EvalPlan R) (f : DensePoly R) :
    plan.eval f = plan.evalImpl f := by
  rw [eval_eq_map]
  unfold evalImpl
  split
  · cases hnode : plan.nodeData with
    | none => rfl
    | some built =>
        simp only
        rw [evalNode_eq built.2 f]
        unfold points
        rw [← Array.toList_map, Array.toArray_toList]
  · rfl

/-- Compile multipoint evaluation through the cached remainder tree. -/
@[csimp] theorem eval_csimp : @EvalPlan.eval = @EvalPlan.evalImpl := by
  funext R instDecEq instRing plan f
  exact eval_eq_impl plan f

/-- Every output entry is evaluation at the corresponding planned point. -/
theorem get_eval (plan : EvalPlan R) (f : DensePoly R) (i : Nat)
    (hi : i < plan.size) :
    (plan.eval f)[i]'(by rw [size_eval]; exact hi) =
      f.eval ((plan.points)[i]'(by rw [size_points]; exact hi)) := by
  rw [Array.getElem_eq_getD (0 : R), Array.getElem_eq_getD (0 : R),
    eval_eq_map]
  simp [hi]

end EvalPlan

end Hex.DensePoly
