/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Multipoint

public section
set_option backward.proofsInPublic true

/-!
Reusable fast interpolation plans.

Construction rejects repeated points, evaluates the derivative of the point
product through the cached remainder tree, and stores its pointwise inverses.
Interpolation then combines weighted leaves bottom-up through a balanced tree.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat
attribute [local instance 1100] Lean.Grind.Semiring.natCast

variable {F : Type u} [DecidableEq F] [Lean.Grind.Field F]

/-- Combine weighted Lagrange numerators through the cached balanced shape. -/
private def combineNode (mul : MulPlan F) {points : List F} {poly : DensePoly F}
    (node : PointNode F mul points poly) (weights : List F) : DensePoly F :=
  match node with
  | .leaf _ => C (weights.getD 0 0)
  | @PointNode.branch _ _ _ _ leftPoints _ leftPoly rightPoly
      left right _ _ _ _ =>
      let leftWeights := weights.take leftPoints.length
      let rightWeights := weights.drop leftPoints.length
      mulWith mul (combineNode mul left leftWeights) rightPoly +
        mulWith mul (combineNode mul right rightWeights) leftPoly

omit [DecidableEq F] in
private theorem field_mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro h
  have h' := congrArg (fun x : F => x * b⁻¹) h
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Field.mul_inv_cancel hb,
    Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.zero_mul] at h'
  exact ha h'

private theorem derivative_pointFactor (a : F) : derivative (pointFactor a) = 1 := by
  apply ext_coeff
  intro i
  change (derivative (pointFactor a)).coeff i = (C 1).coeff i
  rw [coeff_derivative_semiring, coeff_C, pointFactor_eq,
    coeff_sub_ring, coeff_monomial, coeff_C]
  by_cases hi : i = 0
  · subst i
    simp only [Nat.zero_add, ↓reduceIte]
    rw [ite_eq_right Nat.one_ne_zero]
    rw [Lean.Grind.Semiring.natCast_one, Lean.Grind.Semiring.one_mul,
      Lean.Grind.Ring.sub_eq_add_neg]
    change (1 : F) + -(0 : F) = 1
    rw [Lean.Grind.AddCommGroup.neg_zero, Lean.Grind.Semiring.add_zero]
  · have hsucc : i + 1 ≠ 1 := by omega
    simp only [hsucc, hi, ↓reduceIte]
    have hpos : i + 1 ≠ 0 := by omega
    rw [ite_eq_right hpos]
    have hz : (0 : F) - 0 = 0 := SubZeroLaw.sub_zero_zero
    change ((i + 1 : Nat) : F) * ((0 : F) - 0) = 0
    rw [hz, Lean.Grind.Semiring.mul_zero]

private theorem PointNode.eval_zero (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly) (a : F)
    (ha : a ∈ points) : poly.eval a = 0 := by
  induction node with
  | leaf x =>
      simp only [List.mem_singleton] at ha
      subst a
      exact pointFactor_eval x
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      rw [mulWith_eq, eval_mul_commring]
      rw [List.mem_append] at ha
      cases ha with
      | inl hleft => rw [leftIH hleft, Lean.Grind.Semiring.zero_mul]
      | inr hright => rw [rightIH hright, Lean.Grind.Semiring.mul_zero]

private theorem PointNode.eval_ne (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly) (a : F)
    (ha : a ∉ points) : poly.eval a ≠ 0 := by
  induction node with
  | leaf x =>
      rw [pointFactor_eval_at]
      intro hz
      apply ha
      simp only [List.mem_singleton]
      grind
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      rw [mulWith_eq, eval_mul_commring]
      apply field_mul_ne_zero
      · have hparts : a ∉ leftPoints ∧ a ∉ rightPoints := by simpa using ha
        exact leftIH hparts.1
      · have hparts : a ∉ leftPoints ∧ a ∉ rightPoints := by simpa using ha
        exact rightIH hparts.2

private theorem PointNode.derivative_ne (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly)
    (hdistinct : points.Nodup) (a : F) (ha : a ∈ points) :
    (derivative poly).eval a ≠ 0 := by
  induction node with
  | leaf x =>
      rw [derivative_pointFactor, show (1 : DensePoly F) = C 1 by rfl,
        eval_C_semiring]
      exact fun h => Lean.Grind.Field.zero_ne_one h.symm
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      rcases List.nodup_append.mp hdistinct with ⟨hleftDistinct, hrightDistinct, hdisjoint⟩
      rw [List.mem_append] at ha
      rw [mulWith_eq, derivative_mul, eval_add_semiring,
        eval_mul_commring, eval_mul_commring]
      cases ha with
      | inl hleft =>
          have hright : a ∉ rightPoints := by
            intro hmem
            exact hdisjoint a hleft a hmem rfl
          rw [PointNode.eval_zero mul left a hleft, Lean.Grind.Semiring.zero_mul,
            Lean.Grind.Semiring.add_zero]
          exact field_mul_ne_zero
            (leftIH hleftDistinct hleft) (PointNode.eval_ne mul right a hright)
      | inr hright =>
          have hleft : a ∉ leftPoints := by
            intro hmem
            exact hdisjoint a hmem a hright rfl
          rw [PointNode.eval_zero mul right a hright, Lean.Grind.Semiring.mul_zero]
          rw [show (0 : F) + leftPoly.eval a * (derivative rightPoly).eval a =
            leftPoly.eval a * (derivative rightPoly).eval a by grind]
          exact field_mul_ne_zero
            (PointNode.eval_ne mul left a hleft) (rightIH hrightDistinct hright)

private theorem combineNode_eval (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly)
    (weights : List F) (hlen : weights.length = points.length)
    (hdistinct : points.Nodup) (i : Nat) (hi : i < points.length) :
    (combineNode mul node weights).eval points[i] =
      weights[i]'(by omega) * (derivative poly).eval points[i] := by
  induction node generalizing weights i with
  | leaf a =>
      have hi0 : i = 0 := by simp at hi; omega
      subst i
      simp only [combineNode, List.getElem_cons_zero,
        eval_C_semiring, derivative_pointFactor]
      rw [show (1 : DensePoly F) = C 1 by rfl, eval_C_semiring,
        Lean.Grind.Semiring.mul_one]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
      simp
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      rcases List.nodup_append.mp hdistinct with
        ⟨hleftDistinct, hrightDistinct, hdisjoint⟩
      have hleftLe : leftPoints.length ≤ weights.length := by
        rw [hlen, List.length_append]
        omega
      by_cases hindex : i < leftPoints.length
      · have hleftWeights : (weights.take leftPoints.length).length = leftPoints.length := by
          rw [List.length_take, Nat.min_eq_left hleftLe]
        have hleftEval := leftIH (weights.take leftPoints.length) hleftWeights
          hleftDistinct i hindex
        have hpoint : (leftPoints ++ rightPoints)[i] = leftPoints[i] := by
          exact List.getElem_append_left hindex
        have hweight : (weights.take leftPoints.length)[i] = weights[i] := by
          exact List.getElem_take
        simp only [combineNode]
        rw [eval_add_semiring, mulWith_eq, mulWith_eq,
          eval_mul_commring, eval_mul_commring, hpoint, hleftEval, hweight,
          PointNode.eval_zero mul left leftPoints[i] (List.getElem_mem ..),
          Lean.Grind.Semiring.mul_zero]
        rw [show (0 : F) = 0 * rightPoly.eval leftPoints[i] by
          rw [Lean.Grind.Semiring.zero_mul]]
        rw [mulWith_eq, derivative_mul, eval_add_semiring,
          eval_mul_commring, eval_mul_commring,
          PointNode.eval_zero mul left leftPoints[i] (List.getElem_mem ..),
          Lean.Grind.Semiring.zero_mul]
        grind
      · have hrightIndex : i - leftPoints.length < rightPoints.length := by
          simp only [List.length_append] at hi
          omega
        have hrightWeights : (weights.drop leftPoints.length).length = rightPoints.length := by
          rw [List.length_drop, hlen, List.length_append]
          omega
        have hrightEval := rightIH (weights.drop leftPoints.length) hrightWeights
          hrightDistinct (i - leftPoints.length) hrightIndex
        have hpoint : (leftPoints ++ rightPoints)[i] =
            rightPoints[i - leftPoints.length] := by
          exact List.getElem_append_right (Nat.le_of_not_gt hindex)
        have hweight : (weights.drop leftPoints.length)[i - leftPoints.length] =
            weights[i] := by
          rw [List.getElem_drop]
          congr
          omega
        simp only [combineNode]
        rw [eval_add_semiring, mulWith_eq, mulWith_eq,
          eval_mul_commring, eval_mul_commring, hpoint, hrightEval, hweight,
          PointNode.eval_zero mul right rightPoints[i - leftPoints.length]
            (List.getElem_mem ..), Lean.Grind.Semiring.mul_zero]
        rw [show (0 : F) +
            (weights[i] * (derivative rightPoly).eval rightPoints[i - leftPoints.length]) *
              leftPoly.eval rightPoints[i - leftPoints.length] =
            (weights[i] * (derivative rightPoly).eval rightPoints[i - leftPoints.length]) *
              leftPoly.eval rightPoints[i - leftPoints.length] by grind]
        rw [mulWith_eq, derivative_mul, eval_add_semiring,
          eval_mul_commring, eval_mul_commring,
          PointNode.eval_zero mul right rightPoints[i - leftPoints.length]
            (List.getElem_mem ..), Lean.Grind.Semiring.mul_zero]
        grind

private theorem PointNode.poly_size (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly) :
    poly.size ≤ points.length + 1 := by
  induction node with
  | leaf a =>
      rw [pointFactor_size a (fun h => Lean.Grind.Field.zero_ne_one h.symm)]
      simp
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      rw [mulWith_eq]
      have hmul := size_mul_le leftPoly rightPoly
      simp only [List.length_append]
      omega

private theorem PointNode.combine_size (mul : MulPlan F) {points : List F}
    {poly : DensePoly F} (node : PointNode F mul points poly) (weights : List F) :
    (combineNode mul node weights).size ≤ points.length := by
  induction node generalizing weights with
  | leaf a => exact size_C_le_one _
  | @branch leftPoints rightPoints leftPoly rightPoly left right
      leftPlan rightPlan leftZero rightZero leftIH rightIH =>
      simp only [combineNode, List.length_append]
      have hleftPoly := PointNode.poly_size mul left
      have hrightPoly := PointNode.poly_size mul right
      have hleftTerm := size_mul_le
        (combineNode mul left (weights.take leftPoints.length)) rightPoly
      have hrightTerm := size_mul_le
        (combineNode mul right (weights.drop leftPoints.length)) leftPoly
      rw [← mulWith_eq mul] at hleftTerm hrightTerm
      have hadd := size_add_le_max
        (mulWith mul (combineNode mul left (weights.take leftPoints.length)) rightPoly)
        (mulWith mul (combineNode mul right (weights.drop leftPoints.length)) leftPoly)
      have hleft := leftIH (weights.take leftPoints.length)
      have hright := rightIH (weights.drop leftPoints.length)
      omega

private theorem eq_zero_of_size_le_one (p : DensePoly F) (a : F)
    (hsize : p.size ≤ 1) (heval : p.eval a = 0) : p = 0 := by
  have hp : p = C (p.coeff 0) := by
    apply ext_coeff
    intro i
    by_cases hi : i = 0
    · subst i
      rw [coeff_C]
      simp
    · rw [coeff_eq_zero_of_size_le p (by omega), coeff_C]
      simp [hi]
  rw [hp, eval_C_semiring] at heval
  rw [hp, heval]
  apply (size_eq_zero_iff (C (0 : F))).mp
  exact size_C_zero

omit [DecidableEq F] in
private theorem eq_zero_of_mul_right {x y : F} (hxy : x * y = 0)
    (hy : y ≠ 0) : x = 0 := by
  have h := congrArg (fun z : F => z * y⁻¹) hxy
  rw [Lean.Grind.Semiring.mul_assoc, Lean.Grind.Field.mul_inv_cancel hy,
    Lean.Grind.Semiring.mul_one, Lean.Grind.Semiring.zero_mul] at h
  exact h

private theorem eq_zero_of_roots (mul : MulPlan F) (points : List F)
    (hdistinct : points.Nodup) (p : DensePoly F)
    (hsize : p.size ≤ points.length)
    (hroots : ∀ a, a ∈ points → p.eval a = 0) : p = 0 := by
  induction points generalizing p with
  | nil =>
      apply (size_eq_zero_iff p).mp
      simpa using hsize
  | cons a rest ih =>
      simp only [List.length_cons] at hsize
      rcases List.nodup_cons.mp hdistinct with ⟨hanot, hrestDistinct⟩
      have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
      have hfactorSize : (pointFactor a).size = 2 := pointFactor_size a hone
      have hfactorNe : pointFactor a ≠ 0 := by
        intro hzero
        rw [hzero, size_zero] at hfactorSize
        omega
      let div := DivPlan.ofMonic mul (pointFactor a) (pointFactor_monic a)
        hfactorNe p.size
      have hcap : quotientLength p div.divisor ≤ div.capacity := by
        dsimp only [div]
        rw [DivPlan.divisor_ofMonic, DivPlan.capacity_ofMonic]
        rw [quotientLength_eq, hfactorSize]
        by_cases hp : p.size < 2
        · rw [ite_eq_left (by simp [hp])]
          omega
        · rw [ite_eq_right (by simp [hp])]
          omega
      have hrsize : (div.mod p hcap).size ≤ 1 := by
        have h := div.size_mod_le p hcap
        dsimp only [div] at h
        rw [DivPlan.divisor_ofMonic, hfactorSize] at h
        exact h
      have hreval : (div.mod p hcap).eval a = 0 := by
        have h := div.eval_mod p hcap a (by
          dsimp only [div]
          rw [DivPlan.divisor_ofMonic]
          exact pointFactor_eval a)
        rw [h, hroots a (by simp)]
      have hrzero : div.mod p hcap = 0 :=
        eq_zero_of_size_le_one (div.mod p hcap) a hrsize hreval
      have hfactorRaw :
          p = mulWith div.mul (div.quotient p hcap) div.divisor := by
        have hmod := div.mod_eq p hcap
        rw [hrzero] at hmod
        apply ext_coeff
        intro i
        have hc := congrArg (fun s : DensePoly F => s.coeff i) hmod
        simp only [coeff_zero, coeff_sub_ring] at hc
        grind
      have hfactor :
          p = mulWith mul (div.quotient p hcap) (pointFactor a) := by
        dsimp only [div] at hfactorRaw
        simpa only [DivPlan.mul_ofMonic, DivPlan.divisor_ofMonic] using hfactorRaw
      have hqsize : (div.quotient p hcap).size ≤ rest.length := by
        have hq := div.size_quotient_le p hcap
        have hdivisor : div.divisor = pointFactor a := by
          dsimp only [div]
          rw [DivPlan.divisor_ofMonic]
        rw [hdivisor] at hq
        rw [quotientLength_eq, hfactorSize] at hq
        by_cases hp : p.size < 2
        · rw [ite_eq_left (by simp [hp])] at hq
          omega
        · rw [ite_eq_right (by simp [hp])] at hq
          omega
      have hqroots : ∀ b, b ∈ rest → (div.quotient p hcap).eval b = 0 := by
        intro b hb
        have hpzero : p.eval b = 0 := hroots b (by simp [hb])
        rw [hfactor, mulWith_eq, eval_mul_commring, pointFactor_eval_at] at hpzero
        apply eq_zero_of_mul_right hpzero
        intro hba
        have hab : b = a := by grind
        exact hanot (hab ▸ hb)
      have hqzero := ih hrestDistinct (div.quotient p hcap) hqsize hqroots
      rw [hfactor, hqzero, mulWith_eq]
      exact zero_mul (pointFactor a)

/-- An opaque reusable interpolation plan at a distinct point sequence. -/
structure InterpPlan (F : Type u) [DecidableEq F] [Lean.Grind.Field F] where
  private mulData : MulPlan F
  private pointsData : Array F
  private evalData : EvalPlan F
  private nodeData : Option
    (Sigma fun poly => PointNode F mulData pointsData.toList poly)
  private invDerivData : Array F
  private distinctData : pointsData.toList.Nodup
  private evalPointsData : evalData.points = pointsData
  private emptyData : nodeData = none → pointsData.toList = []
  private invDerivSpec : ∀ built, nodeData = some built →
    invDerivData = (evalData.eval (derivative built.1)).map (fun x => x⁻¹)

namespace InterpPlan

/-- Build a reusable interpolation plan exactly when the points are distinct. -/
def build? (mul : MulPlan F) (points : Array F) : Option (InterpPlan F) :=
  if hdistinct : points.toList.Nodup then
    let evalPlan := EvalPlan.build mul points
    if hempty : points.toList = [] then
      some
        { mulData := evalPlan.mulPlan
          pointsData := evalPlan.points
          evalData := evalPlan
          nodeData := none
          invDerivData := #[]
          distinctData := by
            simpa only [evalPlan, EvalPlan.points_build] using hdistinct
          evalPointsData := rfl
          emptyData := fun _ => by
            simpa only [evalPlan, EvalPlan.points_build] using hempty
          invDerivSpec := by intro built h; contradiction }
    else
      have hone : (1 : F) ≠ 0 := fun h => Lean.Grind.Field.zero_ne_one h.symm
      have hnode : evalPlan.cachedNode.isSome := by
        simpa [evalPlan] using
          EvalPlan.cachedNode_build_isSome mul points hone hempty
      let built := evalPlan.cachedNode.get hnode
      let invDeriv := (evalPlan.eval (derivative built.1)).map (fun x => x⁻¹)
      some
        { mulData := evalPlan.mulPlan
          pointsData := evalPlan.points
          evalData := evalPlan
          nodeData := some built
          invDerivData := invDeriv
          distinctData := by
            simpa only [evalPlan, EvalPlan.points_build] using hdistinct
          evalPointsData := rfl
          emptyData := by intro h; contradiction
          invDerivSpec := by intro other h; cases h; rfl }
  else
    none

/-- Plan construction fails exactly when the point sequence has a duplicate. -/
theorem build?_eq_none_iff (mul : MulPlan F) (points : Array F) :
    build? mul points = none ↔ ¬points.toList.Nodup := by
  unfold build?
  split
  · rename_i hdistinct
    simp only
    split <;> simp [hdistinct]
  · simp_all

/-- Planned interpolation points. -/
def points (plan : InterpPlan F) : Array F := plan.pointsData

/-- Number of planned interpolation points. -/
def size (plan : InterpPlan F) : Nat := plan.points.size

/-- The points accessor has the advertised plan size. -/
@[simp] theorem size_points (plan : InterpPlan F) :
    plan.points.size = plan.size := by
  rfl

private theorem size_eq_data (plan : InterpPlan F) :
    plan.size = plan.pointsData.size := by
  rfl

private theorem points_eq_data (plan : InterpPlan F) :
    plan.points = plan.pointsData := by
  rfl

/-- The cached multipoint plan used for derivative evaluation. -/
def evalPlan (plan : InterpPlan F) : EvalPlan F := plan.evalData

/-- The nested evaluation plan uses the same point sequence. -/
@[simp] theorem evalPlan_points (plan : InterpPlan F) :
    plan.evalPlan.points = plan.points := by
  exact plan.evalPointsData

/-- The nested evaluation plan has the same size. -/
@[simp] theorem evalPlan_size (plan : InterpPlan F) :
    plan.evalPlan.size = plan.size := by
  rw [← EvalPlan.size_points, evalPlan_points, size_points]

/-- Interpolate a matching value array, rejecting only a count mismatch. -/
def interpolate? (plan : InterpPlan F) (values : Array F) : Option (DensePoly F) :=
  if values.size = plan.size then
    let weights := List.zipWith (· * ·) values.toList plan.invDerivData.toList
    match plan.nodeData with
    | none => some 0
    | some built => some (combineNode plan.mulData built.2 weights)
  else
    none

/-- Interpolation rejects exactly a mismatch between point and value counts. -/
theorem interpolate?_eq_none_iff (plan : InterpPlan F) (values : Array F) :
    plan.interpolate? values = none ↔ values.size ≠ plan.size := by
  unfold interpolate?
  split
  · rename_i hsize
    constructor
    · intro hnone
      cases hnode : plan.nodeData <;> simp [hnode] at hnone
    · intro hne
      exact False.elim (hne hsize)
  · rename_i hsize
    simp [hsize]

/-- A successful interpolation has the requested values and no more
coefficients than there are points. -/
theorem interpolate?_sound (plan : InterpPlan F) (values : Array F)
    (p : DensePoly F) (hsome : plan.interpolate? values = some p) :
    p.size ≤ plan.size ∧ ∀ i (hi : i < plan.size),
      p.eval ((plan.points)[i]'(by rw [size_points]; exact hi)) =
        values.getD i 0 := by
  have hcount : values.size = plan.size := by
    by_cases h : values.size = plan.size
    · exact h
    · have := (plan.interpolate?_eq_none_iff values).mpr h
      rw [hsome] at this
      contradiction
  unfold interpolate? at hsome
  rw [ite_eq_left hcount] at hsome
  cases hnode : plan.nodeData with
  | none =>
      have hempty := plan.emptyData hnode
      have hpoints : plan.pointsData.size = 0 := by
        rw [← Array.length_toList, hempty]
        rfl
      simp only [hnode] at hsome
      injection hsome with hp
      subst p
      constructor
      · rw [size_eq_data, hpoints]
        simp
      · intro i hi
        rw [size_eq_data, hpoints] at hi
        omega
  | some built =>
      have hcache := plan.invDerivSpec built hnode
      simp only [hnode] at hsome
      injection hsome with hp
      subst p
      let weights := List.zipWith (· * ·) values.toList plan.invDerivData.toList
      have hinvSize : plan.invDerivData.size = plan.size := by
        rw [hcache, Array.size_map, EvalPlan.size_eval]
        calc
          plan.evalData.size = plan.evalData.points.size :=
            (EvalPlan.size_points plan.evalData).symm
          _ = plan.pointsData.size := congrArg Array.size plan.evalPointsData
          _ = plan.size := (size_eq_data plan).symm
      have hweights : weights.length = plan.pointsData.toList.length := by
        dsimp [weights]
        rw [List.length_zipWith, Array.length_toList, Array.length_toList,
          hcount, hinvSize]
        rw [size_eq_data]
        simp
      constructor
      · rw [size_eq_data]
        simpa only [Array.length_toList] using
          PointNode.combine_size plan.mulData built.2 weights
      · intro i hi
        have hipoints : i < plan.pointsData.toList.length := by
          rw [Array.length_toList, ← size_eq_data]
          exact hi
        have heval := combineNode_eval plan.mulData built.2 weights hweights
          plan.distinctData i hipoints
        have heval' :
            (combineNode plan.mulData built.2 weights).eval
                ((plan.points)[i]'(by rw [size_points]; exact hi)) =
              weights[i]'(by rw [hweights]; exact hipoints) *
                (derivative built.1).eval plan.pointsData.toList[i] := by
          have hpointPlan :
              (plan.points)[i]'(by rw [size_points]; exact hi) =
                plan.pointsData.getD i 0 := by
            rw [Array.getElem_eq_getD (0 : F), points_eq_data]
          have hidata : i < plan.pointsData.size := by
            rw [← size_eq_data]
            exact hi
          have hpointList : plan.pointsData.toList[i] =
              plan.pointsData.getD i 0 := by
            calc
              plan.pointsData.toList[i] = plan.pointsData[i]'hidata := by
                simp only [Array.getElem_toList]
              _ = plan.pointsData.getD i 0 := Array.getElem_eq_getD (0 : F)
          calc
            (combineNode plan.mulData built.2 weights).eval
                ((plan.points)[i]'(by rw [size_points]; exact hi)) =
              (combineNode plan.mulData built.2 weights).eval
                (plan.pointsData.getD i 0) := congrArg _ hpointPlan
            _ = (combineNode plan.mulData built.2 weights).eval
                plan.pointsData.toList[i] := congrArg _ hpointList.symm
            _ = _ := heval
        have hderiv : (derivative built.1).eval plan.pointsData.toList[i] ≠ 0 :=
          PointNode.derivative_ne plan.mulData built.2 plan.distinctData
            plan.pointsData.toList[i] (List.getElem_mem ..)
        have hinvArray : plan.invDerivData[i]'(by rw [hinvSize]; exact hi) =
            ((derivative built.1).eval plan.pointsData.toList[i])⁻¹ := by
          have hevalSize : plan.evalData.size = plan.size := by
            calc
              plan.evalData.size = plan.evalData.points.size :=
                (EvalPlan.size_points plan.evalData).symm
              _ = plan.pointsData.size := congrArg Array.size plan.evalPointsData
              _ = plan.size := (size_eq_data plan).symm
          have hie : i < plan.evalData.size := by rw [hevalSize]; exact hi
          have hevalPoint := EvalPlan.get_eval plan.evalData (derivative built.1) i hie
          calc
            plan.invDerivData[i]'(by rw [hinvSize]; exact hi) =
                plan.invDerivData.getD i 0 := Array.getElem_eq_getD (0 : F)
            _ = ((plan.evalData.eval (derivative built.1)).map
                (fun x => x⁻¹)).getD i 0 := congrArg (fun xs : Array F => xs.getD i 0) hcache
            _ = ((plan.evalData.eval (derivative built.1)).map
                (fun x => x⁻¹))[i]'(by
                  simp only [Array.size_map, EvalPlan.size_eval]
                  exact hie) :=
              (Array.getElem_eq_getD (0 : F)).symm
            _ = ((derivative built.1).eval plan.pointsData.toList[i])⁻¹ := by
              rw [Array.getElem_map, hevalPoint]
              congr
              rw [plan.evalPointsData]
        have hinv : plan.invDerivData.toList[i]'(by
            rw [Array.length_toList, hinvSize]
            exact hi) =
            ((derivative built.1).eval plan.pointsData.toList[i])⁻¹ := by
          simpa only [Array.getElem_toList] using hinvArray
        have hweight : weights[i]'(by rw [hweights]; exact hipoints) =
            values[i]'(by rw [hcount]; exact hi) *
              ((derivative built.1).eval plan.pointsData.toList[i])⁻¹ := by
          dsimp [weights]
          rw [List.getElem_zipWith]
          simp only [Array.getElem_toList, hinv]
        rw [heval', hweight, Lean.Grind.Semiring.mul_assoc,
          Lean.Grind.Field.inv_mul_cancel hderiv, Lean.Grind.Semiring.mul_one]
        rw [← Array.getElem_eq_getD (0 : F)]

/-- The successful interpolation is the unique polynomial of size at most the
point count with the supplied values. -/
theorem interpolate?_unique (plan : InterpPlan F) (values : Array F)
    (p q : DensePoly F) (hsome : plan.interpolate? values = some p)
    (hqsize : q.size ≤ plan.size)
    (hqvalues : ∀ i (hi : i < plan.size),
      q.eval ((plan.points)[i]'(by rw [size_points]; exact hi)) = values.getD i 0) :
    q = p := by
  have hp := plan.interpolate?_sound values p hsome
  have hsubSize : (q - p).size ≤ plan.pointsData.toList.length := by
    have hsub := size_sub_le_max q p
    rw [Array.length_toList, ← size_eq_data]
    omega
  have hsubZero : q - p = 0 := by
    apply eq_zero_of_roots plan.mulData plan.pointsData.toList plan.distinctData
      (q - p) hsubSize
    intro a ha
    obtain ⟨i, hi, hpoint⟩ := List.getElem_of_mem ha
    have hip : i < plan.size := by
      rw [size_eq_data, ← Array.length_toList]
      exact hi
    have harray :
        (plan.points)[i]'(by rw [size_points]; exact hip) =
          plan.pointsData.toList[i] := by
      have hplan :
          (plan.points)[i]'(by rw [size_points]; exact hip) =
            plan.pointsData.getD i 0 := by
        rw [Array.getElem_eq_getD (0 : F), points_eq_data]
      have hdata : i < plan.pointsData.size := by
        rw [← Array.length_toList]
        exact hi
      have hlist : plan.pointsData.toList[i] = plan.pointsData.getD i 0 := by
        calc
          plan.pointsData.toList[i] = plan.pointsData[i]'hdata := by
            simp only [Array.getElem_toList]
          _ = plan.pointsData.getD i 0 := Array.getElem_eq_getD (0 : F)
      exact hplan.trans hlist.symm
    have hq := hqvalues i hip
    have hpvalue := hp.2 i hip
    rw [harray] at hq hpvalue
    subst a
    rw [eval_sub_ring]
    calc
      q.eval plan.pointsData.toList[i] - p.eval plan.pointsData.toList[i] =
          values.getD i 0 - p.eval plan.pointsData.toList[i] :=
        congrArg (fun x : F => x - p.eval plan.pointsData.toList[i]) hq
      _ = values.getD i 0 - values.getD i 0 :=
        congrArg (fun x : F => values.getD i 0 - x) hpvalue
      _ = 0 := by grind
  apply ext_coeff
  intro i
  have hc := congrArg (fun s : DensePoly F => s.coeff i) hsubZero
  simp only [coeff_sub_ring, coeff_zero] at hc
  grind

end InterpPlan

end Hex.DensePoly
