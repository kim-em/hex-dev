/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Extension
public import HexOrderedFnMathlib.Progress
public import Mathlib.Algebra.Field.TransferInstance

/-!
Real evaluation, order laws and provider transport for registered rational-function
extensions, together with correctness of their derived approximation providers.
-/

@[expose] public section

namespace Hex.OrderedFn.Real

open Oracle
universe u
variable {K : Type u} [Field K] [DecidableEq K]
variable {ι : K →+* ℝ} {τ : ℝ} {a : Approximation K}

/-- Semantic validity of this exact provider. The witnesses occur only in `Prop`. -/
def Valid (a : Approximation K) : Prop :=
  ∃ (ι : K →+* ℝ) (τ : ℝ),
    ApproximationCorrect ι τ a ∧ ApproximationWidth a ∧ RelativeTranscendence ι τ

/-- Register a provider with structurally erased semantic evidence. -/
def registration (h : Valid a) : Registration K where
  source := a
  signProgress f := by
    obtain ⟨ι, τ, ha, hw, ht⟩ := h
    exact sign_acc ha hw ht f 0
  approxProgress f δ := by
    obtain ⟨ι, τ, ha, hw, ht⟩ := h
    exact approx_acc ha hw ht f δ 0

/-- Registration uses precisely the provider whose semantic validity was proved. -/
@[simp] theorem registration_source (h : Valid a) : (registration h).source = a := rfl

namespace Extension

variable {r : Registration K}

/-- Forget the real registration while retaining the canonical fraction. -/
def equiv : Extension r ≃ RationalFn K where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Field laws transported through the canonical-fraction equivalence. -/
@[reducible] noncomputable def fieldModel : Field (Extension r) :=
  { equiv.field with
    sub f g := ⟨f.val - g.val⟩
    sub_eq_add_neg _ _ := rfl
    div f g := ⟨f.val / g.val⟩
    div_eq_mul_inv _ _ := rfl }

section

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Mathlib field structure using only the core arithmetic in its data fields. -/
instance field : Field (Extension r) where
  add := (· + ·)
  add_assoc := fieldModel.add_assoc
  zero := 0
  zero_add := fieldModel.zero_add
  add_zero := fieldModel.add_zero
  nsmul := fun n a => n • a
  nsmul_zero := fieldModel.nsmul_zero
  nsmul_succ := fieldModel.nsmul_succ
  add_comm := fieldModel.add_comm
  mul := (· * ·)
  mul_assoc := fieldModel.mul_assoc
  one := 1
  one_mul := fieldModel.one_mul
  mul_one := fieldModel.mul_one
  npow := fun n a => a ^ n
  npow_zero := fieldModel.npow_zero
  npow_succ := fieldModel.npow_succ
  zero_mul := fieldModel.zero_mul
  mul_zero := fieldModel.mul_zero
  left_distrib := fieldModel.left_distrib
  right_distrib := fieldModel.right_distrib
  natCast := Nat.cast
  natCast_zero := fieldModel.natCast_zero
  natCast_succ := fieldModel.natCast_succ
  neg := (- ·)
  sub := (· - ·)
  zsmul := fun n a => n • a
  sub_eq_add_neg := fieldModel.sub_eq_add_neg
  zsmul_zero' := fieldModel.zsmul_zero'
  zsmul_succ' := fieldModel.zsmul_succ'
  zsmul_neg' := fieldModel.zsmul_neg'
  neg_add_cancel := fieldModel.neg_add_cancel
  intCast := Int.cast
  intCast_ofNat := fieldModel.intCast_ofNat
  intCast_negSucc := fieldModel.intCast_negSucc
  mul_comm := fieldModel.mul_comm
  inv := (·⁻¹)
  div := (· / ·)
  zpow := fun n a => a ^ n
  div_eq_mul_inv := fieldModel.div_eq_mul_inv
  zpow_zero' := fieldModel.zpow_zero'
  zpow_succ' := fieldModel.zpow_succ'
  zpow_neg' := fieldModel.zpow_neg'
  exists_pair_ne := fieldModel.exists_pair_ne
  nnratCast := fun q => (Nat.cast q.num : Extension r) / Nat.cast q.den
  ratCast := fun q => (Int.cast q.num : Extension r) / Nat.cast q.den
  mul_inv_cancel := fieldModel.mul_inv_cancel
  inv_zero := fieldModel.inv_zero
  nnratCast_def := fieldModel.nnratCast_def
  nnqsmul := fun q a => ((Nat.cast q.num : Extension r) / Nat.cast q.den) * a
  nnqsmul_def := fieldModel.nnqsmul_def
  ratCast_def := fieldModel.ratCast_def
  qsmul := fun q a => ((Int.cast q.num : Extension r) / Nat.cast q.den) * a
  qsmul_def := fieldModel.qsmul_def

end

/-- The companion field induces precisely the core field operations and laws. -/
theorem coreField_eq : Field.toGrindField (K := Extension r) = instField := rfl

/-- The wrapper's field operations are those of its canonical fraction. -/
def valHom : Extension r →+* RationalFn K where
  toFun := val
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Real evaluation of the registered field. -/
noncomputable def evalHom (ht : RelativeTranscendence ι τ) : Extension r →+* ℝ :=
  (Real.evalHom ht).comp valHom

/-- The registered embedding evaluates the underlying canonical fraction. -/
theorem evalHom_apply (ht : RelativeTranscendence ι τ) (f : Extension r) :
    evalHom ht f = Real.eval ι τ f.val := Real.evalHom_apply ht f.val

/-- The registered total sign agrees with the real embedding, under containment
for its fixed provider and transcendence over the predecessor field. -/
theorem sign_eq (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) :
    sign f = sgn (evalHom ht f) := Real.sign_eq ha ht f.val _

/-- A registered predecessor constant evaluates through its specified embedding. -/
@[simp] theorem evalHom_C (ht : RelativeTranscendence ι τ) (c : K) :
    evalHom (r := r) ht (C c) = ι c := Real.evalHom_C ht c

/-- The registered indeterminate evaluates to the specified new real constant. -/
@[simp] theorem evalHom_X (ht : RelativeTranscendence ι τ) :
    evalHom (r := r) ht X = τ := Real.evalHom_X ht

/-- Total sign respects negation. -/
theorem sign_neg (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) : sign (-f) = -sign f := by
  rw [sign_eq ha ht, sign_eq ha ht, map_neg]
  simp only [sgn, Left.sign_neg, SignType.coe_neg]

/-- Total sign is multiplicative. -/
theorem sign_mul (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f g : Extension r) :
    sign (f * g) = sign f * sign g := by
  rw [sign_eq ha ht, sign_eq ha ht, sign_eq ha ht, map_mul]
  simp only [sgn, _root_.sign_mul, SignType.coe_mul]

/-- Formal zero is exactly zero under the total sign. -/
theorem sign_eq_zero_iff (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) : sign f = 0 ↔ f = 0 :=
  (Real.sign_eq_zero_iff ha ht f.val _).trans ⟨ext, congrArg val⟩

/-- A finite successful attempt proves the total sign without reducing its
accessibility argument. Containment is still required for this exact source. -/
theorem sign_of_attempt (ha : ApproximationCorrect ι τ r.source)
    (f : Extension r) {n : Nat} {s : Int} (hs : attempt r.source f.val n = some s) :
    sign f = s := Real.sign_of_attempt ha f.val _ hs

/-- Explicit comparison agrees with the real order. -/
theorem compare_eq (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f g : Extension r) :
    compare f g = compareOfLessAndEq (evalHom ht f) (evalHom ht g) := by
  unfold compare
  simp only [sign_eq ha ht]
  rw [map_sub (evalHom ht) f g]
  rcases lt_trichotomy (evalHom ht f) (evalHom ht g) with h | h | h
  · simp [compareOfLessAndEq, sgn, sub_neg.mpr h, h]
  · simp [compareOfLessAndEq, sgn, h]
  · simp [compareOfLessAndEq, sgn, sub_pos.mpr h, h.not_gt, h.ne']

/-- Strict negativity of the integer sign characterizes a negative real value. -/
private theorem sgn_neg_iff (x : ℝ) : sgn x < 0 ↔ x < 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [sgn, hx]
  · simp [sgn]
  · simp [sgn, hx, hx.not_gt]

/-- Nonpositivity of the integer sign characterizes a nonpositive real value. -/
private theorem sgn_nonpos_iff (x : ℝ) : sgn x ≤ 0 ↔ x ≤ 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [sgn, hx, hx.le]
  · simp [sgn]
  · simp [sgn, hx, hx.not_ge]

/-- Strict order agrees with real evaluation. -/
theorem eval_lt (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f g : Extension r) :
    f < g ↔ evalHom ht f < evalHom ht g := by
  change sign (f - g) < 0 ↔ _
  rw [sign_eq ha ht, sgn_neg_iff, map_sub, sub_neg]

/-- Nonstrict order agrees with real evaluation. -/
theorem eval_le (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f g : Extension r) :
    f ≤ g ↔ evalHom ht f ≤ evalHom ht g := by
  change sign (f - g) ≤ 0 ↔ _
  rw [sign_eq ha ht, sgn_nonpos_iff, map_sub, sub_nonpos]

/-- A positive total sign is exactly strict positivity in the registered order. -/
theorem sign_pos_iff (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) : sign f = 1 ↔ 0 < f := by
  rw [sign_eq ha ht, eval_lt ha ht, map_zero]
  rcases lt_trichotomy (evalHom ht f) 0 with h | h | h
  · simp [sgn, h, h.not_gt]
  · simp [sgn, h]
  · simp [sgn, h]

/-- A negative total sign is exactly strict negativity in the registered order. -/
theorem sign_neg_iff (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) : sign f = -1 ↔ f < 0 := by
  rw [sign_eq ha ht, eval_lt ha ht, map_zero]
  rcases lt_trichotomy (evalHom ht f) 0 with h | h | h
  · simp [sgn, h]
  · simp [sgn, h]
  · simp [sgn, h, h.not_gt]

/-- An order-preserving predecessor embedding preserves coefficient order. -/
theorem C_lt [LinearOrder K] (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (hι : StrictMono ι) (c d : K) :
    C (r := r) c < C d ↔ c < d := by
  rw [eval_lt ha ht, evalHom_C, evalHom_C, hι.lt_iff_lt]

/-- Semantic validity needed for the registered order. -/
def OrderValid (r : Registration K) : Prop :=
  ∃ (ι : K →+* ℝ) (τ : ℝ), ApproximationCorrect ι τ r.source ∧ RelativeTranscendence ι τ

/-- The order of a registered real extension is linear. Its data uses only the
core decisions; semantic witnesses occur solely inside the erased proof fields. -/
@[instance_reducible] def linearOrder (h : OrderValid r) : LinearOrder (Extension r) where
  le_refl f := by
    obtain ⟨ι, τ, ha, ht⟩ := h
    exact (eval_le ha ht f f).mpr le_rfl
  le_trans f g k hfg hgk := by
    obtain ⟨ι, τ, ha, ht⟩ := h
    exact (eval_le ha ht f k).mpr
      (((eval_le ha ht f g).mp hfg).trans ((eval_le ha ht g k).mp hgk))
  le_antisymm f g hfg hgf := by
    obtain ⟨ι, τ, ha, ht⟩ := h
    exact (evalHom ht).injective
      (le_antisymm ((eval_le ha ht f g).mp hfg) ((eval_le ha ht g f).mp hgf))
  le_total f g := by
    obtain ⟨ι, τ, ha, ht⟩ := h
    exact (le_total (evalHom ht f) (evalHom ht g)).imp
      (eval_le ha ht f g).mpr (eval_le ha ht g f).mpr
  lt_iff_le_not_ge f g := by
    obtain ⟨ι, τ, ha, ht⟩ := h
    rw [eval_lt ha ht, eval_le ha ht, eval_le ha ht, lt_iff_le_not_ge]
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance

/-- Real evaluation preserves the registered linear order. -/
theorem eval_strictMono (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) :
    let := linearOrder ⟨ι, τ, ha, ht⟩
    StrictMono (evalHom (r := r) ht) := by
  dsimp only
  intro f g hfg
  exact (eval_lt ha ht f g).mp hfg

/-- Field arithmetic preserves the registered real order. -/
theorem strictOrderedRing (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) :
    let := linearOrder ⟨ι, τ, ha, ht⟩
    IsStrictOrderedRing (Extension r) := by
  let := linearOrder ⟨ι, τ, ha, ht⟩
  exact Function.Injective.isStrictOrderedRing (evalHom ht) (map_zero _) (map_one _)
    (map_add _) (map_mul _) (fun {_ _} => (eval_le ha ht _ _).symm)
    (fun {_ _} => (eval_lt ha ht _ _).symm)

/-- Ordered-ring laws for consumers of the core field dictionary. -/
theorem orderedRing (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) :
    let := linearOrder ⟨ι, τ, ha, ht⟩
    Lean.Grind.OrderedRing (Extension r) := by
  let := linearOrder ⟨ι, τ, ha, ht⟩
  exact {
    add_le_left_iff := fun c => by
      rw [eval_le ha ht, eval_le ha ht, map_add, map_add, add_le_add_iff_right]
    zero_lt_one := (eval_lt ha ht 0 1).mpr (by simp)
    mul_lt_mul_of_pos_left := by
      intro f g c hfg hc
      apply (eval_lt ha ht _ _).mpr
      rw [map_mul, map_mul]
      exact mul_lt_mul_of_pos_left ((eval_lt ha ht _ _).mp hfg)
        (by simpa using (eval_lt ha ht 0 c).mp hc)
    mul_lt_mul_of_pos_right := by
      intro f g c hfg hc
      apply (eval_lt ha ht _ _).mpr
      rw [map_mul, map_mul]
      exact mul_lt_mul_of_pos_right ((eval_lt ha ht _ _).mp hfg)
        (by simpa using (eval_lt ha ht 0 c).mp hc) }

/-- Semantic validity supplies strict ordered-ring laws for the registered order,
without exposing the existential evaluation witnesses. -/
theorem OrderValid.strictOrderedRing (h : OrderValid r) :
    let := linearOrder h
    IsStrictOrderedRing (Extension r) := by
  obtain ⟨ι, τ, ha, ht⟩ := h
  exact Extension.strictOrderedRing ha ht

/-- Semantic validity supplies the core ordered-ring laws for the registered order. -/
theorem OrderValid.orderedRing (h : OrderValid r) :
    let := linearOrder h
    Lean.Grind.OrderedRing (Extension r) := by
  obtain ⟨ι, τ, ha, ht⟩ := h
  exact Extension.orderedRing ha ht

/-- Approximation containment is separate from the core requested-width theorem. -/
theorem approx_contains (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) (δ : Rat) :
    Contains (approx f δ) (evalHom ht f) := by
  rw [evalHom_apply]
  exact Real.approx_contains ha f.val δ _

/-- Changing providers for the same subject and embedding preserves evaluation. -/
theorem eval_transport (s : Registration K) (ht : RelativeTranscendence ι τ)
    (f : Extension r) : evalHom ht (transport s f) = evalHom ht f := rfl

/-- Provider transport preserves order only after both sources are checked
against the same predecessor embedding and new real constant. -/
theorem transport_lt (s : Registration K)
    (hr : ApproximationCorrect ι τ r.source) (hs : ApproximationCorrect ι τ s.source)
    (ht : RelativeTranscendence ι τ) (f g : Extension r) :
    transport s f < transport s g ↔ f < g := by
  rw [eval_lt hs ht, eval_transport, eval_transport, ← eval_lt hr ht]

/-- Finite sign proofs also transport with containment for the exact two sources. -/
theorem sign_transport (s : Registration K)
    (hr : ApproximationCorrect ι τ r.source) (hs : ApproximationCorrect ι τ s.source)
    (ht : RelativeTranscendence ι τ) (f : Extension r) :
    sign (transport s f) = sign f := by
  rw [sign_eq hs ht, eval_transport, sign_eq hr ht]

/-- The derived coefficient source refers to this same embedding and carrier. -/
theorem approximation_correct (ha : ApproximationCorrect ι τ r.source)
    (ht : RelativeTranscendence ι τ) (constant : Rat → Bounds) (σ : ℝ)
    (hc : ∀ δ, 0 < δ → Contains (constant δ) σ) :
    ApproximationCorrect (evalHom (r := r) ht) σ (approximation constant) where
  coeff f δ _ := approx_contains ha ht f δ
  constant := hc

end Extension

/-- A semantically valid provider gives its registered extension a valid order.
The width hypothesis is used to register total searches; order itself needs only
the same containment and relative-transcendence witnesses. -/
theorem Valid.orderValid (h : Valid a) : Extension.OrderValid (registration h) := by
  obtain ⟨ι, τ, ha, _, ht⟩ := h
  exact ⟨ι, τ, ha, ht⟩

end Hex.OrderedFn.Real
