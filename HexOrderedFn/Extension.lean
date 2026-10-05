/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Real

/-!
Canonical rational-function fields indexed by a fixed real approximation provider,
with proof-founded total sign, comparison and derived coefficient bounds.
-/

@[expose] public section

namespace Hex.OrderedFn.Real

open Oracle
universe u
variable (K : Type u) [Lean.Grind.Field K] [DecidableEq K]

/-- A fixed provider with termination proofs for every field query. Semantic
validity is a separate companion theorem about the same provider and embedding. -/
structure Registration where
  /-- The exact fixed provider used by this registration's searches. -/
  source : Approximation K
  /-- Every fraction's total-sign search terminates from precision zero. -/
  signProgress : ∀ f : RationalFn K, Acc (Next (attempt source f)) 0
  /-- Every fraction's approximation search terminates at its normalized width. -/
  approxProgress : ∀ (f : RationalFn K) (δ : Rat),
    Acc (Next (approxAttempt source f (requestWidth δ))) 0

variable {K}

/-- The rational-function field carrying the order of one real registration. -/
structure Extension (r : Registration K) where
  /-- The canonical fraction, independent of approximation and semantic proofs. -/
  val : RationalFn K

namespace Extension

variable {r : Registration K}

/-- Registered values are equal exactly when their canonical fractions agree. -/
@[ext] theorem ext {f g : Extension r} (h : f.val = g.val) : f = g := by
  cases f; cases g; cases h; rfl

instance : DecidableEq (Extension r) := fun f g =>
  decidable_of_iff (f.val = g.val) ⟨ext, congrArg val⟩

instance : Lean.Grind.Field (Extension r) where
  add f g := ⟨f.val + g.val⟩
  mul f g := ⟨f.val * g.val⟩
  neg f := ⟨-f.val⟩
  sub f g := ⟨f.val - g.val⟩
  inv f := ⟨f.val⁻¹⟩
  div f g := ⟨f.val / g.val⟩
  natCast := ⟨fun n => ⟨Nat.cast n⟩⟩
  intCast := ⟨fun n => ⟨Int.cast n⟩⟩
  ofNat
    | 0 => ⟨⟨0⟩⟩
    | 1 => ⟨⟨1⟩⟩
    | n + 2 => ⟨⟨Nat.cast (n + 2)⟩⟩
  nsmul := ⟨fun n f => ⟨n • f.val⟩⟩
  zsmul := ⟨fun n f => ⟨n • f.val⟩⟩
  npow := ⟨fun f n => ⟨f.val ^ n⟩⟩
  zpow := ⟨fun f n => ⟨f.val ^ n⟩⟩
  add_zero f := ext (Lean.Grind.Semiring.add_zero f.val)
  add_comm f g := ext (Lean.Grind.Semiring.add_comm f.val g.val)
  add_assoc f g h := ext (Lean.Grind.Semiring.add_assoc f.val g.val h.val)
  mul_assoc f g h := ext (Lean.Grind.Semiring.mul_assoc f.val g.val h.val)
  mul_one f := ext (Lean.Grind.Semiring.mul_one f.val)
  one_mul f := ext (Lean.Grind.Semiring.one_mul f.val)
  left_distrib f g h := ext (Lean.Grind.Semiring.left_distrib f.val g.val h.val)
  right_distrib f g h := ext (Lean.Grind.Semiring.right_distrib f.val g.val h.val)
  zero_mul f := ext (Lean.Grind.Semiring.zero_mul f.val)
  mul_zero f := ext (Lean.Grind.Semiring.mul_zero f.val)
  pow_zero f := ext (Lean.Grind.Semiring.pow_zero f.val)
  pow_succ f n := ext (Lean.Grind.Semiring.pow_succ f.val n)
  ofNat_succ n := by
    cases n with
    | zero => exact ext (Lean.Grind.Semiring.ofNat_succ 0)
    | succ n => cases n with
      | zero => exact ext ((Lean.Grind.Semiring.ofNat_eq_natCast 2).symm.trans
          (Lean.Grind.Semiring.ofNat_succ 1))
      | succ n => exact ext (Lean.Grind.Semiring.natCast_succ (n + 2))
  ofNat_eq_natCast n := by
    cases n with
    | zero => exact ext (Lean.Grind.Semiring.ofNat_eq_natCast 0)
    | succ n => cases n with
      | zero => exact ext (Lean.Grind.Semiring.ofNat_eq_natCast 1)
      | succ n => rfl
  nsmul_eq_natCast_mul n f := ext (Lean.Grind.Semiring.nsmul_eq_natCast_mul n f.val)
  neg_add_cancel f := ext (Lean.Grind.Ring.neg_add_cancel f.val)
  sub_eq_add_neg f g := ext (Lean.Grind.Ring.sub_eq_add_neg f.val g.val)
  neg_zsmul n f := ext (Lean.Grind.Ring.neg_zsmul n f.val)
  zsmul_natCast_eq_nsmul n f := ext (Lean.Grind.Ring.zsmul_natCast_eq_nsmul n f.val)
  intCast_ofNat n := by
    cases n with
    | zero => exact ext (Lean.Grind.Ring.intCast_ofNat 0)
    | succ n => cases n with
      | zero => exact ext (Lean.Grind.Ring.intCast_ofNat 1)
      | succ n => exact ext (Lean.Grind.Ring.intCast_natCast (n + 2))
  intCast_neg n := ext (Lean.Grind.Ring.intCast_neg (α := RationalFn K) n)
  mul_comm f g := ext (Lean.Grind.CommSemiring.mul_comm f.val g.val)
  div_eq_mul_inv f g := ext (Lean.Grind.Field.div_eq_mul_inv f.val g.val)
  zpow_zero f := ext (Lean.Grind.Field.zpow_zero f.val)
  zpow_succ f n := ext (Lean.Grind.Field.zpow_succ f.val n)
  zpow_neg f n := ext (Lean.Grind.Field.zpow_neg f.val n)
  zero_ne_one h := RationalFn.zero_ne_one (congrArg val h)
  inv_zero := ext RationalFn.inv_zero
  mul_inv_cancel h := ext (RationalFn.mul_inv_cancel (fun he => h (ext he)))

/-- Include a predecessor coefficient. -/
def C (x : K) : Extension r := ⟨RationalFn.C x⟩

/-- The newly adjoined constant. -/
def X : Extension r := ⟨RationalFn.X⟩

/-- Including a predecessor coefficient stores its constant canonical fraction. -/
@[simp] theorem val_C (x : K) : (C (r := r) x).val = RationalFn.C x := rfl

/-- The registered indeterminate stores the canonical rational-function indeterminate. -/
@[simp] theorem val_X : (X : Extension r).val = RationalFn.X := rfl

/-- Total sign using this registration's fixed source. -/
def sign (f : Extension r) : Int := Real.sign r.source f.val (r.signProgress f.val)

/-- Refine a quotient enclosure to the requested width. -/
def approx (f : Extension r) (δ : Rat) : Bounds :=
  Real.approx r.source f.val δ (r.approxProgress f.val δ)

/-- Compare by the total sign of the difference. -/
def compare (f g : Extension r) : Ordering :=
  let s := sign (f - g)
  if s < 0 then .lt else if s = 0 then .eq else .gt

instance : LE (Extension r) := ⟨fun f g => sign (f - g) ≤ 0⟩
instance : LT (Extension r) := ⟨fun f g => sign (f - g) < 0⟩
instance : DecidableLE (Extension r) := fun _ _ => inferInstanceAs (Decidable (_ ≤ (0 : Int)))
instance : DecidableLT (Extension r) := fun _ _ => inferInstanceAs (Decidable (_ < (0 : Int)))

/-- Positive requests achieve their rational width bound. -/
theorem approx_width (f : Extension r) (δ : Rat) (hδ : 0 < δ) :
    (approx f δ).width ≤ δ := Real.approx_width _ _ _ _ hδ

/-- Copy a canonical fraction to another provider over the same coefficient
field. Preserving its order requires the companion's checked semantic hypotheses. -/
def transport (s : Registration K) (f : Extension r) : Extension s := ⟨f.val⟩

/-- Provider transport preserves the canonical fraction verbatim. -/
@[simp] theorem transport_val (s : Registration K) (f : Extension r) :
    (transport s f).val = f.val := rfl

/-- This level supplies the coefficient approximation for the next real level. -/
def approximation (constant : Rat → Bounds) : Approximation (Extension r) :=
  ⟨approx, constant⟩

/-- The derived provider meets positive widths when the new constant's provider does. -/
theorem approximation_width (constant : Rat → Bounds)
    (h : ∀ δ, 0 < δ → (constant δ).width ≤ δ) :
    ApproximationWidth (approximation (r := r) constant) where
  coeff := approx_width
  constant := h

end Extension
end Hex.OrderedFn.Real
