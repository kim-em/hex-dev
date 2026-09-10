/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Field

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

/-- A point is regular when the canonical denominator does not vanish there. -/
@[expose]
def Regular (f : RationalFn K) (a : K) : Prop := f.den.eval a ≠ 0

/-- Evaluate at a regular point, returning none at a pole. -/
@[expose]
def eval? (f : RationalFn K) (a : K) : Option K :=
  let d := f.den.eval a
  if d = 0 then none else some (f.num.eval a / d)

/-- Successful evaluation records both regularity and the quotient value. -/
theorem eval?_eq_some (f : RationalFn K) (a v : K) :
    eval? f a = some v ↔ Regular f a ∧ v = f.num.eval a / f.den.eval a := by
  unfold eval? Regular
  dsimp only
  split <;> simp_all [eq_comm]

/-- Evaluation fails exactly at poles of the canonical denominator. -/
theorem eval?_eq_none (f : RationalFn K) (a : K) : eval? f a = none ↔ ¬Regular f a := by
  unfold eval? Regular
  dsimp only
  split <;> simp_all

/-- A canonical denominator divides the denominator in any fraction presentation. -/
theorem Represents.den_dvd {f : RationalFn K} {p q : DensePoly K}
    (h : Represents f p q) : f.den ∣ q :=
  f.bezout.dvd_of_dvd_mul ⟨p, by unfold Represents at h; grind⟩

/-- A nonvanishing multiple forces its divisor to be nonvanishing. -/
theorem eval_ne_zero_of_dvd {p q : DensePoly K} (h : p ∣ q) (a : K)
    (hq : q.eval a ≠ 0) : p.eval a ≠ 0 := by
  rcases h with ⟨r, hr⟩
  intro hp
  apply hq
  rw [hr, eval_mul_commring, hp, Lean.Grind.Semiring.zero_mul]

/-- A nonvanishing presentation denominator implies regularity after cancellation. -/
theorem Represents.regular {f : RationalFn K} {p q : DensePoly K}
    (h : Represents f p q) (a : K) (hq : q.eval a ≠ 0) : Regular f a :=
  eval_ne_zero_of_dvd h.den_dvd a hq

/-- At points where the input denominator is nonzero, a presentation computes the value. -/
theorem Represents.eval {f : RationalFn K} {p q : DensePoly K}
    (h : Represents f p q) (a : K) (hq : q.eval a ≠ 0) :
    eval? f a = some (p.eval a / q.eval a) := by
  apply (eval?_eq_some _ _ _).mpr
  have hd := h.regular a hq
  refine ⟨hd, ?_⟩
  have he := congrArg (fun p : DensePoly K => p.eval a) h
  simp only [eval_mul_commring] at he
  have hqi := Lean.Grind.Field.mul_inv_cancel hq
  have hdi := Lean.Grind.Field.mul_inv_cancel hd
  simp only [Lean.Grind.Field.div_eq_mul_inv]
  grind

/-- Normalization evaluates like its input fraction wherever that input is defined. -/
theorem eval?_normalize (p q : DensePoly K) (hq : q ≠ 0) (a : K)
    (ha : q.eval a ≠ 0) : eval? (normalize p q hq) a = some (p.eval a / q.eval a) :=
  Represents.eval (normalize_spec p q hq) a ha

/-- Sums of regular rational functions are regular. -/
theorem regular_add {f g : RationalFn K} {a : K} (hf : Regular f a) (hg : Regular g a) :
    Regular (f + g) a := by
  apply Represents.regular (add_spec f g) a
  rw [eval_mul_commring]
  intro h
  rcases Lean.Grind.Field.of_mul_eq_zero h with h | h
  · exact hf h
  · exact hg h

/-- Products of regular rational functions are regular. -/
theorem regular_mul {f g : RationalFn K} {a : K} (hf : Regular f a) (hg : Regular g a) :
    Regular (f * g) a := by
  apply Represents.regular (mul_spec f g) a
  rw [eval_mul_commring]
  intro h
  rcases Lean.Grind.Field.of_mul_eq_zero h with h | h
  · exact hf h
  · exact hg h

/-- Negation leaves regularity unchanged. -/
theorem regular_neg (f : RationalFn K) (a : K) : Regular (-f) a ↔ Regular f a := Iff.rfl

/-- Subtraction preserves regularity of its operands. -/
theorem regular_sub {f g : RationalFn K} {a : K} (hf : Regular f a) (hg : Regular g a) :
    Regular (f - g) a := regular_add hf hg

/-- Evaluation preserves addition on regular operands. -/
theorem eval?_add {f g : RationalFn K} {a u v : K}
    (hf : eval? f a = some u) (hg : eval? g a = some v) :
    eval? (f + g) a = some (u + v) := by
  rcases (eval?_eq_some _ _ _).mp hf with ⟨hfr, rfl⟩
  rcases (eval?_eq_some _ _ _).mp hg with ⟨hgr, rfl⟩
  apply (eval?_eq_some _ _ _).mpr
  refine ⟨regular_add hfr hgr, ?_⟩
  have hr := regular_add hfr hgr
  have he := congrArg (fun p : DensePoly K => p.eval a) (add_spec f g)
  simp only [eval_mul_commring, eval_add_semiring] at he
  have hi := Lean.Grind.Field.mul_inv_cancel hfr
  have hj := Lean.Grind.Field.mul_inv_cancel hgr
  have hk := Lean.Grind.Field.mul_inv_cancel hr
  simp only [Lean.Grind.Field.div_eq_mul_inv]
  grind

/-- Evaluation preserves multiplication on regular operands. -/
theorem eval?_mul {f g : RationalFn K} {a u v : K}
    (hf : eval? f a = some u) (hg : eval? g a = some v) :
    eval? (f * g) a = some (u * v) := by
  rcases (eval?_eq_some _ _ _).mp hf with ⟨hfr, rfl⟩
  rcases (eval?_eq_some _ _ _).mp hg with ⟨hgr, rfl⟩
  apply (eval?_eq_some _ _ _).mpr
  refine ⟨regular_mul hfr hgr, ?_⟩
  have hr := regular_mul hfr hgr
  have he := congrArg (fun p : DensePoly K => p.eval a) (mul_spec f g)
  simp only [eval_mul_commring] at he
  have hi := Lean.Grind.Field.mul_inv_cancel hfr
  have hj := Lean.Grind.Field.mul_inv_cancel hgr
  have hk := Lean.Grind.Field.mul_inv_cancel hr
  simp only [Lean.Grind.Field.div_eq_mul_inv]
  grind

/-- Evaluation preserves negation on regular inputs. -/
theorem eval?_neg {f : RationalFn K} {a u : K} (hf : eval? f a = some u) :
    eval? (-f) a = some (-u) := by
  rcases (eval?_eq_some _ _ _).mp hf with ⟨hr, rfl⟩
  apply (eval?_eq_some _ _ _).mpr
  refine ⟨hr, ?_⟩
  change -(f.num.eval a / f.den.eval a) = (-f.num).eval a / f.den.eval a
  rw [eval_neg_ring]
  simp only [Lean.Grind.Field.div_eq_mul_inv]
  grind

/-- Evaluation preserves subtraction on regular inputs. -/
theorem eval?_sub {f g : RationalFn K} {a u v : K}
    (hf : eval? f a = some u) (hg : eval? g a = some v) :
    eval? (f - g) a = some (u - v) := by
  rw [Lean.Grind.Field.toCommRing.toRing.sub_eq_add_neg]
  have h := eval?_add hf (eval?_neg hg)
  simpa only [Lean.Grind.Ring.sub_eq_add_neg] using h

/-- Inversion evaluates to the inverse when the input value is nonzero. -/
theorem eval?_inv {f : RationalFn K} {a u : K} (hf : eval? f a = some u) (hu : u ≠ 0) :
    eval? f⁻¹ a = some u⁻¹ := by
  rcases (eval?_eq_some _ _ _).mp hf with ⟨hr, rfl⟩
  have hn : f.num.eval a ≠ 0 := by
    intro hn
    apply hu
    rw [hn, Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.zero_mul]
  have hfn : f.num ≠ 0 := by intro h; apply hn; rw [h, eval_zero]
  have h := Represents.eval (inv_spec f hfn) a hn
  have hi := Lean.Grind.Field.mul_inv_cancel hn
  have hd := Lean.Grind.Field.mul_inv_cancel hr
  have he : (f.num.eval a / f.den.eval a)⁻¹ = f.den.eval a / f.num.eval a := by
    symm
    apply Lean.Grind.Field.eq_inv_of_mul_eq_one
    simp only [Lean.Grind.Field.div_eq_mul_inv]
    grind
  rw [he]
  exact h

/-- Division evaluates through a regular divisor with nonzero value. -/
theorem eval?_div {f g : RationalFn K} {a u v : K}
    (hf : eval? f a = some u) (hg : eval? g a = some v) (hv : v ≠ 0) :
    eval? (f / g) a = some (u / v) := by
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Field.div_eq_mul_inv]
  exact eval?_mul hf (eval?_inv hg hv)

end Hex.RationalFn
