/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexInterval.Experiment.Center

public section

/-!
# Real semantics for the centered-product vertical

This experimental companion gives the D2 centered-product checker an ordinary
mathematical interpretation.  Expression semantics are relational over a
total typed valuation.  In particular, malformed node references are never
read with `getD` or assigned a default real value.

The file proves soundness of the finite-closed literal, subtraction,
four-corner multiplication, and square rules; validates the static
`centerV1` identity; turns a checked equality edge into a real equality; and
transports the centered `[0, 1/4]` range back to `x * (1 - x)`.
-/

namespace Hex.Interval.Experiment.Center

/-! # Dyadic and raw-interval interpretation -/

/-- Mathematical real value of a Core dyadic. -/
def dyadic (value : Dyadic) : ℝ := (value.toRat : ℝ)

@[simp]
theorem dyadic_zero : dyadic 0 = 0 := by
  simp [dyadic, Dyadic.toRat_zero]

@[simp]
theorem dyadic_one : dyadic 1 = 1 := by
  rw [dyadic, show (1 : Dyadic) = ((1 : Int) : Dyadic) from rfl,
    Dyadic.toRat_intCast]
  norm_num

@[simp]
theorem dyadic_neg (value : Dyadic) : dyadic (-value) = -dyadic value := by
  simp [dyadic, Dyadic.toRat_neg]

@[simp]
theorem dyadic_sub (left right : Dyadic) :
    dyadic (left - right) = dyadic left - dyadic right := by
  simp [dyadic, Dyadic.toRat_sub]

@[simp]
theorem dyadic_mul (left right : Dyadic) :
    dyadic (left * right) = dyadic left * dyadic right := by
  simp [dyadic, Dyadic.toRat_mul]

theorem dyadic_le {left right : Dyadic} (h : left ≤ right) :
    dyadic left ≤ dyadic right := by
  exact (Rat.cast_le (K := ℝ)).2 (Dyadic.toRat_le_toRat_iff.2 h)

theorem dyadic_lt {left right : Dyadic} (h : left < right) :
    dyadic left < dyadic right := by
  exact (Rat.cast_lt (K := ℝ)).2 (Dyadic.toRat_lt_toRat_iff.2 h)

@[simp]
theorem dyadic_half : dyadic half = (1 / 2 : ℝ) := by
  norm_num [half, dyadic, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

@[simp]
theorem dyadic_quarter : dyadic quarter = (1 / 4 : ℝ) := by
  norm_num [quarter, dyadic, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]

/-- Meaning of a lower cut at a real value. -/
def lowerHolds : Lower → ℝ → Prop
  | .unbounded, _ => True
  | .finite value false, x => dyadic value ≤ x
  | .finite value true, x => dyadic value < x

/-- Meaning of an upper cut at a real value. -/
def upperHolds : Upper → ℝ → Prop
  | .finite value false, x => x ≤ dyadic value
  | .finite value true, x => x < dyadic value
  | .unbounded, _ => True

/-- Membership in an exact raw interval, including empty, strict, and
unbounded cuts. -/
def Contains : Raw → ℝ → Prop
  | .empty, _ => False
  | .bounds lower upper, x => lowerHolds lower x ∧ upperHolds upper x

@[simp]
theorem contains_closed (lower upper : Dyadic) (x : ℝ) :
    Contains (closed lower upper) x ↔ dyadic lower ≤ x ∧ x ≤ dyadic upper :=
  Iff.rfl

/-- A successful finite-closed extraction identifies the original raw range;
normalization cannot silently replace a rejected or inconsistent input. -/
theorem closed?_eq_some {limit : EndpointLimit} {raw : Raw} {lower upper : Dyadic}
    (h : closed? limit raw = some (lower, upper)) : raw = closed lower upper := by
  unfold closed? at h
  generalize hresult : raw.normalizeWithin limit = result at h
  cases result with
  | resourceLimit _ =>
      simp at h
  | ready normalized isConsistent =>
      cases normalized with
      | empty =>
          simp at h
      | bounds lowerCut upperCut =>
          cases lowerCut with
          | unbounded =>
              simp at h
          | finite actualLower lowerStrict =>
              cases upperCut with
              | unbounded =>
                  simp at h
              | finite actualUpper upperStrict =>
                  cases lowerStrict <;> cases upperStrict <;>
                    simp at h
                  rcases h with ⟨rfl, rfl⟩
                  unfold Raw.normalizeWithin at hresult
                  dsimp only at hresult
                  split at hresult
                  · injection hresult with hnormalized
                    unfold Raw.normalizeUnchecked at hnormalized
                    split at hnormalized
                    · exact hnormalized
                    · cases hnormalized
                  · cases hresult

/-! Successful resource checks expose exact arithmetic results. -/

theorem subDyadic?_eq_some {limit : EndpointLimit} {left right result : Dyadic}
    (h : subDyadic? limit left right = some result) : result = left - right := by
  unfold subDyadic? at h
  split at h <;> simp_all

theorem mulDyadic?_eq_some {limit : EndpointLimit} {left right result : Dyadic}
    (h : mulDyadic? limit left right = some result) : result = left * right := by
  unfold mulDyadic? at h
  split at h <;> simp_all

theorem le?_eq_some_true {limit : EndpointLimit} {left right : Dyadic}
    (h : le? limit left right = some true) : left ≤ right := by
  unfold le? at h
  split at h <;> simp_all

theorem le?_eq_some_false {limit : EndpointLimit} {left right : Dyadic}
    (h : le? limit left right = some false) : right < left := by
  unfold le? at h
  split at h <;> simp_all [Dyadic.not_lt]

theorem checkedClosed?_eq_some {limit : EndpointLimit} {node : NodeId .real}
    {lower upper : Dyadic} {output : Row}
    (h : checkedClosed? limit node lower upper = some output) :
    output = ⟨node, closed lower upper⟩ := by
  unfold checkedClosed? at h
  cases hclosed : closed? limit (closed lower upper) with
  | none => simp [hclosed] at h
  | some endpoints => simp [hclosed] at h ⊢; exact h.symm

namespace Row

theorem min2?_sound {limit : EndpointLimit} {left right result : Dyadic}
    (h : min2? limit left right = some result) :
    dyadic result = min (dyadic left) (dyadic right) := by
  by_cases hcost : compareOk limit left right
  · by_cases hle : left ≤ right
    · simp [min2?, le?, hcost, hle] at h
      subst result
      exact (min_eq_left (dyadic_le hle)).symm
    · simp [min2?, le?, hcost, hle] at h
      subst result
      have hright : right < left := Dyadic.not_lt.mp hle
      exact (min_eq_right (dyadic_lt hright).le).symm
  · simp [min2?, le?, hcost] at h

theorem max2?_sound {limit : EndpointLimit} {left right result : Dyadic}
    (h : max2? limit left right = some result) :
    dyadic result = max (dyadic left) (dyadic right) := by
  by_cases hcost : compareOk limit left right
  · by_cases hle : left ≤ right
    · simp [max2?, le?, hcost, hle] at h
      subst result
      exact (max_eq_right (dyadic_le hle)).symm
    · simp [max2?, le?, hcost, hle] at h
      subst result
      have hright : right < left := Dyadic.not_lt.mp hle
      exact (max_eq_left (dyadic_lt hright).le).symm
  · simp [max2?, le?, hcost] at h

theorem min4?_sound {limit : EndpointLimit} {a b c d result : Dyadic}
    (h : min4? limit a b c d = some result) :
    dyadic result =
      min (min (dyadic a) (dyadic b)) (min (dyadic c) (dyadic d)) := by
  cases hab : min2? limit a b with
  | none => simp [min4?, hab] at h
  | some ab =>
      cases hcd : min2? limit c d with
      | none => simp [min4?, hab, hcd] at h
      | some cd =>
          have habSound := min2?_sound hab
          have hcdSound := min2?_sound hcd
          have hresult : min2? limit ab cd = some result := by
            simpa [min4?, hab, hcd] using h
          rw [min2?_sound hresult, habSound, hcdSound]

theorem max4?_sound {limit : EndpointLimit} {a b c d result : Dyadic}
    (h : max4? limit a b c d = some result) :
    dyadic result =
      max (max (dyadic a) (dyadic b)) (max (dyadic c) (dyadic d)) := by
  cases hab : max2? limit a b with
  | none => simp [max4?, hab] at h
  | some ab =>
      cases hcd : max2? limit c d with
      | none => simp [max4?, hab, hcd] at h
      | some cd =>
          have habSound := max2?_sound hab
          have hcdSound := max2?_sound hcd
          have hresult : max2? limit ab cd = some result := by
            simpa [max4?, hab, hcd] using h
          rw [max2?_sound hresult, habSound, hcdSound]

end Row

/-! # Total program semantics -/

/-- A total real valuation of typed node identifiers.  Totality is harmless:
`Program.Holds` constrains exactly the nodes actually present in the program,
and no lookup invents a value for a missing instruction. -/
abbrev Valuation := NodeId .real → ℝ

namespace Prim

/-- Relational meaning of one instruction at its output node. -/
def Holds (valuation : Valuation) (output : NodeId .real) : Prim .real → Prop
  | .var _ => True
  | .lit value => valuation output = dyadic value
  | .sub left right => valuation output = valuation left - valuation right
  | .mul left right => valuation output = valuation left * valuation right
  | .sq input => valuation output = valuation input ^ 2

end Prim

namespace Program

/-- A program holds under a total valuation when every exact successful node
lookup satisfies its instruction relation.  There is no defaulting lookup. -/
def Holds (program : Program) (valuation : Valuation) : Prop :=
  ∀ (node : NodeId .real) (operation : Prim .real),
    program.node? node = some operation → operation.Holds valuation node

end Program

namespace Row

/-- Semantic truth of one interval row under a node valuation. -/
def Holds (valuation : Valuation) (row : Row) : Prop :=
  Contains row.range (valuation row.node)

/-- Public elimination rule for arbitrary row semantics; downstream users do
not need the implementation of `Holds` to be exposed. -/
theorem holds_iff {valuation : Valuation} {row : Row} :
    row.Holds valuation ↔ Contains row.range (valuation row.node) :=
  Iff.rfl

/-- Public constructor/eliminator for the finite-closed rows emitted by the
current arithmetic rules. -/
@[simp]
theorem holds_closed_iff {valuation : Valuation} {node : NodeId .real}
    {lower upper : Dyadic} :
    (⟨node, closed lower upper⟩ : Row).Holds valuation ↔
      dyadic lower ≤ valuation node ∧ valuation node ≤ dyadic upper :=
  Iff.rfl

end Row

/-! # Finite-closed rule soundness -/

/-- A literal belongs to its singleton range. -/
theorem contains_lit (value : Dyadic) : Contains (closed value value) (dyadic value) := by
  simp

/-- Closed subtraction uses opposite endpoint order on the subtrahend. -/
theorem contains_sub {leftLower leftUpper rightLower rightUpper : Dyadic} {x y : ℝ}
    (hx : Contains (closed leftLower leftUpper) x)
    (hy : Contains (closed rightLower rightUpper) y) :
    Contains (closed (leftLower - rightUpper) (leftUpper - rightLower)) (x - y) := by
  simp only [contains_closed, dyadic_sub] at hx hy ⊢
  constructor <;> linarith

private theorem mul_le_max4 {x y a b c d : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  rcases le_total 0 y with hy | hy
  · have hxy : x * y ≤ b * y := mul_le_mul_of_nonneg_right hb hy
    rcases le_total 0 b with hb0 | hb0
    · exact (hxy.trans (mul_le_mul_of_nonneg_left hd hb0)).trans
        (le_max_of_le_right (le_max_right _ _))
    · exact (hxy.trans (mul_le_mul_of_nonpos_left hc hb0)).trans
        (le_max_of_le_right (le_max_left _ _))
  · have hxy : x * y ≤ a * y := mul_le_mul_of_nonpos_right ha hy
    rcases le_total 0 a with ha0 | ha0
    · exact (hxy.trans (mul_le_mul_of_nonneg_left hd ha0)).trans
        (le_max_of_le_left (le_max_right _ _))
    · exact (hxy.trans (mul_le_mul_of_nonpos_left hc ha0)).trans
        (le_max_of_le_left (le_max_left _ _))

private theorem min4_le_mul {x y a b c d : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h := mul_le_max4 (x := -x) (y := y) (a := -b) (b := -a) (c := c) (d := d)
    (by linarith) (by linarith) hc hd
  have hmax :
      max (max (-b * c) (-b * d)) (max (-a * c) (-a * d)) =
        -(min (min (b * c) (b * d)) (min (a * c) (a * d))) := by
    simp [max_neg_neg]
  rw [neg_mul, hmax] at h
  have hneg := neg_le_neg h
  rw [neg_neg] at hneg
  calc
    min (min (a * c) (a * d)) (min (b * c) (b * d)) =
        min (min (b * c) (b * d)) (min (a * c) (a * d)) := min_comm _ _
    _ ≤ x * y := by linarith

/-- Four-corner multiplication encloses products for arbitrary signs. -/
theorem contains_mul {leftLower leftUpper rightLower rightUpper : Dyadic} {x y : ℝ}
    {outputLower outputUpper : Dyadic}
    (hlower : dyadic outputLower =
      min (min (dyadic leftLower * dyadic rightLower)
          (dyadic leftLower * dyadic rightUpper))
        (min (dyadic leftUpper * dyadic rightLower)
          (dyadic leftUpper * dyadic rightUpper)))
    (hupper : dyadic outputUpper =
      max (max (dyadic leftLower * dyadic rightLower)
          (dyadic leftLower * dyadic rightUpper))
        (max (dyadic leftUpper * dyadic rightLower)
          (dyadic leftUpper * dyadic rightUpper)))
    (hx : Contains (closed leftLower leftUpper) x)
    (hy : Contains (closed rightLower rightUpper) y) :
    Contains (closed outputLower outputUpper) (x * y) := by
  rcases hx with ⟨hxLower, hxUpper⟩
  rcases hy with ⟨hyLower, hyUpper⟩
  rw [contains_closed, hlower, hupper]
  exact ⟨min4_le_mul hxLower hxUpper hyLower hyUpper,
    mul_le_max4 hxLower hxUpper hyLower hyUpper⟩

private theorem sq_le_endpoint_max {lower upper x : ℝ}
    (hlower : lower ≤ x) (hupper : x ≤ upper) :
    x ^ 2 ≤ max (lower ^ 2) (upper ^ 2) := by
  rcases le_total 0 x with hx | hx
  · have hu : 0 ≤ upper := hx.trans hupper
    exact ((sq_le_sq₀ hx hu).2 hupper).trans (le_max_right _ _)
  · have hl : lower ≤ 0 := hlower.trans hx
    have hneg : (-x) ^ 2 ≤ (-lower) ^ 2 :=
      (sq_le_sq₀ (neg_nonneg.mpr hx) (neg_nonneg.mpr hl)).2 (neg_le_neg hlower)
    have hsq : x ^ 2 ≤ lower ^ 2 := by simpa using hneg
    exact hsq.trans (le_max_left _ _)

/-- A zero-spanning square range has lower endpoint zero and the larger
endpoint square as its upper endpoint. -/
theorem contains_sq_span {lower upper : Dyadic} {x : ℝ}
    {outputUpper : Dyadic}
    (houtput : dyadic outputUpper = max (dyadic lower ^ 2) (dyadic upper ^ 2))
    (hx : Contains (closed lower upper) x) :
    Contains (closed 0 outputUpper) (x ^ 2) := by
  rw [contains_closed] at hx ⊢
  rcases hx with ⟨hlower, hupper⟩
  constructor
  · rw [dyadic_zero]
    positivity
  · rw [houtput]
    exact sq_le_endpoint_max hlower hupper

/-- On a nonnegative input range, squaring preserves endpoint order. -/
theorem contains_sq_nonneg {lower upper : Dyadic} {x : ℝ}
    (hlowerZero : 0 ≤ dyadic lower)
    (hx : Contains (closed lower upper) x) :
    Contains (closed (lower * lower) (upper * upper)) (x ^ 2) := by
  rw [contains_closed] at hx ⊢
  rcases hx with ⟨hlower, hupper⟩
  have hxZero := hlowerZero.trans hlower
  have hupperZero := hxZero.trans hupper
  simp only [dyadic_mul, ← pow_two]
  exact ⟨(sq_le_sq₀ hlowerZero hxZero).2 hlower,
    (sq_le_sq₀ hxZero hupperZero).2 hupper⟩

/-- On a nonpositive input range, squaring reverses endpoint order. -/
theorem contains_sq_nonpos {lower upper : Dyadic} {x : ℝ}
    (hupperZero : dyadic upper ≤ 0)
    (hx : Contains (closed lower upper) x) :
    Contains (closed (upper * upper) (lower * lower)) (x ^ 2) := by
  rw [contains_closed] at hx ⊢
  rcases hx with ⟨hlower, hupper⟩
  have hxZero := hupper.trans hupperZero
  have hlowerZero := hlower.trans hxZero
  simp only [dyadic_mul, ← pow_two]
  constructor
  · have hsq := (sq_le_sq₀ (neg_nonneg.mpr hupperZero) (neg_nonneg.mpr hxZero)).2
      (neg_le_neg hupper)
    simpa using hsq
  · have hsq := (sq_le_sq₀ (neg_nonneg.mpr hxZero) (neg_nonneg.mpr hlowerZero)).2
      (neg_le_neg hlower)
    simpa using hsq

namespace Row

/-- A successful resource-checked literal row is semantically sound. -/
theorem lit?_sound {limit : EndpointLimit} {valuation : Valuation}
    {node : NodeId .real} {value : Dyadic} {output : Row}
    (hcheck : lit? limit node value = some output)
    (hvalue : valuation node = dyadic value) : Holds valuation output := by
  have hclosed : checkedClosed? limit node value value = some output := by
    change checkedClosed? limit node value value = some output at hcheck
    exact hcheck
  rw [checkedClosed?_eq_some hclosed]
  change Contains (closed value value) (valuation node)
  rw [hvalue]
  exact contains_lit value

/-- A successful resource-checked subtraction row preserves containment. -/
theorem sub?_sound {limit : EndpointLimit} {valuation : Valuation}
    {node : NodeId .real} {left right output : Row}
    (hcheck : sub? limit node left right = some output)
    (hleft : Holds valuation left) (hright : Holds valuation right)
    (hvalue : valuation node = valuation left.node - valuation right.node) :
    Holds valuation output := by
  cases hleftClosed : closed? limit left.range with
  | none => simp [sub?, hleftClosed] at hcheck
  | some leftEndpoints =>
      rcases leftEndpoints with ⟨leftLower, leftUpper⟩
      cases hrightClosed : closed? limit right.range with
      | none => simp [sub?, hleftClosed, hrightClosed] at hcheck
      | some rightEndpoints =>
          rcases rightEndpoints with ⟨rightLower, rightUpper⟩
          have hclosed : checkedClosed? limit node (leftLower - rightUpper)
              (leftUpper - rightLower) = some output := by
            simp [sub?, hleftClosed, hrightClosed] at hcheck
            exact hcheck.2.2
          unfold Holds at hleft hright
          rw [closed?_eq_some hleftClosed] at hleft
          rw [closed?_eq_some hrightClosed] at hright
          rw [checkedClosed?_eq_some hclosed]
          change Contains (closed (leftLower - rightUpper) (leftUpper - rightLower))
            (valuation node)
          rw [hvalue]
          exact contains_sub hleft hright

/-- A successful resource-checked four-corner product row preserves
containment for arbitrary endpoint signs. -/
theorem mul?_sound {limit : EndpointLimit} {valuation : Valuation}
    {node : NodeId .real} {left right output : Row}
    (hcheck : mul? limit node left right = some output)
    (hleft : Holds valuation left) (hright : Holds valuation right)
    (hvalue : valuation node = valuation left.node * valuation right.node) :
    Holds valuation output := by
  cases hleftClosed : closed? limit left.range with
  | none => simp [mul?, hleftClosed] at hcheck
  | some leftEndpoints =>
      rcases leftEndpoints with ⟨leftLower, leftUpper⟩
      cases hrightClosed : closed? limit right.range with
      | none => simp [mul?, hleftClosed, hrightClosed] at hcheck
      | some rightEndpoints =>
          rcases rightEndpoints with ⟨rightLower, rightUpper⟩
          cases hll : mulDyadic? limit leftLower rightLower with
          | none => simp [mul?, hleftClosed, hrightClosed, hll] at hcheck
          | some ll =>
              cases hlu : mulDyadic? limit leftLower rightUpper with
              | none => simp [mul?, hleftClosed, hrightClosed, hll, hlu] at hcheck
              | some lu =>
                  cases hul : mulDyadic? limit leftUpper rightLower with
                  | none =>
                      simp [mul?, hleftClosed, hrightClosed, hll, hlu, hul] at hcheck
                  | some ul =>
                      cases huu : mulDyadic? limit leftUpper rightUpper with
                      | none =>
                          simp [mul?, hleftClosed, hrightClosed, hll, hlu, hul, huu] at hcheck
                      | some uu =>
                          cases hlower : min4? limit ll lu ul uu with
                          | none =>
                              simp [mul?, hleftClosed, hrightClosed, hll, hlu, hul,
                                huu, hlower] at hcheck
                          | some outputLower =>
                              cases hupper : max4? limit ll lu ul uu with
                              | none =>
                                  simp [mul?, hleftClosed, hrightClosed, hll, hlu, hul,
                                    huu, hlower, hupper] at hcheck
                              | some outputUpper =>
                                  have hclosed : checkedClosed? limit node outputLower
                                      outputUpper = some output := by
                                    simpa [mul?, hleftClosed, hrightClosed, hll, hlu, hul,
                                      huu, hlower, hupper] using hcheck
                                  have hlowerSound := min4?_sound hlower
                                  have hupperSound := max4?_sound hupper
                                  rw [mulDyadic?_eq_some hll, mulDyadic?_eq_some hlu,
                                    mulDyadic?_eq_some hul, mulDyadic?_eq_some huu] at hlowerSound
                                  rw [mulDyadic?_eq_some hll, mulDyadic?_eq_some hlu,
                                    mulDyadic?_eq_some hul, mulDyadic?_eq_some huu] at hupperSound
                                  simp only [dyadic_mul] at hlowerSound hupperSound
                                  unfold Holds at hleft hright ⊢
                                  rw [closed?_eq_some hleftClosed] at hleft
                                  rw [closed?_eq_some hrightClosed] at hright
                                  rw [checkedClosed?_eq_some hclosed, hvalue]
                                  exact contains_mul hlowerSound hupperSound hleft hright

/-- A successful resource-checked square row preserves containment in each
of the negative, positive, and zero-spanning sign branches. -/
theorem sq?_sound {limit : EndpointLimit} {valuation : Valuation}
    {node : NodeId .real} {input output : Row}
    (hcheck : sq? limit node input = some output)
    (hinput : Holds valuation input)
    (hvalue : valuation node = valuation input.node ^ 2) : Holds valuation output := by
  cases hinputClosed : closed? limit input.range with
  | none => simp [sq?, hinputClosed] at hcheck
  | some endpoints =>
      rcases endpoints with ⟨lower, upper⟩
      cases hlowerSq : mulDyadic? limit lower lower with
      | none => simp [sq?, hinputClosed, hlowerSq] at hcheck
      | some lowerSq =>
          cases hupperSq : mulDyadic? limit upper upper with
          | none => simp [sq?, hinputClosed, hlowerSq, hupperSq] at hcheck
          | some upperSq =>
              cases hnonpos : le? limit upper 0 with
              | none => simp [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos] at hcheck
              | some upperNonpositive =>
                  cases upperNonpositive with
                  | true =>
                      have hclosed :
                          checkedClosed? limit node upperSq lowerSq = some output := by
                        simpa [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos] using hcheck
                      have hsign : dyadic upper ≤ 0 := by
                        have := dyadic_le (le?_eq_some_true hnonpos)
                        simpa using this
                      unfold Holds at hinput ⊢
                      rw [closed?_eq_some hinputClosed] at hinput
                      rw [checkedClosed?_eq_some hclosed, hvalue,
                        mulDyadic?_eq_some hupperSq, mulDyadic?_eq_some hlowerSq]
                      exact contains_sq_nonpos hsign hinput
                  | false =>
                      cases hnonneg : le? limit 0 lower with
                      | none =>
                          simp [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos,
                            hnonneg] at hcheck
                      | some lowerNonnegative =>
                          cases lowerNonnegative with
                          | true =>
                              have hclosed : checkedClosed? limit node lowerSq upperSq =
                                  some output := by
                                simpa [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos,
                                  hnonneg] using hcheck
                              have hsign : 0 ≤ dyadic lower := by
                                have := dyadic_le (le?_eq_some_true hnonneg)
                                simpa using this
                              unfold Holds at hinput ⊢
                              rw [closed?_eq_some hinputClosed] at hinput
                              rw [checkedClosed?_eq_some hclosed, hvalue,
                                mulDyadic?_eq_some hlowerSq, mulDyadic?_eq_some hupperSq]
                              exact contains_sq_nonneg hsign hinput
                          | false =>
                              cases hmax : max2? limit lowerSq upperSq with
                              | none =>
                                  simp [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos,
                                    hnonneg, hmax] at hcheck
                              | some outputUpper =>
                                  have hclosed : checkedClosed? limit node 0 outputUpper =
                                      some output := by
                                    simpa [sq?, hinputClosed, hlowerSq, hupperSq, hnonpos,
                                      hnonneg, hmax] using hcheck
                                  have hmaxSound := max2?_sound hmax
                                  rw [mulDyadic?_eq_some hlowerSq,
                                    mulDyadic?_eq_some hupperSq] at hmaxSound
                                  simp only [dyadic_mul, ← pow_two] at hmaxSound
                                  unfold Holds at hinput ⊢
                                  rw [closed?_eq_some hinputClosed] at hinput
                                  rw [checkedClosed?_eq_some hclosed, hvalue]
                                  exact contains_sq_span hmaxSound hinput

end Row

/-! # Checked centered equality -/

/-- The algebraic identity installed by the versioned `centerV1` recipe. -/
theorem centerV1_identity (x : ℝ) :
    x * (1 - x) = 1 / 4 - (x - 1 / 2) ^ 2 := by
  ring

namespace EqEdge

/-- Every accepted `centerV1` edge denotes an actual equality under any total
valuation satisfying the checked program. -/
theorem sound {program : Program} {edge : EqEdge} {valuation : Valuation}
    {expectedBaseSize maxGeneration : Nat}
    (hcheck : edge.check program expectedBaseSize maxGeneration = true)
    (hprogram : program.Holds valuation) :
    valuation edge.left = valuation edge.right := by
  rcases edge with ⟨edgeLeft, edgeRight, recipe⟩
  cases recipe with
  | centerV1 center =>
      simp only [EqEdge.check, Bool.and_eq_true, beq_iff_eq] at hcheck
      have hcenter : center.check program = true := by tauto
      have hleft : edgeLeft = center.prod := by tauto
      have hright : edgeRight = center.form := by tauto
      simp only [Center.check, Bool.and_eq_true, beq_iff_eq] at hcenter
      have hone : program.node? center.one = some (.lit (1 : Dyadic)) := by tauto
      have hgap : program.node? center.gap = some (.sub center.one center.x) := by tauto
      have hprod : program.node? center.prod = some (.mul center.x center.gap) := by tauto
      have hhalf : program.node? center.half =
          some (.lit (Dyadic.ofIntWithPrec 1 1)) := by tauto
      have hshift : program.node? center.shift = some (.sub center.x center.half) := by tauto
      have hsquare : program.node? center.square = some (.sq center.shift) := by tauto
      have hquarter : program.node? center.quarter =
          some (.lit (Dyadic.ofIntWithPrec 1 2)) := by tauto
      have hform : program.node? center.form = some (.sub center.quarter center.square) := by tauto
      have honeSem : valuation center.one = dyadic 1 := by
        simpa [Prim.Holds] using hprogram center.one (.lit 1) hone
      have hgapSem : valuation center.gap = valuation center.one - valuation center.x := by
        simpa [Prim.Holds] using
          hprogram center.gap (.sub center.one center.x) hgap
      have hprodSem : valuation center.prod = valuation center.x * valuation center.gap := by
        simpa [Prim.Holds] using
          hprogram center.prod (.mul center.x center.gap) hprod
      have hhalfSem : valuation center.half = dyadic half := by
        simpa [Prim.Holds, half] using
          hprogram center.half (.lit (Dyadic.ofIntWithPrec 1 1)) hhalf
      have hshiftSem : valuation center.shift = valuation center.x - valuation center.half := by
        simpa [Prim.Holds] using
          hprogram center.shift (.sub center.x center.half) hshift
      have hsquareSem : valuation center.square = valuation center.shift ^ 2 := by
        simpa [Prim.Holds] using hprogram center.square (.sq center.shift) hsquare
      have hquarterSem : valuation center.quarter = dyadic quarter := by
        simpa [Prim.Holds, quarter] using
          hprogram center.quarter (.lit (Dyadic.ofIntWithPrec 1 2)) hquarter
      have hformSem :
          valuation center.form = valuation center.quarter - valuation center.square := by
        simpa [Prim.Holds] using
          hprogram center.form (.sub center.quarter center.square) hform
      calc
        valuation edgeLeft = valuation center.prod := congrArg valuation hleft
        _ = valuation center.x * valuation center.gap := hprodSem
        _ = valuation center.x * (1 - valuation center.x) := by
          rw [hgapSem, honeSem, dyadic_one]
        _ = 1 / 4 - (valuation center.x - 1 / 2) ^ 2 :=
          centerV1_identity _
        _ = valuation center.quarter - valuation center.square := by
          rw [hquarterSem, hsquareSem, hshiftSem, hhalfSem, dyadic_quarter,
            dyadic_half]
        _ = valuation center.form := hformSem.symm
        _ = valuation edgeRight := congrArg valuation hright.symm

end EqEdge

/-! # Generic checked-trace soundness -/

/-- Every row in a proof-facing table is semantically true. -/
def RowsHold (valuation : Valuation) (rows : List Row) : Prop :=
  ∀ row ∈ rows, row.Holds valuation

namespace RowsHold

/-- Public introduction and elimination rule for a semantic row table. -/
theorem iff_forall {valuation : Valuation} {rows : List Row} :
    RowsHold valuation rows ↔ ∀ row ∈ rows, row.Holds valuation :=
  Iff.rfl

/-- An exact successful list lookup inherits the table's semantic invariant. -/
theorem lookup {valuation : Valuation} {rows : List Row} {index : Nat} {row : Row}
    (hrows : RowsHold valuation rows) (hlookup : rows[index]? = some row) :
    row.Holds valuation := by
  exact hrows row (List.mem_of_getElem? hlookup)

/-- `Fact.prior?` never fabricates a row: every successful lookup names an
element of the newest-first accumulator. -/
theorem prior {valuation : Valuation} {priorCount : Nat} {priorRev : List Row}
    {index : Nat} {row : Row} (hrows : RowsHold valuation priorRev)
    (hlookup : Fact.prior? priorCount priorRev index = some row) :
    row.Holds valuation := by
  unfold Fact.prior? at hlookup
  split at hlookup
  · exact hrows.lookup hlookup
  · simp at hlookup

end RowsHold

namespace Row

/-- Transporting an unchanged range across a semantically valid equality
edge preserves its meaning in either orientation. -/
theorem transport_sound {valuation : Valuation} {input output : Row}
    {edge : EqEdge} (hinput : input.Holds valuation)
    (hrange : input.range = output.range)
    (hnodes :
      (input.node = edge.left ∧ output.node = edge.right) ∨
        (input.node = edge.right ∧ output.node = edge.left))
    (hedge : valuation edge.left = valuation edge.right) :
    output.Holds valuation := by
  unfold Holds at hinput ⊢
  rw [← hrange]
  rcases hnodes with ⟨hinputNode, houtputNode⟩ | ⟨hinputNode, houtputNode⟩
  · simpa [hinputNode, houtputNode, hedge] using hinput
  · simpa [hinputNode, houtputNode, hedge] using hinput

end Row

namespace Fact

/-- One accepted derivation is semantically sound, assuming the checked
program, caller-bound sources, equality table, and already accepted rows are
sound. Exact optional lookups are the only way information enters the rule. -/
theorem sound {limit : EndpointLimit} {program : Program} {sources : List Row}
    {edges : List EqEdge} {priorCount : Nat} {priorRev : List Row} {fact : Fact}
    {valuation : Valuation}
    (hcheck : fact.check limit program sources edges priorCount priorRev = true)
    (hprogram : program.Holds valuation) (hsources : RowsHold valuation sources)
    (hedges : ∀ edge ∈ edges, valuation edge.left = valuation edge.right)
    (hprior : RowsHold valuation priorRev) : fact.row.Holds valuation := by
  rcases fact with ⟨row, derivation⟩
  cases derivation with
  | source source =>
      simp only [Fact.check, Bool.and_eq_true, beq_iff_eq] at hcheck
      exact hsources.lookup hcheck.2
  | lit =>
      cases hnode : program.node? row.node with
      | none => simp [Fact.check, hnode] at hcheck
      | some operation =>
          cases operation with
          | var source => simp [Fact.check, hnode] at hcheck
          | lit value =>
              simp only [Fact.check, hnode, Bool.and_eq_true, beq_iff_eq] at hcheck
              apply Row.lit?_sound hcheck.2
              simpa [Prim.Holds] using hprogram row.node (.lit value) hnode
          | sub left right => simp [Fact.check, hnode] at hcheck
          | mul left right => simp [Fact.check, hnode] at hcheck
          | sq input => simp [Fact.check, hnode] at hcheck
  | sub left right =>
      cases hnode : program.node? row.node with
      | none => simp [Fact.check, hnode] at hcheck
      | some operation =>
          cases operation with
          | var source => simp [Fact.check, hnode] at hcheck
          | lit value => simp [Fact.check, hnode] at hcheck
          | mul leftNode rightNode => simp [Fact.check, hnode] at hcheck
          | sq inputNode => simp [Fact.check, hnode] at hcheck
          | sub leftNode rightNode =>
              cases hleftLookup : Fact.prior? priorCount priorRev left with
              | none => simp [Fact.check, hnode, hleftLookup] at hcheck
              | some leftRow =>
                  cases hrightLookup : Fact.prior? priorCount priorRev right with
                  | none => simp [Fact.check, hnode, hleftLookup, hrightLookup] at hcheck
                  | some rightRow =>
                      simp only [Fact.check, hnode, hleftLookup, hrightLookup,
                        Bool.and_eq_true, beq_iff_eq] at hcheck
                      have hleftNode : leftRow.node = leftNode := by tauto
                      have hrightNode : rightRow.node = rightNode := by tauto
                      have hrule : Row.sub? limit row.node leftRow rightRow = some row := by
                        tauto
                      apply Row.sub?_sound hrule (hprior.prior hleftLookup)
                        (hprior.prior hrightLookup)
                      simpa [Prim.Holds, ← hleftNode, ← hrightNode] using
                        hprogram row.node (.sub leftNode rightNode) hnode
  | mul left right =>
      cases hnode : program.node? row.node with
      | none => simp [Fact.check, hnode] at hcheck
      | some operation =>
          cases operation with
          | var source => simp [Fact.check, hnode] at hcheck
          | lit value => simp [Fact.check, hnode] at hcheck
          | sub leftNode rightNode => simp [Fact.check, hnode] at hcheck
          | sq inputNode => simp [Fact.check, hnode] at hcheck
          | mul leftNode rightNode =>
              cases hleftLookup : Fact.prior? priorCount priorRev left with
              | none => simp [Fact.check, hnode, hleftLookup] at hcheck
              | some leftRow =>
                  cases hrightLookup : Fact.prior? priorCount priorRev right with
                  | none => simp [Fact.check, hnode, hleftLookup, hrightLookup] at hcheck
                  | some rightRow =>
                      simp only [Fact.check, hnode, hleftLookup, hrightLookup,
                        Bool.and_eq_true, beq_iff_eq] at hcheck
                      have hleftNode : leftRow.node = leftNode := by tauto
                      have hrightNode : rightRow.node = rightNode := by tauto
                      have hrule : Row.mul? limit row.node leftRow rightRow = some row := by
                        tauto
                      apply Row.mul?_sound hrule (hprior.prior hleftLookup)
                        (hprior.prior hrightLookup)
                      simpa [Prim.Holds, ← hleftNode, ← hrightNode] using
                        hprogram row.node (.mul leftNode rightNode) hnode
  | sq input =>
      cases hnode : program.node? row.node with
      | none => simp [Fact.check, hnode] at hcheck
      | some operation =>
          cases operation with
          | var source => simp [Fact.check, hnode] at hcheck
          | lit value => simp [Fact.check, hnode] at hcheck
          | sub leftNode rightNode => simp [Fact.check, hnode] at hcheck
          | mul leftNode rightNode => simp [Fact.check, hnode] at hcheck
          | sq inputNode =>
              cases hinputLookup : Fact.prior? priorCount priorRev input with
              | none => simp [Fact.check, hnode, hinputLookup] at hcheck
              | some inputRow =>
                  simp only [Fact.check, hnode, hinputLookup, Bool.and_eq_true,
                    beq_iff_eq] at hcheck
                  have hinputNode : inputRow.node = inputNode := by tauto
                  have hrule : Row.sq? limit row.node inputRow = some row := by tauto
                  apply Row.sq?_sound hrule (hprior.prior hinputLookup)
                  simpa [Prim.Holds, ← hinputNode] using
                    hprogram row.node (.sq inputNode) hnode
  | transport edge input =>
      cases hedgeLookup : edges[edge]? with
      | none => simp [Fact.check, hedgeLookup] at hcheck
      | some equality =>
          cases hinputLookup : Fact.prior? priorCount priorRev input with
          | none => simp [Fact.check, hedgeLookup, hinputLookup] at hcheck
          | some inputRow =>
              simp only [Fact.check, hedgeLookup, hinputLookup, Bool.and_eq_true,
                Bool.or_eq_true, beq_iff_eq] at hcheck
              apply Row.transport_sound (hprior.prior hinputLookup)
              · exact hcheck.2.1
              · exact hcheck.2.2
              · exact hedges equality (List.mem_of_getElem? hedgeLookup)

end Fact

/-- Every fact in an original-order certificate suffix has a true row. -/
def FactsHold (valuation : Valuation) (facts : List Fact) : Prop :=
  ∀ fact ∈ facts, fact.row.Holds valuation

/-- Successful bounded replay proves every row in the checked fact suffix.
The work counter affects acceptance only; it cannot affect the resulting
mathematical statement. -/
theorem checkFacts_sound {limit : EndpointLimit} {program : Program}
    {sources : List Row} {edges : List EqEdge}
    {programCount sourceCount edgeCount priorCount remainingSteps : Nat}
    {facts : List Fact} {priorRev : List Row} {valuation : Valuation}
    (hcheck : checkFacts limit program sources edges programCount sourceCount edgeCount
      priorCount remainingSteps facts priorRev = true)
    (hprogram : program.Holds valuation) (hsources : RowsHold valuation sources)
    (hedges : ∀ edge ∈ edges, valuation edge.left = valuation edge.right)
    (hprior : RowsHold valuation priorRev) : FactsHold valuation facts := by
  induction facts generalizing priorCount remainingSteps priorRev with
  | nil =>
      simp [FactsHold]
  | cons fact tail ih =>
      cases hcost : Fact.lookupCost? programCount sourceCount edgeCount priorCount fact with
      | none =>
          simp [checkFacts, hcost] at hcheck
      | some cost =>
          by_cases hbudget : cost ≤ remainingSteps
          · simp only [checkFacts, hcost, hbudget, ite_true, Bool.and_eq_true] at hcheck
            have hfact : fact.row.Holds valuation :=
              Fact.sound hcheck.1 hprogram hsources hedges hprior
            have hprior' : RowsHold valuation (fact.row :: priorRev) := by
              intro row hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hfact
              · exact hprior row hmem
            have htail : FactsHold valuation tail :=
              ih hcheck.2 hprior'
            intro current hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hfact
            · exact htail current hmem
          · simp [checkFacts, hcost, hbudget] at hcheck

namespace Certificate

/-- An accepted certificate proves its caller-selected target under the
caller-supplied source hypotheses and any valuation satisfying the reified
program. Neither sources nor target are taken from untrusted certificate
fields. -/
theorem sound {certificate : Certificate} {endpointLimit : EndpointLimit}
    {structureLimit : StructureLimit} {expectedBaseSize : Nat}
    {expectedSources : List Row} {expectedTarget : Row} {valuation : Valuation}
    (hcheck : certificate.check endpointLimit structureLimit expectedBaseSize
      expectedSources expectedTarget = true)
    (hprogram : certificate.program.Holds valuation)
    (hsources : RowsHold valuation expectedSources) :
    expectedTarget.Holds valuation := by
  unfold Certificate.check at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have hedgesChecked : certificate.edges.all
      (EqEdge.check certificate.program expectedBaseSize structureLimit.maxGeneration) =
      true := by
    tauto
  have hresult :
      (match Fact.forwardDistance? certificate.facts.length certificate.result with
      | none => false
      | some resultCost =>
          if resultCost ≤ structureLimit.maxLookupSteps then
            checkFacts endpointLimit certificate.program expectedSources certificate.edges
                certificate.program.length expectedSources.length certificate.edges.length 0
                (structureLimit.maxLookupSteps - resultCost) certificate.facts [] &&
              certificate.facts[certificate.result]?.map (fun fact => fact.row) ==
                some expectedTarget
          else
            false) = true := by
    tauto
  have hedges : ∀ edge ∈ certificate.edges,
      valuation edge.left = valuation edge.right := by
    intro edge hmem
    apply EqEdge.sound (hprogram := hprogram)
    exact (List.all_eq_true.mp hedgesChecked) edge hmem
  cases hcost : Fact.forwardDistance? certificate.facts.length certificate.result with
  | none =>
      simp [hcost] at hresult
  | some resultCost =>
      by_cases hbudget : resultCost ≤ structureLimit.maxLookupSteps
      · simp only [hcost, hbudget, ite_true, Bool.and_eq_true, beq_iff_eq] at hresult
        have hfacts : FactsHold valuation certificate.facts :=
          checkFacts_sound hresult.1 hprogram hsources hedges (by simp [RowsHold])
        cases hfactLookup : certificate.facts[certificate.result]? with
        | none => simp [hfactLookup] at hresult
        | some fact =>
            have hfact : fact.row.Holds valuation :=
              hfacts fact (List.mem_of_getElem? hfactLookup)
            have hrow : fact.row = expectedTarget := by
              simpa [hfactLookup] using hresult.2
            simpa [← hrow] using hfact
      · simp [hcost, hbudget] at hresult

end Certificate

/-! # Fixed centered-product consequence -/

/-- Concrete valuation of every node in the fixed program at a chosen real
input. Values outside the nine-node program are irrelevant and set to zero. -/
noncomputable def valuationOf (x : ℝ) : Valuation := fun current =>
  match current.index with
  | 0 => x
  | 1 => 1
  | 2 => 1 - x
  | 3 => x * (1 - x)
  | 4 => dyadic half
  | 5 => x - dyadic half
  | 6 => (x - dyadic half) ^ 2
  | 7 => dyadic quarter
  | 8 => dyadic quarter - (x - dyadic half) ^ 2
  | _ => 0

/-- Reification is inhabited for every real input: the fixed SSA program has
the concrete valuation described by its instructions. -/
theorem valuationOf_holds (x : ℝ) : extendedProgram.Holds (valuationOf x) := by
  intro current operation hlookup
  rcases current with ⟨index⟩
  have hindex : index < extendedProgram.length := by
    by_contra hnot
    have hnone : extendedProgram[index]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt hnot)
    simp [Program.node?, hnone] at hlookup
  norm_num [extendedProgram, baseProgram] at hindex
  interval_cases index <;>
    simp [Program.node?, extendedProgram, baseProgram] at hlookup <;>
    subst operation <;>
    simp [Prim.Holds, valuationOf, node, dyadic_one]
  · simpa [half] using dyadic_half.symm
  · simpa [quarter] using dyadic_quarter.symm

/-- The committed replay transports the generated centered bound back to the
original product node under exactly its caller-bound source hypothesis. -/
theorem fixture_sound {valuation : Valuation}
    (hprogram : extendedProgram.Holds valuation)
    (hsource : Contains unitRange (valuation (node 0))) :
    fixtureTarget.Holds valuation := by
  apply Certificate.sound
    (certificate := fixtureCert)
    (endpointLimit := fixtureLimit)
    (structureLimit := fixtureStructureLimit)
    (expectedBaseSize := baseProgram.length)
    (expectedSources := fixtureSources)
    (expectedTarget := fixtureTarget)
  · simpa [checkFixture] using checkFixture_eq_true
  · exact hprogram
  · intro row hmem
    simp only [fixtureSources, List.mem_singleton] at hmem
    subst row
    exact hsource

/-- The checked base program really makes node 3 denote `x * (1 - x)`. -/
theorem fixture_product_eq {valuation : Valuation}
    (hprogram : extendedProgram.Holds valuation) :
    valuation (node 3) = valuation (node 0) * (1 - valuation (node 0)) := by
  have hone : valuation (node 1) = dyadic 1 := by
    simpa [Prim.Holds] using
      hprogram (node 1) (.lit 1) (by decide +kernel)
  have hgap : valuation (node 2) = valuation (node 1) - valuation (node 0) := by
    simpa [Prim.Holds] using
      hprogram (node 2) (.sub (node 1) (node 0)) (by decide +kernel)
  have hprod : valuation (node 3) = valuation (node 0) * valuation (node 2) := by
    simpa [Prim.Holds] using
      hprogram (node 3) (.mul (node 0) (node 2)) (by decide +kernel)
  rw [hprod, hgap, hone, dyadic_one]

/-- Numeric form of the final checked fixture: for a source value in
`[0, 1]`, the original product node lies in `[0, 1/4]`. -/
theorem fixture_product_bound {valuation : Valuation}
    (hprogram : extendedProgram.Holds valuation)
    (hsource : 0 ≤ valuation (node 0) ∧ valuation (node 0) ≤ 1) :
    0 ≤ valuation (node 3) ∧ valuation (node 3) ≤ (1 / 4 : ℝ) := by
  have hsource' : Contains unitRange (valuation (node 0)) := by
    simpa [unitRange] using hsource
  have htarget := fixture_sound hprogram hsource'
  simpa only [fixtureTarget, quarterRange, Row.holds_closed_iff, dyadic_zero,
    dyadic_quarter] using htarget

/-- The same result stated directly for the source expression represented by
the checked program. -/
theorem fixture_expression_bound {valuation : Valuation}
    (hprogram : extendedProgram.Holds valuation)
    (hsource : 0 ≤ valuation (node 0) ∧ valuation (node 0) ≤ 1) :
    0 ≤ valuation (node 0) * (1 - valuation (node 0)) ∧
      valuation (node 0) * (1 - valuation (node 0)) ≤ (1 / 4 : ℝ) := by
  rw [← fixture_product_eq hprogram]
  exact fixture_product_bound hprogram hsource

/-- End-to-end consequence of the checked fixture, with the reified valuation
constructed rather than assumed. -/
theorem product_bound (x : ℝ) (hsource : 0 ≤ x ∧ x ≤ 1) :
    0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ (1 / 4 : ℝ) := by
  simpa [valuationOf, node] using
    fixture_expression_bound (valuationOf_holds x) hsource

end Hex.Interval.Experiment.Center
