/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseMap
public import HexRationalFn.Eval
import all HexRealClosure.BaseMap
import all HexPoly.Operations

public section

namespace Hex.RealClosure.BaseContext.FieldEmbedding

variable {K L : Type} [Lean.Grind.Field K] [DecidableEq K]
variable [Lean.Grind.Field L] [DecidableEq L]
variable {M : Type} [Lean.Grind.Field M] [DecidableEq M]

/-- Evaluate the stored canonical fraction after mapping its coefficients. -/
@[expose] def evaluateValue (map : FieldEmbedding K L) (x : L) (f : RationalFn K) : L :=
  let mapped := map.rationalFunctions.value f
  mapped.num.eval x / mapped.den.eval x

/-- Algebraic independence of the target variable over the coefficient image
ensures that every mapped canonical denominator is regular. -/
private theorem regular (map : FieldEmbedding K L) (x : L)
    (independent : ∀ p : DensePoly K,
      (DensePoly.Interpret.map map.value map.zero p).eval x = 0 ↔ p = 0)
    (f : RationalFn K) : RationalFn.Regular (map.rationalFunctions.value f) x := by
  unfold RationalFn.Regular
  rw [rationalFunctions_value, RationalFn.mapCoeffs_den]
  intro vanished
  exact f.den_ne_zero ((independent f.den).mp vanished)

private theorem evaluated (map : FieldEmbedding K L) (x : L)
    (independent : ∀ p : DensePoly K,
      (DensePoly.Interpret.map map.value map.zero p).eval x = 0 ↔ p = 0)
    (f : RationalFn K) :
    RationalFn.eval? (map.rationalFunctions.value f) x = some (evaluateValue map x f) :=
  (RationalFn.eval?_eq_some _ _ _).mpr ⟨regular map x independent f, rfl⟩

/-- Horner evaluation at the native formal variable is the polynomial
embedding itself, including coefficient arrays with trailing zeros. -/
theorem formal_eval (p : DensePoly K) :
    (DensePoly.Interpret.map (RationalFn.C (K := K)) RationalFn.C_eq_zero_iff p).eval
      RationalFn.X = RationalFn.ofPoly p := by
  have cons (a : K) (cs : List K) :
      DensePoly.ofList (a :: cs) =
        DensePoly.shift 1 (DensePoly.ofList cs) + DensePoly.C a := by
    apply DensePoly.ext_coeff
    intro i
    cases i with
    | zero =>
      simp [DensePoly.coeff_ofList, DensePoly.coeff_shift, DensePoly.coeff_C]
      change a = (0 : K) + a
      grind
    | succ i =>
      simp [DensePoly.coeff_ofList, DensePoly.coeff_shift, DensePoly.coeff_C]
      change cs[i]?.getD (0 : K) = cs[i]?.getD (0 : K) + 0
      exact (Lean.Grind.Semiring.add_zero _).symm
  have loop (cs : List K) :
      DensePoly.evalCoeffList (cs.map RationalFn.C) RationalFn.X =
        RationalFn.ofPoly (DensePoly.ofList cs) := by
    induction cs with
    | nil => rfl
    | cons a cs ih =>
      simp only [List.map_cons, DensePoly.evalCoeffList, ih, cons]
      rw [← DensePoly.monomial_one_mul_poly_eq_shift, RationalFn.ofPoly_add,
        RationalFn.ofPoly_mul]
      change RationalFn.ofPoly (DensePoly.ofList cs) * RationalFn.X + RationalFn.C a =
        RationalFn.X * RationalFn.ofPoly (DensePoly.ofList cs) + RationalFn.C a
      grind
  rw [DensePoly.eval, DensePoly.Interpret.map_list]
  exact (loop p.toList).trans (congrArg RationalFn.ofPoly (DensePoly.ofList_toList p))

/-- The formal variable is algebraically independent over the embedded
coefficient field. This is a native polynomial identity, not a model premise. -/
theorem formal_independent (p : DensePoly K) :
    (DensePoly.Interpret.map (RationalFn.C (K := K)) RationalFn.C_eq_zero_iff p).eval
      RationalFn.X = 0 ↔ p = 0 := by
  rw [formal_eval]
  constructor
  · intro vanished
    exact RationalFn.ofPoly_injective vanished
  · intro vanished
    subst p
    rfl

/-- Coefficient transport retains the native formal variable. -/
theorem rationalFunctions_X (map : FieldEmbedding K L) :
    map.rationalFunctions.value RationalFn.X = RationalFn.X := by
  rw [rationalFunctions_value]
  apply RationalFn.ext
  · change DensePoly.Interpret.map map.value map.zero (DensePoly.monomial 1 1) =
      DensePoly.monomial 1 1
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.Interpret.map_coeff, DensePoly.coeff_monomial, DensePoly.coeff_monomial]
    split
    · exact map.one
    · exact (map.zero 0).mpr rfl
  · change DensePoly.Interpret.map map.value map.zero (1 : DensePoly K) = 1
    exact DensePoly.Interpret.map_one map.value map.zero map.one

/-- Coefficient transport preserves a polynomial fraction with denominator one. -/
theorem rationalFunctions_ofPoly (map : FieldEmbedding K L) (p : DensePoly K) :
    map.rationalFunctions.value (RationalFn.ofPoly p) =
      RationalFn.ofPoly (DensePoly.Interpret.map map.value map.zero p) := by
  rw [rationalFunctions_value]
  apply RationalFn.ext
  · rfl
  · change DensePoly.Interpret.map map.value map.zero (1 : DensePoly K) = 1
    exact DensePoly.Interpret.map_one map.value map.zero map.one

/-- Substitution maps an embedded source coefficient through the coefficient map. -/
theorem evaluateValue_C (map : FieldEmbedding K L) (x : L) (a : K) :
    evaluateValue map x (RationalFn.C a) = map.value a := by
  unfold evaluateValue
  rw [rationalFunctions_value, RationalFn.mapCoeffs_C]
  change (DensePoly.C (map.value a)).eval x / (DensePoly.C (1 : L)).eval x = _
  rw [DensePoly.eval_C_semiring, DensePoly.eval_C_semiring]
  grind

/-- Substitution sends the formal source variable to the requested target value. -/
theorem evaluateValue_X (map : FieldEmbedding K L) (x : L) :
    evaluateValue map x RationalFn.X = x := by
  unfold evaluateValue
  rw [rationalFunctions_X]
  change (DensePoly.monomial 1 (1 : L)).eval x / (DensePoly.C (1 : L)).eval x = x
  rw [DensePoly.eval_monomial_semiring, DensePoly.eval_C_semiring]
  grind

private theorem numerator_denominator (f : RationalFn K) :
    f * RationalFn.ofPoly f.den = RationalFn.ofPoly f.num := by
  have product := (RationalFn.represents_self f).mul (RationalFn.represents_ofPoly f.den)
  apply product.eq
    (hq := DensePoly.mul_ne_zero f.den_ne_zero (DensePoly.monic_ne_zero DensePoly.monic_one))
  change f.num * (f.den * 1) = (f.num * f.den) * 1
  grind

/-- A finite family of canonical fractions has one nonzero polynomial
denominator that clears every member. -/
theorem clear_denominators (fs : List (RationalFn K)) :
    ∃ d : DensePoly K, d ≠ 0 ∧ ∀ f ∈ fs, ∃ p : DensePoly K,
      f * RationalFn.ofPoly d = RationalFn.ofPoly p := by
  induction fs with
  | nil =>
    exact ⟨1, DensePoly.monic_ne_zero DensePoly.monic_one, fun _ member => by cases member⟩
  | cons first rest ih =>
    obtain ⟨d, nonzero, clears⟩ := ih
    refine ⟨first.den * d, DensePoly.mul_ne_zero first.den_ne_zero nonzero, ?_⟩
    intro f member
    rcases List.mem_cons.mp member with same | later
    · subst f
      refine ⟨first.num * d, ?_⟩
      rw [RationalFn.ofPoly_mul, ← Lean.Grind.Semiring.mul_assoc,
        numerator_denominator, ← RationalFn.ofPoly_mul]
    · obtain ⟨p, cleared⟩ := clears f later
      refine ⟨p * first.den, ?_⟩
      calc
        f * RationalFn.ofPoly (first.den * d) =
            (f * RationalFn.ofPoly d) * RationalFn.ofPoly first.den := by
          rw [RationalFn.ofPoly_mul]
          grind
        _ = RationalFn.ofPoly (p * first.den) := by
          rw [cleared, ← RationalFn.ofPoly_mul]

/-- Horner combination of coefficient polynomials in a second variable. -/
@[expose] def combine (map : FieldEmbedding K L) (x : L) :
    List (DensePoly K) → DensePoly L
  | [] => 0
  | p :: ps => DensePoly.scale x (combine map x ps) + DensePoly.Interpret.map map.value map.zero p

private theorem combine_coeff (map : FieldEmbedding K L) (x : L)
    (ps : List (DensePoly K)) (j : Nat) :
    (combine map x ps).coeff j =
      DensePoly.evalCoeffList ((ps.map (fun p => p.coeff j)).map map.value) x := by
  induction ps with
  | nil => exact DensePoly.coeff_zero j
  | cons p ps ih =>
    rw [combine, DensePoly.coeff_add _ _ j (by change (0 : L) + 0 = 0; grind)]
    simp only [DensePoly.coeff_scale_semiring,
      DensePoly.Interpret.map_coeff, List.map_cons, DensePoly.evalCoeffList, ih]
    grind

private theorem map_list_eval (map : FieldEmbedding K L) (x : L) (cs : List K) :
    (DensePoly.Interpret.map map.value map.zero (DensePoly.ofList cs)).eval x =
      DensePoly.evalCoeffList (cs.map map.value) x := by
  change (DensePoly.Interpret.map map.value map.zero (DensePoly.ofCoeffs cs.toArray)).eval x = _
  rw [DensePoly.Interpret.map_ofCoeffs]
  rw [List.map_toArray]
  change (DensePoly.ofList (cs.map map.value)).eval x = _
  apply DensePoly.eval_ofList_eq_evalCoeffList
  change (0 : L) * x + 0 = 0
  grind

/-- Transcendence of the second variable prevents a nontrivial finite
combination of coefficient polynomials from vanishing. -/
theorem combine_eq_zero (map : FieldEmbedding K L) (x : L)
    (independent : ∀ p : DensePoly K,
      (DensePoly.Interpret.map map.value map.zero p).eval x = 0 ↔ p = 0)
    (ps : List (DensePoly K)) : combine map x ps = 0 ↔ ∀ p ∈ ps, p = 0 := by
  constructor
  · intro vanished p member
    apply DensePoly.ext_coeff
    intro j
    have coordinate : DensePoly.ofList (ps.map (fun p => p.coeff j)) = 0 := by
      apply (independent _).mp
      rw [map_list_eval, ← combine_coeff, vanished, DensePoly.coeff_zero]
    obtain ⟨i, atIndex⟩ := List.getElem?_of_mem member
    have equal := congrArg (fun polynomial : DensePoly K => polynomial.coeff i) coordinate
    rw [DensePoly.coeff_ofList, DensePoly.coeff_zero] at equal
    change ((ps.map (fun p => p.coeff j))[i]?).getD (0 : K) = 0 at equal
    rw [List.getElem?_map, atIndex] at equal
    exact equal
  · intro empty
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      have head := empty p List.mem_cons_self
      have tail := ih (fun q member => empty q (List.mem_cons_of_mem _ member))
      rw [combine, head, tail]
      apply DensePoly.ext_coeff
      intro j
      rw [DensePoly.coeff_add _ _ j (by change (0 : L) + 0 = 0; grind), DensePoly.coeff_scale_semiring,
        DensePoly.Interpret.map_coeff, DensePoly.coeff_zero, DensePoly.coeff_zero]
      have mappedZero := (map.zero 0).mpr rfl
      rw [mappedZero]
      change x * (0 : L) + 0 = 0
      grind

private inductive Cleared (d : DensePoly K) :
    List (RationalFn K) → List (DensePoly K) → Prop
  | nil : Cleared d [] []
  | cons {f : RationalFn K} {p : DensePoly K}
      {fs : List (RationalFn K)} {ps : List (DensePoly K)}
      (head : f * RationalFn.ofPoly d = RationalFn.ofPoly p)
      (tail : Cleared d fs ps) : Cleared d (f :: fs) (p :: ps)

private theorem clear_pairs (fs : List (RationalFn K)) (d : DensePoly K)
    (clears : ∀ f ∈ fs, ∃ p : DensePoly K,
      f * RationalFn.ofPoly d = RationalFn.ofPoly p) :
    ∃ ps : List (DensePoly K),
      Cleared d fs ps := by
  induction fs with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
    obtain ⟨p, cleared⟩ := clears first List.mem_cons_self
    obtain ⟨ps, restCleared⟩ := ih (fun f member => clears f (List.mem_cons_of_mem _ member))
    exact ⟨p :: ps, .cons cleared restCleared⟩

private theorem clear_horner (map : FieldEmbedding K L) (x : L) (d : DensePoly K)
    (fs : List (RationalFn K)) (ps : List (DensePoly K))
    (cleared : Cleared d fs ps) :
    DensePoly.evalCoeffList (fs.map map.rationalFunctions.value) (RationalFn.C x) *
        map.rationalFunctions.value (RationalFn.ofPoly d) =
      RationalFn.ofPoly (combine map x ps) := by
  induction cleared with
  | nil =>
    change (0 : RationalFn L) * _ = 0
    grind
  | cons equal rest ih =>
    simp only [List.map_cons, DensePoly.evalCoeffList, combine]
    rw [RationalFn.ofPoly_add, DensePoly.scale_eq_C_mul, RationalFn.ofPoly_mul]
    have head := congrArg map.rationalFunctions.value equal
    rw [map.rationalFunctions.mul] at head
    simp only [rationalFunctions_ofPoly] at head ih ⊢
    change _ * _ = RationalFn.C x * RationalFn.ofPoly _ + RationalFn.ofPoly _
    grind

private theorem cleared_zero (d : DensePoly K) (nonzero : d ≠ 0)
    (fs : List (RationalFn K)) (ps : List (DensePoly K))
    (cleared : Cleared d fs ps) (empty : ∀ p ∈ ps, p = 0) :
    ∀ f ∈ fs, f = 0 := by
  have denominator : RationalFn.ofPoly d ≠ 0 :=
    fun vanished => nonzero (RationalFn.ofPoly_injective vanished)
  induction cleared with
  | nil => intro f member; cases member
  | cons equal rest ih =>
    intro f member
    rcases List.mem_cons.mp member with same | later
    · subst f
      rw [empty _ List.mem_cons_self, RationalFn.ofPoly_zero] at equal
      exact (Lean.Grind.Field.of_mul_eq_zero equal).resolve_right denominator
    · exact ih (fun p member => empty p (List.mem_cons_of_mem _ member)) f later

/-- A new formal variable preserves transcendence of an existing target
value over the coefficient image. This supplies variable substitution across
a rational-function level without an interpretation in an ambient field. -/
theorem rationalFunctions_independent (map : FieldEmbedding K L) (x : L)
    (independent : ∀ p : DensePoly K,
      (DensePoly.Interpret.map map.value map.zero p).eval x = 0 ↔ p = 0)
    (p : DensePoly (RationalFn K)) :
    (DensePoly.Interpret.map map.rationalFunctions.value map.rationalFunctions.zero p).eval
      (RationalFn.C x) = 0 ↔ p = 0 := by
  constructor
  · intro vanished
    obtain ⟨d, nonzero, clears⟩ := clear_denominators p.toList
    obtain ⟨ps, cleared⟩ := clear_pairs p.toList d clears
    have evaluated := clear_horner map x d p.toList ps cleared
    rw [DensePoly.eval, DensePoly.Interpret.map_list] at vanished
    rw [vanished, Lean.Grind.Semiring.zero_mul] at evaluated
    have combination : combine map x ps = 0 := RationalFn.ofPoly_injective evaluated.symm
    have zeros := cleared_zero d nonzero p.toList ps cleared
      ((combine_eq_zero map x independent ps).mp combination)
    apply DensePoly.ext_coeff
    intro j
    rw [DensePoly.coeff_zero]
    by_cases bound : j < p.toList.length
    · have value := zeros (p.toList[j]'bound) (List.getElem_mem bound)
      have coefficient := DensePoly.toList_getD_eq_coeff p j
      simp only [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos bound] at coefficient
      exact coefficient.symm.trans value
    · exact DensePoly.coeff_eq_zero_of_size_le p (by
        rw [← DensePoly.length_toList]
        omega)
  · intro vanished
    subst p
    rw [(DensePoly.Interpret.map_eq_zero _ _ _).mpr rfl]
    exact DensePoly.eval_zero _

/-- Substitute a target variable algebraically independent over the source
coefficient image. The native evaluation preserves total field operations.
Context factories must derive independence for their actual formal variables. -/
def evaluate (map : FieldEmbedding K L) (x : L)
    (independent : ∀ p : DensePoly K,
      (DensePoly.Interpret.map map.value map.zero p).eval x = 0 ↔ p = 0) :
    FieldEmbedding (RationalFn K) L := by
  have zero (f : RationalFn K) : evaluateValue map x f = 0 ↔ f = 0 := by
    have denominator := regular map x independent f
    change (map.rationalFunctions.value f).den.eval x ≠ 0 at denominator
    have fraction : evaluateValue map x f = 0 ↔
        (map.rationalFunctions.value f).num.eval x = 0 := by
      unfold evaluateValue
      simp only [Lean.Grind.Field.div_eq_mul_inv]
      have cancel := Lean.Grind.Field.mul_inv_cancel denominator
      constructor <;> intro vanished <;> grind
    rw [fraction, rationalFunctions_value, RationalFn.mapCoeffs_num,
      independent, RationalFn.num_eq_zero]
  have one : evaluateValue map x 1 = 1 := by
    unfold evaluateValue
    rw [map.rationalFunctions.one]
    change (1 : DensePoly L).eval x / (1 : DensePoly L).eval x = 1
    change (DensePoly.C (1 : L)).eval x / (DensePoly.C (1 : L)).eval x = 1
    rw [DensePoly.eval_C_semiring]
    grind
  refine ⟨evaluateValue map x, zero, one, ?_, ?_, ?_⟩
  · intro a b
    have result := RationalFn.eval?_sub (evaluated map x independent a)
      (evaluated map x independent b)
    rw [← map.rationalFunctions.sub] at result
    exact Option.some.inj ((evaluated map x independent (a - b)).symm.trans result)
  · intro a b
    have result := RationalFn.eval?_mul (evaluated map x independent a)
      (evaluated map x independent b)
    rw [← map.rationalFunctions.mul] at result
    exact Option.some.inj ((evaluated map x independent (a * b)).symm.trans result)
  · intro a
    by_cases vanished : evaluateValue map x a = 0
    · have source := (zero a).mp vanished
      subst a
      have empty := (zero (0 : RationalFn K)).mpr rfl
      simp only [Lean.Grind.Field.inv_zero, empty]
    · have result := RationalFn.eval?_inv (evaluated map x independent a) vanished
      rw [← map.rationalFunctions.inv] at result
      exact Option.some.inj ((evaluated map x independent a⁻¹).symm.trans result)

/-- Embeddings of a rational-function field agree when they agree on the
coefficient field and formal variable. The proof uses the stored canonical
numerator and denominator, so it also covers totalized inverses. -/
theorem rationalFunctions_ext (first next : FieldEmbedding (RationalFn K) L)
    (coefficients : ∀ a : K, first.value (RationalFn.C a) = next.value (RationalFn.C a))
    (generator : first.value RationalFn.X = next.value RationalFn.X) : first = next := by
  have polynomial (p : DensePoly K) :
      first.value (RationalFn.ofPoly p) = next.value (RationalFn.ofPoly p) := by
    have loop (cs : List K) :
        first.value (DensePoly.evalCoeffList (cs.map RationalFn.C) RationalFn.X) =
          next.value (DensePoly.evalCoeffList (cs.map RationalFn.C) RationalFn.X) := by
      induction cs with
      | nil => exact ((first.zero 0).mpr rfl).trans ((next.zero 0).mpr rfl).symm
      | cons a cs ih =>
        simp only [List.map_cons, DensePoly.evalCoeffList, first.add, next.add,
          first.mul, next.mul, ih, coefficients, generator]
    rw [← formal_eval, DensePoly.eval, DensePoly.Interpret.map_list]
    exact loop p.toList
  apply value_ext
  intro f
  have firstFraction := congrArg first.value (numerator_denominator f)
  have nextFraction := congrArg next.value (numerator_denominator f)
  rw [first.mul] at firstFraction
  rw [next.mul, ← polynomial f.den, ← polynomial f.num] at nextFraction
  have denominator : first.value (RationalFn.ofPoly f.den) ≠ 0 := by
    intro vanished
    exact f.den_ne_zero (RationalFn.ofPoly_injective ((first.zero _).mp vanished))
  grind

/-- Lifting coefficient embeddings commutes with their actual composition. -/
theorem rationalFunctions_comp (first : FieldEmbedding K L) (next : FieldEmbedding L M) :
    first.rationalFunctions.comp next.rationalFunctions = (first.comp next).rationalFunctions := by
  apply value_ext
  intro f
  rw [comp_value]
  apply RationalFn.ext
  · simp only [rationalFunctions_value, RationalFn.mapCoeffs_num]
    apply DensePoly.ext_coeff
    intro i
    simp only [DensePoly.Interpret.map_coeff, comp_value]
  · simp only [rationalFunctions_value, RationalFn.mapCoeffs_den]
    apply DensePoly.ext_coeff
    intro i
    simp only [DensePoly.Interpret.map_coeff, comp_value]

private theorem constants_independent (p : DensePoly K) :
    (DensePoly.Interpret.map (constants K).value (constants K).zero p).eval
      RationalFn.X = 0 ↔ p = 0 := by
  change (DensePoly.Interpret.map RationalFn.C RationalFn.C_eq_zero_iff p).eval
    RationalFn.X = 0 ↔ p = 0
  exact formal_independent p

/-- Exchange two adjacent formal variables. Coefficients stay in the original
field; the old outer variable becomes the inner variable and conversely. -/
def swap (K : Type) [Lean.Grind.Field K] [DecidableEq K] :
    FieldEmbedding (RationalFn (RationalFn K)) (RationalFn (RationalFn K)) :=
  (constants K).rationalFunctions.evaluate (RationalFn.C RationalFn.X)
    (rationalFunctions_independent (constants K) RationalFn.X constants_independent)

private theorem swap_value_proof (f : RationalFn (RationalFn K)) :
    (swap K).value f =
      evaluateValue (constants K).rationalFunctions (RationalFn.C RationalFn.X) f := rfl

/-- Swapping sends the old outer variable to the new inner variable. -/
theorem swap_outer : (swap K).value RationalFn.X = RationalFn.C RationalFn.X := by
  rw [swap_value_proof, evaluateValue_X]

/-- Swapping sends the old inner variable to the new outer variable. -/
theorem swap_inner : (swap K).value (RationalFn.C RationalFn.X) = RationalFn.X := by
  rw [swap_value_proof, evaluateValue_C, rationalFunctions_X]

/-- The exchange retains every coefficient from the original field. -/
theorem swap_coefficient (a : K) :
    (swap K).value (RationalFn.C (RationalFn.C a)) = RationalFn.C (RationalFn.C a) := by
  rw [swap_value_proof, evaluateValue_C, rationalFunctions_value,
    RationalFn.mapCoeffs_C, constants_value]

/-- An old outer coefficient becomes a coefficientwise inclusion into the
new outer rational-function field. -/
theorem swap_constants (f : RationalFn K) :
    (swap K).value (RationalFn.C f) = (constants K).rationalFunctions.value f := by
  rw [swap_value_proof, evaluateValue_C]

/-- Swapping the coefficientwise inclusion recovers constant inclusion. -/
theorem swap_transport :
    (constants K).rationalFunctions.comp (swap K) = constants (RationalFn K) := by
  apply rationalFunctions_ext
  · intro a
    rw [comp_value, rationalFunctions_value, RationalFn.mapCoeffs_C,
      constants_value, swap_coefficient, constants_value]
  · rw [comp_value, rationalFunctions_X, swap_outer, constants_value]

/-- Two adjacent exchanges restore every canonical fraction. -/
theorem swap_involution : (swap K).comp (swap K) = identity (RationalFn (RationalFn K)) := by
  apply rationalFunctions_ext
  · intro f
    rw [comp_value, swap_constants, identity_value]
    have restored := congrArg (fun map : FieldEmbedding (RationalFn K)
      (RationalFn (RationalFn K)) => map.value f) (swap_transport (K := K))
    simpa only [comp_value, constants_value] using restored
  · rw [comp_value, swap_outer, swap_inner, identity_value]

end Hex.RealClosure.BaseContext.FieldEmbedding

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.evaluate

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.formal_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.formal_independent

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.rationalFunctions_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.rationalFunctions_independent

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.swap

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.swap_involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.swap_involution
