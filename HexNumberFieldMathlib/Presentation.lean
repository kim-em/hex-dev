/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Roots
public import HexNumberFieldMathlib.AlgebraicPoly
public import Mathlib.FieldTheory.PrimitiveElement

public section

/-!
# Common fixed-field presentations

Semantic totality and value preservation for the checked arithmetic used by
the algebraic-coefficient root driver's common-field construction.
-/

namespace Hex.AlgebraicPoly.Common

private theorem rationalDense_ne_zero (q : Rat) :
    DensePoly.ofList [-q, 1] ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : DensePoly Rat => f.coeff 1) hzero
  simp at hcoeff

private theorem rationalPrimitive_ne_zero (q : Rat) :
    ZPoly.ratPolyPrimitivePart (DensePoly.ofList [-q, 1]) ≠ 0 := by
  let f : DensePoly Rat := DensePoly.ofList [-q, 1]
  obtain ⟨unit, hunit⟩ := ZPoly.ratPolyPrimitivePart_rational_associate f
  intro hzero
  rw [hzero] at hunit
  simp at hunit
  exact rationalDense_ne_zero q hunit

private theorem rationalPrimitive_isRoot (q : Rat) :
    (HexRootsMathlib.toPolyℂ
      (ZPoly.ratPolyPrimitivePart (DensePoly.ofList [-q, 1]))).IsRoot
        (q : ℂ) := by
  let f : DensePoly Rat := DensePoly.ofList [-q, 1]
  let p := ZPoly.ratPolyPrimitivePart f
  obtain ⟨unit, hunit⟩ := ZPoly.ratPolyPrimitivePart_rational_associate f
  have hunitNe : unit ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
    exact rationalDense_ne_zero q hunit
  have hpoly := congrArg HexPolyMathlib.toPolynomial hunit
  have hfpoly : HexPolyMathlib.toPolynomial f =
      Polynomial.C (-q) + Polynomial.X := by
    ext n
    rw [HexPolyMathlib.coeff_toPolynomial]
    cases n with
    | zero => simp [f]
    | succ n =>
        cases n with
        | zero => simp [f]
        | succ n =>
            simp only [Polynomial.coeff_add, Polynomial.coeff_C,
              Polynomial.coeff_X]
            simp [f, DensePoly.coeff_ofList]
            rfl
  rw [HexPolyMathlib.toPolynomial_scale] at hpoly
  have heval := congrArg (Polynomial.eval q) hpoly
  rw [hfpoly] at heval
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    neg_add_cancel, Polynomial.eval_mul] at heval
  have hpRat : (HexPolyZMathlib.toPolyℚ p).eval q = 0 := by
    rw [← HexPolyZMathlib.toPolynomial_toRatPoly]
    exact (mul_eq_zero.mp heval.symm).resolve_left hunitNe
  have hcomp :
      (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
  have hmapped : ((HexPolyZMathlib.toPolyℚ p).map
      (algebraMap Rat ℂ)).eval (q : ℂ) = 0 := by
    calc
      ((HexPolyZMathlib.toPolyℚ p).map
          (algebraMap Rat ℂ)).eval (q : ℂ) =
          algebraMap Rat ℂ ((HexPolyZMathlib.toPolyℚ p).eval q) := by
            exact Polynomial.eval_map_apply (algebraMap Rat ℂ) q
      _ = 0 := by rw [hpRat, map_zero]
  simpa [p, f, HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ,
    Polynomial.map_map, hcomp] using hmapped

/-- Checked canonical construction of a rational algebraic number is total. -/
theorem rational?_isSome (q : Rat) :
    (rational? q).isSome := by
  unfold rational?
  split
  · simp
  · let p := ZPoly.ratPolyPrimitivePart (DensePoly.ofList [-q, 1])
    let prec : Int := separationDepth (ZPoly.squareFreeCore p)
    let ball := DyadicComplexBall.ofRat q prec
    have hsepNat : mahlerPrec (ZPoly.squareFreeCore p) ≤
        separationDepth (ZPoly.squareFreeCore p) := by
      rw [separationDepth]
      omega
    have hsepInt : (mahlerPrec (ZPoly.squareFreeCore p) : Int) ≤
        separationDepth (ZPoly.squareFreeCore p) := by
      exact_mod_cast hsepNat
    have hradius : ball.realRadius ≤
        (2 : ℝ) ^ (-(mahlerPrec (ZPoly.squareFreeCore p) : ℤ)) := by
      calc
        ball.realRadius ≤ (2 : ℝ) ^ (-prec) :=
          DyadicComplexBall.realRadius_ofRat_le q prec
        _ ≤ (2 : ℝ) ^
            (-(mahlerPrec (ZPoly.squareFreeCore p) : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hrootSome := AlgebraicRoot.ofEliminant?_isSome p
      (fun requested => some (DyadicComplexBall.ofRat q requested))
      (z := (q : ℂ)) (by simpa [p] using rationalPrimitive_ne_zero q)
      (by simpa [p] using rationalPrimitive_isRoot q) ball
      (by rfl) (by exact DyadicComplexBall.ofRat_mem q prec) hradius
    obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp hrootSome
    change (AlgebraicRoot.ofEliminant? p
      (fun requested => some (DyadicComplexBall.ofRat q requested)) >>=
        fun root => root.exact?).isSome
    rw [hroot]
    simpa using AlgebraicRoot.exact?_isSome root

/-- Checked canonical construction of a rational preserves its value. -/
theorem rational?_sound (q : Rat) {a : AlgebraicNumber}
    (h : rational? q = some a) :
    a.toComplex = (q : ℂ) := by
  unfold rational? at h
  split at h
  · rename_i hzero
    have ha := Option.some.inj h
    subst a
    simp [hzero]
  · let p := ZPoly.ratPolyPrimitivePart (DensePoly.ofList [-q, 1])
    obtain ⟨root, hroot, hexact⟩ := Option.bind_eq_some_iff.mp h
    rw [AlgebraicRoot.exact?_sound root hexact]
    apply AlgebraicRoot.ofEliminant?_sound p
      (fun requested => some (DyadicComplexBall.ofRat q requested)) hroot
      (by simpa [p] using rationalPrimitive_isRoot q)
    intro ball hball
    have hballEq := Option.some.inj hball
    subst ball
    exact DyadicComplexBall.ofRat_mem q _

/-- Checked canonical addition is total. -/
theorem add?_isSome (a b : AlgebraicNumber) :
    (add? a b).isSome := by
  unfold add?
  cases hroot : a.toRoot.add? b.toRoot with
  | none =>
      have hsome := AlgebraicRoot.add?_isSome a.toRoot b.toRoot
      simp [hroot] at hsome
  | some root =>
      simpa [hroot] using AlgebraicRoot.exact?_isSome root

/-- Checked canonical addition preserves the represented complex value. -/
theorem add?_sound (a b : AlgebraicNumber) {c : AlgebraicNumber}
    (h : add? a b = some c) :
    c.toComplex = a.toComplex + b.toComplex := by
  unfold add? at h
  obtain ⟨root, hroot, hexact⟩ := Option.bind_eq_some_iff.mp h
  rw [AlgebraicRoot.exact?_sound root hexact,
    AlgebraicRoot.add?_sound a.toRoot b.toRoot hroot,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Checked canonical multiplication is total. -/
theorem mul?_isSome (a b : AlgebraicNumber) :
    (mul? a b).isSome := by
  unfold mul?
  cases hroot : a.toRoot.mul? b.toRoot with
  | none =>
      have hsome := AlgebraicRoot.mul?_isSome a.toRoot b.toRoot
      simp [hroot] at hsome
  | some root =>
      simpa [hroot] using AlgebraicRoot.exact?_isSome root

/-- Checked canonical multiplication preserves the represented complex value. -/
theorem mul?_sound (a b : AlgebraicNumber) {c : AlgebraicNumber}
    (h : mul? a b = some c) :
    c.toComplex = a.toComplex * b.toComplex := by
  unfold mul? at h
  obtain ⟨root, hroot, hexact⟩ := Option.bind_eq_some_iff.mp h
  rw [AlgebraicRoot.exact?_sound root hexact,
    AlgebraicRoot.mul?_sound a.toRoot b.toRoot hroot,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Checked integer scaling is total. -/
theorem scale?_isSome (c : Int) (a : AlgebraicNumber) :
    (scale? c a).isSome := by
  unfold scale?
  obtain ⟨scalar, hscalar⟩ := Option.isSome_iff_exists.mp
    (rational?_isSome (c : Rat))
  rw [hscalar]
  simpa using mul?_isSome scalar a

/-- A successful checked integer scaling has the expected value. -/
theorem scale?_sound (c : Int) (a : AlgebraicNumber) {b : AlgebraicNumber}
    (h : scale? c a = some b) :
    b.toComplex = (c : ℂ) * a.toComplex := by
  unfold scale? at h
  obtain ⟨scalar, hscalar, hmul⟩ := Option.bind_eq_some_iff.mp h
  rw [mul?_sound scalar a hmul, rational?_sound (c : Rat) hscalar]
  norm_num

/-- A checked primitive-element shift is total. -/
theorem shift?_isSome (theta alpha : AlgebraicNumber) (c : Int) :
    (shift? theta alpha c).isSome := by
  unfold shift?
  split
  · simp
  · unfold scale?
    obtain ⟨scalar, hscalar⟩ := Option.isSome_iff_exists.mp
      (rational?_isSome (c : Rat))
    rw [hscalar]
    change (mul? scalar alpha >>= fun scaled => add? theta scaled).isSome
    obtain ⟨scaled, hscaled⟩ := Option.isSome_iff_exists.mp
      (mul?_isSome scalar alpha)
    rw [hscaled]
    simpa using add?_isSome theta scaled

/-- A successful checked primitive-element shift has the expected value. -/
theorem shift?_sound (theta alpha : AlgebraicNumber) (c : Int)
    {candidate : AlgebraicNumber}
    (h : shift? theta alpha c = some candidate) :
    candidate.toComplex = theta.toComplex + (c : ℂ) * alpha.toComplex := by
  unfold shift? at h
  split at h
  · rename_i hzero
    have hc := Option.some.inj h
    subst candidate
    simp [hzero]
  · obtain ⟨scaled, hscaled, hadd⟩ := Option.bind_eq_some_iff.mp h
    rw [add?_sound theta scaled hadd, scale?_sound c alpha hscaled]

/-- The executable degree is the degree of the rational minimal polynomial. -/
theorem degree_eq_minpoly (a : AlgebraicNumber) :
    degree a = (minpoly Rat a.toComplex).natDegree := by
  have hlc : (a.p.leadingCoeff : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt a.pos_lc)
  calc
    degree a = (HexPolyZMathlib.toPolyℚ a.p).natDegree := by
      unfold degree HexPolyZMathlib.toPolyℚ
      rw [Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom Rat)),
        HexPolyMathlib.natDegree_toPolynomial]
    _ = ((a.p.leadingCoeff : Rat)⁻¹ •
        HexPolyZMathlib.toPolyℚ a.p).natDegree := by
      symm
      exact Polynomial.natDegree_smul _ (inv_ne_zero hlc)
    _ = (minpoly Rat a.toComplex).natDegree := by
      rw [AlgebraicNumber.p_eq_minpoly]

/-- The complex value represented by a canonical algebraic number is
algebraic over the rationals. -/
theorem isIntegral_toComplex (a : AlgebraicNumber) :
    IsIntegral Rat a.toComplex := by
  apply minpoly.ne_zero_iff.mp
  rw [← AlgebraicNumber.p_eq_minpoly]
  have hlc : (a.p.leadingCoeff : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt a.pos_lc)
  have hp : a.p ≠ 0 := by
    intro hzero
    have hdegree := a.pos_degree
    rw [hzero] at hdegree
    simp at hdegree
  exact smul_ne_zero (inv_ne_zero hlc)
    (HexPolyZMathlib.toPolyℚ_ne_zero hp)

/-- Every canonical algebraic number has positive degree. -/
theorem degree_pos (a : AlgebraicNumber) : 0 < degree a := by
  exact a.pos_degree

@[simp] private theorem signedShift_odd (n : Nat) :
    signedShift (2 * n + 1) = Int.ofNat (n + 1) := by
  simp [signedShift]

@[simp] private theorem signedShift_zero : signedShift 0 = 0 := rfl

@[simp] private theorem signedShift_even_succ (n : Nat) :
    signedShift (2 * n + 2) = -Int.ofNat (n + 1) := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, signedShift]
  simp [hdiv]

@[simp] private theorem signedShift_even_pos (n : Nat) :
    signedShift (2 * (n + 1)) = -Int.ofNat (n + 1) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    signedShift_even_succ]

/-- The deterministic signed-shift enumeration never repeats a scalar. -/
theorem signedShift_injective : Function.Injective signedShift := by
  intro i j hij
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
  · cases a with
    | zero =>
        obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' j
        · cases b with
          | zero => rfl
          | succ b =>
              simp only [signedShift_even_pos, Nat.mul_zero, signedShift_zero] at hij
              have hpos : (0 : Int) < Int.ofNat (b + 1) := by
                exact Int.ofNat_lt.mpr (Nat.succ_pos b)
              omega
        · simp only [signedShift_odd, Nat.mul_zero, signedShift_zero] at hij
          have hpos : (0 : Int) < Int.ofNat (b + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos b)
          omega
    | succ a =>
        obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' j
        · cases b with
          | zero =>
              simp only [signedShift_even_pos, Nat.mul_zero, signedShift_zero] at hij
              have hpos : (0 : Int) < Int.ofNat (a + 1) := by
                exact Int.ofNat_lt.mpr (Nat.succ_pos a)
              omega
          | succ b =>
              simp only [signedShift_even_pos] at hij
              have hab : a + 1 = b + 1 := by
                exact Int.ofNat.inj (neg_injective hij)
              omega
        · simp only [signedShift_even_pos, signedShift_odd] at hij
          have ha : (0 : Int) < Int.ofNat (a + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos a)
          have hb : (0 : Int) < Int.ofNat (b + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos b)
          omega
  · obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' j
    · cases b with
      | zero =>
          simp only [signedShift_odd, Nat.mul_zero, signedShift_zero] at hij
          have hpos : (0 : Int) < Int.ofNat (a + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos a)
          omega
      | succ b =>
          simp only [signedShift_odd, signedShift_even_pos] at hij
          have ha : (0 : Int) < Int.ofNat (a + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos a)
          have hb : (0 : Int) < Int.ofNat (b + 1) := by
            exact Int.ofNat_lt.mpr (Nat.succ_pos b)
          omega
    · simp only [signedShift_odd] at hij
      have hab : a + 1 = b + 1 := by
        exact Int.ofNat.inj hij
      omega

private theorem extendShiftStep_some (theta alpha : AlgebraicNumber)
    (best : Option ShiftCandidate) (k : Nat) :
    ∃ candidate, extendShiftStep theta alpha best k = some (some candidate) := by
  obtain ⟨shifted, hshifted⟩ := Option.isSome_iff_exists.mp
    (shift?_isSome theta alpha (signedShift k))
  simp only [extendShiftStep, hshifted]
  cases best with
  | none => exact ⟨⟨signedShift k, shifted⟩, rfl⟩
  | some current =>
      by_cases hdegree : degree current.value < degree shifted
      · exact ⟨⟨signedShift k, shifted⟩, by simp [hdegree]⟩
      · exact ⟨current, by simp [hdegree]⟩

private theorem extendShiftFold_fromSome (theta alpha : AlgebraicNumber)
    (indices : List Nat) (current : ShiftCandidate) :
    ∃ candidate, indices.foldlM (extendShiftStep theta alpha) (some current) =
      some (some candidate) := by
  induction indices generalizing current with
  | nil => exact ⟨current, rfl⟩
  | cons k indices ih =>
      obtain ⟨next, hnext⟩ :=
        extendShiftStep_some theta alpha (some current) k
      rw [List.foldlM_cons, hnext]
      exact ih next

private theorem extendShiftFold_nonempty (theta alpha : AlgebraicNumber)
    (indices : List Nat) (hnonempty : indices ≠ []) :
    ∃ candidate, indices.foldlM (extendShiftStep theta alpha) none =
      some (some candidate) := by
  cases indices with
  | nil => exact (hnonempty rfl).elim
  | cons k indices =>
      obtain ⟨first, hfirst⟩ := extendShiftStep_some theta alpha none k
      rw [List.foldlM_cons, hfirst]
      exact extendShiftFold_fromSome theta alpha indices first

/-- The shift-retaining primitive search is total. -/
theorem extendShift?_isSome (theta alpha : AlgebraicNumber) :
    (extendShift? theta alpha).isSome := by
  let upper := degree theta * degree alpha
  let count := Nat.choose upper 2 + 1
  have hcount : count ≠ 0 := by omega
  have hrange : List.range count ≠ [] := by simp [hcount]
  obtain ⟨candidate, hfold⟩ :=
    extendShiftFold_nonempty theta alpha (List.range count) hrange
  unfold extendShift?
  change ((List.range count).foldlM (extendShiftStep theta alpha) none >>=
    fun best => best).isSome
  rw [hfold]
  simp

/-- Retaining the producing shift does not change the selected primitive
element. -/
theorem extendShift?_value (theta alpha : AlgebraicNumber) :
    (extendShift? theta alpha).map ShiftCandidate.value =
      extend? theta alpha := rfl

/-- The bounded maximum-degree primitive-element search is operationally
total. Its field-generation invariant is established separately. -/
theorem extend?_isSome (theta alpha : AlgebraicNumber) :
    (extend? theta alpha).isSome := by
  rw [← extendShift?_value, Option.isSome_map]
  exact extendShift?_isSome theta alpha

private theorem extendShiftFold_source (theta alpha : AlgebraicNumber)
    (indices : List Nat) (best : Option ShiftCandidate)
    (out : ShiftCandidate)
    (hbest : ∀ current, best = some current →
      shift? theta alpha current.shift = some current.value)
    (hfold : indices.foldlM (extendShiftStep theta alpha) best =
      some (some out)) :
    shift? theta alpha out.shift = some out.value := by
  induction indices generalizing best with
  | nil =>
      have heq := Option.some.inj hfold
      exact hbest out heq
  | cons k indices ih =>
      rw [List.foldlM_cons] at hfold
      cases hshift : shift? theta alpha (signedShift k) with
      | none => simp [extendShiftStep, hshift] at hfold
      | some candidate =>
          cases best with
          | none =>
              simp only [extendShiftStep, hshift] at hfold
              apply ih (some ⟨signedShift k, candidate⟩)
              · intro current hcurrent
                have heq := Option.some.inj hcurrent
                subst current
                exact hshift
              · exact hfold
          | some current =>
              by_cases hdegree : degree current.value < degree candidate
              · simp [extendShiftStep, hshift, hdegree] at hfold
                apply ih (some ⟨signedShift k, candidate⟩)
                · intro next hnext
                  have heq := Option.some.inj hnext
                  subst next
                  exact hshift
                · exact hfold
              · simp [extendShiftStep, hshift, hdegree] at hfold
                apply ih (some current)
                · intro next hnext
                  have heq := Option.some.inj hnext
                  subst next
                  exact hbest current rfl
                · exact hfold

/-- The retained shift exactly produces the selected primitive candidate. -/
theorem extendShift?_source (theta alpha : AlgebraicNumber)
    (shifted : ShiftCandidate)
    (h : extendShift? theta alpha = some shifted) :
    shift? theta alpha shifted.shift = some shifted.value := by
  let upper := degree theta * degree alpha
  let count := Nat.choose upper 2 + 1
  unfold extendShift? at h
  change ((List.range count).foldlM
      (extendShiftStep theta alpha) none >>= fun best => best) =
    some shifted at h
  obtain ⟨best, hfold, hbest⟩ := Option.bind_eq_some_iff.mp h
  subst best
  exact extendShiftFold_source theta alpha (List.range count) none
    shifted (by simp) hfold

private theorem list_foldlM_isSome {A B : Type*} {step : B → A → Option B}
    (items : List A) (init : B)
    (hstep : ∀ state item, item ∈ items → (step state item).isSome) :
    (items.foldlM step init).isSome := by
  induction items generalizing init with
  | nil => simp
  | cons item items ih =>
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (hstep init item (by simp))
      rw [List.foldlM_cons, hnext]
      exact ih next fun state tail htail =>
        hstep state tail (by simp [htail])

/-- The primitive-element fold is total for any coefficient array containing
a semantically nonzero entry. -/
theorem primitive?_isSome (coefficients : Array AlgebraicNumber)
    (hnonzero : ∃ a ∈ coefficients.toList, a.isZero = false) :
    (primitive? coefficients).isSome := by
  let nonzero := coefficients.filter fun a => !a.isZero
  obtain ⟨a, ha, hzero⟩ := hnonzero
  have haArray : a ∈ coefficients := Array.mem_toList_iff.mp ha
  have haFiltered : a ∈ nonzero := by
    simp [nonzero, haArray, hzero]
  have hpos : 0 < nonzero.size :=
    Array.size_pos_iff_exists_mem.mpr ⟨a, haFiltered⟩
  let first := nonzero[0]
  have hfirst : nonzero[0]? = some first :=
    Array.getElem?_eq_some_iff.mpr ⟨hpos, rfl⟩
  have hfold := list_foldlM_isSome (nonzero.toList.drop 1) first
    (fun state item _ => extend?_isSome state item)
  unfold primitive?
  change (nonzero[0]? >>= fun first =>
    nonzero.toList.drop 1 |>.foldlM extend? first).isSome
  rw [hfirst]
  exact hfold

private theorem powersFold_isSome (gamma : AlgebraicNumber)
    (indices : List Nat) (powers : Array AlgebraicNumber)
    (hnonempty : powers ≠ #[]) :
    ∃ out, indices.foldlM
        (fun powers _ => do
          let previous ← powers.back?
          let next ← mul? previous gamma
          some (powers.push next))
        powers = some out ∧ out ≠ #[] := by
  induction indices generalizing powers with
  | nil => exact ⟨powers, rfl, hnonempty⟩
  | cons index indices ih =>
      cases hback : powers.back? with
      | none =>
          have hempty := Array.back?_eq_none_iff.mp hback
          exact (hnonempty hempty).elim
      | some previous =>
          obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
            (mul?_isSome previous gamma)
          rw [List.foldlM_cons, hback]
          simpa [hnext] using ih (powers.push next) (by simp)

/-- The checked power table construction is total. -/
theorem powers?_isSome (gamma : AlgebraicNumber) (last : Nat) :
    (powers? gamma last).isSome := by
  unfold powers?
  obtain ⟨one, hone⟩ := Option.isSome_iff_exists.mp (rational?_isSome 1)
  rw [hone]
  change ((List.range last).foldlM
    (fun (powers : Array AlgebraicNumber) _ => do
      let previous ← powers.back?
      let next ← mul? previous gamma
      some (powers.push next)) #[one]).isSome
  obtain ⟨out, hout, _⟩ := powersFold_isSome gamma (List.range last) #[one]
    (by simp)
  rw [hout]
  simp

private theorem powersFold_sound (gamma : AlgebraicNumber)
    (indices : List Nat) (powers out : Array AlgebraicNumber) (offset : Nat)
    (hsize : powers.size = offset + 1)
    (hvalues : ∀ i (hi : i < powers.size),
      powers[i].toComplex = gamma.toComplex ^ i)
    (hrun : indices.foldlM
      (fun powers _ => do
        let previous ← powers.back?
        let next ← mul? previous gamma
        some (powers.push next))
      powers = some out) :
    out.size = offset + 1 + indices.length ∧
      ∀ i (hi : i < out.size),
        out[i].toComplex = gamma.toComplex ^ i := by
  induction indices generalizing powers offset with
  | nil =>
      have hout := Option.some.inj hrun
      subst out
      exact ⟨by simp [hsize], hvalues⟩
  | cons index indices ih =>
      rw [List.foldlM_cons] at hrun
      cases hback : powers.back? with
      | none => simp [hback] at hrun
      | some previous =>
          cases hnext : mul? previous gamma with
          | none => simp [hback, hnext] at hrun
          | some next =>
              have htail : indices.foldlM
                  (fun powers _ => do
                    let previous ← powers.back?
                    let next ← mul? previous gamma
                    some (powers.push next))
                  (powers.push next) = some out := by
                simpa [hback, hnext] using hrun
              rw [Array.back?_eq_getElem?,
                Array.getElem?_eq_some_iff] at hback
              obtain ⟨hlast, hprevious⟩ := hback
              have hlastIndex : powers.size - 1 = offset := by omega
              have hpreviousValue :
                  previous.toComplex = gamma.toComplex ^ offset := by
                rw [← hprevious, hvalues (powers.size - 1) hlast,
                  hlastIndex]
              have hnextValue :
                  next.toComplex = gamma.toComplex ^ (offset + 1) := by
                rw [mul?_sound previous gamma hnext, hpreviousValue,
                  pow_succ]
              have hpushSize : (powers.push next).size = (offset + 1) + 1 := by
                simp [hsize]
              have hpushValues : ∀ i (hi : i < (powers.push next).size),
                  (powers.push next)[i].toComplex = gamma.toComplex ^ i := by
                intro i hi
                by_cases hiold : i < powers.size
                · rw [Array.getElem_push_lt hiold]
                  exact hvalues i hiold
                · have hieq : i = powers.size := by
                    simp only [Array.size_push] at hi
                    omega
                  subst i
                  rw [Array.getElem_push_eq, hsize]
                  exact hnextValue
              obtain ⟨houtSize, houtValues⟩ :=
                ih (powers.push next) (offset + 1) hpushSize hpushValues htail
              exact ⟨by simp at houtSize ⊢; omega, houtValues⟩

/-- A successful checked power table contains exactly the requested initial
powers of its generator. -/
theorem powers?_sound (gamma : AlgebraicNumber) (last : Nat)
    {powers : Array AlgebraicNumber} (h : powers? gamma last = some powers) :
    powers.size = last + 1 ∧
      ∀ i (hi : i < powers.size),
        powers[i].toComplex = gamma.toComplex ^ i := by
  unfold powers? at h
  obtain ⟨one, hone, hfold⟩ := Option.bind_eq_some_iff.mp h
  have honeValue : one.toComplex = 1 := by
    simpa using rational?_sound 1 hone
  have hinitial : ∀ i (hi : i < (#[one] : Array AlgebraicNumber).size),
      (#[one] : Array AlgebraicNumber)[i].toComplex = gamma.toComplex ^ i := by
    intro i hi
    have hiZero : i = 0 := by simpa using hi
    subst i
    simpa using honeValue
  obtain ⟨hsize, hvalues⟩ := powersFold_sound gamma (List.range last)
    #[one] powers 0 (by simp) hinitial hfold
  exact ⟨by simpa [Nat.add_comm] using hsize, hvalues⟩

end Hex.AlgebraicPoly.Common
