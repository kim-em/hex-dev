/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Presentation
public import HexNumberFieldMathlib.RootDisambiguation
public import HexNumberFieldMathlib.Yun
public import Mathlib.Algebra.Polynomial.Div

public section

/-!
# Correctness of algebraic root APIs

This module gives {name}`Hex.RootSet` a semantic interface independent of structural
equality on algebraic roots, then states completeness, multiplicity, and
normal-form contracts for both fixed-field and algebraic-coefficient drivers.
-/

namespace Hex

/-- Proof-local Mathlib `CommRing` view of `ZPoly`, assembled from the
executable library's verified `Lean.Grind.CommRing` instance. -/
@[implicit_reducible] local instance : CommRing ZPoly :=
  let s := (inferInstance : Lean.Grind.CommRing ZPoly)
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one,
        Lean.Grind.Semiring.natCast_succ] }

/-- Proof-local domain structure on `ZPoly`, transported from
`Polynomial Int`. -/
local instance : IsDomain ZPoly :=
  MulEquiv.isDomain (Polynomial Int)
    (HexPolyMathlib.equiv (R := Int)).toMulEquiv

namespace RootSet

/-- Semantic membership in a root set.  Every complex number belongs to the
root set of the zero polynomial. -/
@[expose] def Contains (roots : RootSet) (z : ℂ) : Prop :=
  match roots with
  | .all => True
  | .finite entries =>
      ∃ entry ∈ entries.toList, entry.root.toComplex = z

/-- The recorded multiplicity of a complex value, or zero when it is absent.
The `.all` case also returns zero, matching Mathlib's convention for
{name}`Polynomial.rootMultiplicity` of the zero polynomial. -/
@[expose]
noncomputable def multiplicityOf (roots : RootSet) (z : ℂ) : Nat := by
  classical
  exact match roots with
  | .all => 0
  | .finite entries =>
      (entries.toList.find? fun entry => entry.root.toComplex = z).map
        (fun entry => entry.multiplicity) |>.getD 0

/-- Sum of the multiplicities in a finite root set. -/
@[expose]
def totalMultiplicity : RootSet → Nat
  | .all => 0
  | .finite entries =>
      entries.foldl (fun total entry => total + entry.multiplicity) 0

/-- Every stored entry has positive multiplicity. -/
@[expose] def Positive : RootSet → Prop
  | .all => True
  | .finite entries => ∀ entry ∈ entries.toList, 0 < entry.multiplicity

/-- A finite root set contains no two entries with the same semantic value. -/
@[expose] def NoDuplicates : RootSet → Prop
  | .all => True
  | .finite entries =>
      entries.toList.Pairwise fun a b =>
        a.root.toComplex ≠ b.root.toComplex

/-- Finite root entries occur in the executable canonical order. -/
@[expose] def Ordered : RootSet → Prop
  | .all => True
  | .finite entries =>
      entries.toList.Pairwise fun a b => QAdjoin.Roots.rootLe a b

end RootSet

namespace QAdjoin.Roots

private theorem list_foldlM_isSome {A B : Type*} {step : B → A → Option B}
    {items : List A} (init : B)
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

private theorem array_foldlM_isSome {A B : Type*} {step : B → A → Option B}
    {items : Array A} (init : B)
    (hstep : ∀ state item, item ∈ items.toList → (step state item).isSome) :
    (items.foldlM step init).isSome := by
  rw [← Array.foldlM_toList]
  exact list_foldlM_isSome init hstep

private theorem transported_root {p q : ZPoly} (h : p = q)
    (rep : RefinedIsolation p) :
    (h ▸ rep).root = rep.root := by
  cases h
  rfl

private theorem gcd_degree_zero_ne (a b : AlgebraicRoot)
    (hdegree : (DensePoly.gcd (ZPoly.toRatPoly a.p)
      (ZPoly.toRatPoly b.p)).degree?.getD 0 = 0) :
    a.toComplex ≠ b.toComplex := by
  intro hab
  let f := HexPolyZMathlib.toPolyℚ a.p
  let g := HexPolyZMathlib.toPolyℚ b.p
  let common := DensePoly.gcd (ZPoly.toRatPoly a.p)
    (ZPoly.toRatPoly b.p)
  let raw := HexPolyMathlib.toPolynomial common
  let normalized := EuclideanDomain.gcd f g
  have haf : a.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
  have hbf : b.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero b.rep
  have hf : f ≠ 0 := HexPolyZMathlib.toPolyℚ_ne_zero haf
  have hg : g ≠ 0 := HexPolyZMathlib.toPolyℚ_ne_zero hbf
  have hnormalized : normalized ≠ 0 := by
    intro hzero
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hassociated : Associated raw normalized := by
    simpa [raw, normalized, common, f, g,
      HexPolyZMathlib.toPolynomial_toRatPoly] using
      (HexPolyMathlib.toPolynomial_gcd_associated
        (ZPoly.toRatPoly a.p) (ZPoly.toRatPoly b.p))
  have hraw : raw ≠ 0 := fun hzero =>
    hnormalized (hassociated.eq_zero_iff.mp hzero)
  have hcomp :
      (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
  have haRoot : f.eval₂ (algebraMap Rat ℂ) a.toComplex = 0 := by
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [f, HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ,
      Polynomial.map_map, hcomp] using AlgebraicRoot.toComplex_isRoot a
  have hbRoot : g.eval₂ (algebraMap Rat ℂ) a.toComplex = 0 := by
    rw [hab]
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [g, HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ,
      Polynomial.map_map, hcomp] using AlgebraicRoot.toComplex_isRoot b
  have hnormalizedRoot :
      normalized.eval₂ (algebraMap Rat ℂ) a.toComplex = 0 := by
    exact Polynomial.eval₂_gcd_eq_zero haRoot hbRoot
  have hrawRoot : raw.eval₂ (algebraMap Rat ℂ) a.toComplex = 0 := by
    obtain ⟨c, hc⟩ := hassociated.symm.dvd
    rw [hc, Polynomial.eval₂_mul, hnormalizedRoot, zero_mul]
  have hpositive : 0 < raw.natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hraw (algebraMap Rat ℂ)
      hrawRoot fun x hx =>
        (FaithfulSMul.algebraMap_injective Rat ℂ)
          (by simpa using hx)
  have hzero : raw.natDegree = 0 := by
    simpa [raw, common, HexPolyMathlib.natDegree_toPolynomial] using hdegree
  omega

/-- A successful lazy-root comparison decides equality of represented complex
values. -/
theorem sameValue?_sound (a b : AlgebraicRoot) {same : Bool}
    (h : sameValue? a b = some same) :
    same ↔ a.toComplex = b.toComplex := by
  rw [sameValue?] at h
  split at h
  next hp =>
    have hsame : (hp ▸ a.rep).sameRoot b.rep = same := by
      simpa using Option.some.inj h
    rw [← hsame,
      HexRootsMathlib.RefinedIsolation.sameRoot_eq_true_iff,
      HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq]
    change (hp ▸ a.rep).root = b.rep.root ↔
      a.rep.root = b.rep.root
    rw [transported_root hp a.rep]
  next hp =>
    dsimp only at h
    split at h
    next hdegree =>
      have hsame : false = same := Option.some.inj h
      rw [← hsame]
      simp [gcd_degree_zero_ne a b hdegree]
    next hdegree =>
      obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.exact?_isSome a)
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.exact?_isSome b)
      simp only [ha', hb'] at h
      have hsame : (a' == b') = same := Option.some.inj h
      rw [← hsame, AlgebraicNumber.beq_iff,
        AlgebraicRoot.exact?_sound a ha',
        AlgebraicRoot.exact?_sound b hb']

/-- Lazy-root comparison always succeeds, exactifying only when distinct
enclosing polynomials have a nonconstant gcd. -/
theorem sameValue?_isSome (a b : AlgebraicRoot) :
    (sameValue? a b).isSome := by
  rw [sameValue?]
  split
  · simp
  · dsimp only
    split
    · simp
    · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.exact?_isSome a)
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.exact?_isSome b)
      simp [ha', hb']

variable {p : ZPoly} {x : SimpleRoot p}

/-- Certified ball Horner evaluation always reaches its requested precision. -/
theorem evalBall?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) (prec : Nat) :
    (evalBall? f rep h candidate prec).isSome := by
  obtain ⟨candidate', hrefine⟩ := Option.isSome_iff_exists.mp
    (RefinedIsolation.refineTo?_isSome candidate.rep ((prec : Int) + 1))
  rw [evalBall?, hrefine]
  simp only
  cases f.toArray.back? <;> simp

/-- Once the norm eliminant passes its normalization checks, component root
isolation, refinement, exact evaluation, and bounded disambiguation are total. -/
theorem componentRoots?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x)
    (hprim : ZPoly.content
      (ZPoly.squareFreeCore (normEliminant f)) = 1)
    (hpos : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).leadingCoeff)
    (hdegree : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).degree?.getD 0)
    (hsimple : HasOnlySimpleRoots
      (ZPoly.squareFreeCore (normEliminant f))) :
    (componentRoots? f multiplicity hMultiplicity rep h).isSome := by
  let eliminant := ZPoly.squareFreeCore (normEliminant f)
  change ZPoly.content eliminant = 1 at hprim
  change 0 < eliminant.leadingCoeff at hpos
  change 0 < eliminant.degree?.getD 0 at hdegree
  change HasOnlySimpleRoots eliminant at hsimple
  have heliminant : eliminant ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  unfold componentRoots?
  dsimp only
  rw [dite_eq_left hprim, dite_eq_left hpos, dite_eq_left hdegree, dite_eq_left hsimple]
  have hisolateSome := HexRootsMathlib.isolate_isSome eliminant hsimple
    heliminant (separationDepth eliminant : Int) .nkThenPellet
  cases hisolate : isolate eliminant hsimple
      (separationDepth eliminant : Int) with
  | none => simp [hisolate] at hisolateSome
  | some isolations =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hmapSome := HexRootsMathlib.array_mapM_isSome
        (xs := isolations) (f := DyadicRootIsolation.toRefined?)
        (fun iso hiso => by
          unfold DyadicRootIsolation.toRefined?
          rw [dite_eq_left (HexRootsMathlib.isolate_refined eliminant hsimple
            (separationDepth eliminant : Int) .nkThenPellet
            hisolate iso hiso)]
          rfl)
      cases hmap : isolations.mapM DyadicRootIsolation.toRefined? with
      | none => simp [hmap] at hmapSome
      | some refined =>
          simp only [Option.bind_some]
          apply array_foldlM_isSome #[]
          intro out candidateRep _hcandidateRep
          let candidate : AlgebraicRoot :=
            { p := eliminant
              prim := hprim
              pos_lc := hpos
              pos_degree := hdegree
              squarefree := hsimple
              x := SimpleRoot.mk candidateRep
              rep := candidateRep
              rep_mk := rfl }
          obtain ⟨keep, hkeep⟩ := Option.isSome_iff_exists.mp
            (retainZero?_isSome (evalEliminant f eliminant) f rep h candidate)
          change (do
            let keep ← retainZero? (evalEliminant f eliminant)
              (evalMajorant f candidate.p) (evalBall? f rep h candidate)
            if keep then
              some (out.push
                { root := candidate
                  multiplicity
                  multiplicity_pos := hMultiplicity })
            else
              some out).isSome
          rw [hkeep]
          cases keep <;> simp

/-- A nonzero norm eliminant with positive-degree square-free core supplies all
normalization witnesses required by the component driver. -/
theorem componentRoots?_total [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (hnorm : normEliminant f ≠ 0)
    (hdegree : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).degree?.getD 0) :
    (componentRoots? f multiplicity hMultiplicity rep h).isSome := by
  have hprim : ZPoly.content
      (ZPoly.squareFreeCore (normEliminant f)) = 1 := by
    simpa only [ZPoly.Primitive] using
      ZPoly.squareFreeCore_primitive (normEliminant f) hnorm
  have hpos : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).leadingCoeff :=
    ZPoly.leadingCoeff_squareFreeCore_pos (normEliminant f) hnorm
  have hsimple : HasOnlySimpleRoots
      (ZPoly.squareFreeCore (normEliminant f)) := by
    simpa only [HasOnlySimpleRoots] using
      ZPoly.squareFreeRat_squareFreeCore (normEliminant f) hnorm
  exact componentRoots?_isSome f multiplicity hMultiplicity rep h
    hprim hpos hdegree hsimple

private theorem mergeRootList_isSome (candidate : RootCount)
    (roots : List RootCount) :
    (mergeRootList candidate roots).isSome := by
  induction roots with
  | nil => simp [mergeRootList]
  | cons current roots ih =>
      obtain ⟨same, hsame⟩ := Option.isSome_iff_exists.mp
        (sameValue?_isSome current.root candidate.root)
      cases same with
      | true => simp [mergeRootList, hsame]
      | false =>
          obtain ⟨tail, htail⟩ := Option.isSome_iff_exists.mp ih
          simp [mergeRootList, hsame, htail]

/-- Merging a root through a complete semantic scan cannot fail. -/
theorem mergeRoot_isSome (roots : Array RootCount) (candidate : RootCount) :
    (mergeRoot roots candidate).isSome := by
  obtain ⟨merged, hmerged⟩ := Option.isSome_iff_exists.mp
    (mergeRootList_isSome candidate roots.toList)
  simp [mergeRoot, hmerged]

/-- Folding semantic root merging over a finite candidate array cannot fail. -/
theorem mergeRoots_isSome (roots candidates : Array RootCount) :
    (candidates.foldlM mergeRoot roots).isSome := by
  exact array_foldlM_isSome roots fun state candidate _ =>
    mergeRoot_isSome state candidate

private theorem yunAux_positive [ZPoly.CheckedIrreducible p]
    (w repeated : DensePoly (QAdjoin p x)) (multiplicity fuel : Nat)
    (out : Array (DensePoly (QAdjoin p x) × Nat))
    (hMultiplicity : 0 < multiplicity)
    (hOut : ∀ component ∈ out.toList,
      0 < component.1.degree?.getD 0 ∧ 0 < component.2) :
    ∀ component ∈ (yunAux w repeated multiplicity fuel out).toList,
      0 < component.1.degree?.getD 0 ∧ 0 < component.2 := by
  induction fuel generalizing w repeated multiplicity out with
  | zero => simpa [yunAux] using hOut
  | succ fuel ih =>
      rw [yunAux]
      split
      · exact hOut
      · dsimp only
        split
        · apply ih
          · omega
          · intro component hcomponent
            rw [Array.toList_push, List.mem_append,
              List.mem_singleton] at hcomponent
            rcases hcomponent with hcomponent | rfl
            · exact hOut component hcomponent
            · exact ⟨by assumption, hMultiplicity⟩
        · apply ih
          · omega
          · exact hOut

/-- Every component emitted by the executable Yun loop has positive degree
and positive multiplicity. -/
theorem yun_positive [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (component)
    (hcomponent : component ∈ (yun f).toList) :
    0 < component.1.degree?.getD 0 ∧ 0 < component.2 := by
  unfold yun at hcomponent
  split at hcomponent
  · simp at hcomponent
  · exact yunAux_positive _ _ 1 (f.size + 1) #[] Nat.one_pos
      (by simp) component hcomponent

end QAdjoin.Roots

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

open scoped QAdjoinField

namespace Roots

private theorem lcmFold_preserves (coefficients : List Rat) {d acc : Nat}
    (hacc : d ∣ acc) :
    d ∣ coefficients.foldl (fun den q => Nat.lcm den q.den) acc := by
  induction coefficients generalizing acc with
  | nil => exact hacc
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.dvd_trans hacc
        (Nat.dvd_lcm_left acc coefficient.den))

private theorem lcmFold_dvd (coefficients : List Rat) {q : Rat} {acc : Nat}
    (hq : q ∈ coefficients) :
    q.den ∣ coefficients.foldl (fun den q => Nat.lcm den q.den) acc := by
  induction coefficients generalizing acc with
  | nil => cases hq
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons, List.mem_cons] at hq ⊢
      rcases hq with rfl | hq
      · exact lcmFold_preserves coefficients
          (Nat.dvd_lcm_right acc q.den)
      · exact ih hq

private theorem lcmFold_pos (coefficients : List Rat) {acc : Nat}
    (hacc : 0 < acc) :
    0 < coefficients.foldl (fun den q => Nat.lcm den q.den) acc := by
  induction coefficients generalizing acc with
  | nil => exact hacc
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.lcm_pos hacc coefficient.den_pos)

private theorem nestedLcmFold_preserves
    (coefficients : List (QAdjoin p x)) {d acc : Nat}
    (hacc : d ∣ acc) :
    d ∣ coefficients.foldl
      (fun den a => a.coeffs.toList.foldl
        (fun den q => Nat.lcm den q.den) den) acc := by
  induction coefficients generalizing acc with
  | nil => exact hacc
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      exact ih (lcmFold_preserves coefficient.coeffs.toList hacc)

private theorem nestedLcmFold_dvd
    (coefficients : List (QAdjoin p x)) {a : QAdjoin p x} {q : Rat}
    {acc : Nat} (ha : a ∈ coefficients) (hq : q ∈ a.coeffs.toList) :
    q.den ∣ coefficients.foldl
      (fun den a => a.coeffs.toList.foldl
        (fun den q => Nat.lcm den q.den) den) acc := by
  induction coefficients generalizing acc with
  | nil => cases ha
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons, List.mem_cons] at ha ⊢
      rcases ha with rfl | ha
      · exact nestedLcmFold_preserves coefficients
          (lcmFold_dvd a.coeffs.toList hq)
      · exact ih ha

private theorem nestedLcmFold_pos
    (coefficients : List (QAdjoin p x)) {acc : Nat}
    (hacc : 0 < acc) :
    0 < coefficients.foldl
      (fun den a => a.coeffs.toList.foldl
        (fun den q => Nat.lcm den q.den) den) acc := by
  induction coefficients generalizing acc with
  | nil => exact hacc
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      exact ih (lcmFold_pos coefficient.coeffs.toList hacc)

/-- Every stored rational coordinate denominator divides the executable common
denominator, including zero-extended coefficient reads. -/
theorem coeffDen_dvd (f : DensePoly (QAdjoin p x)) (i j : Nat) :
    ((f.coeff i).coeffs.coeff j).den ∣ commonDen f := by
  by_cases hi : i < f.size
  · have ha : f.coeff i ∈ f.toList := by
      rw [DensePoly.toList_eq_coeff_range]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    by_cases hj : j < (f.coeff i).coeffs.size
    · have hq : (f.coeff i).coeffs.coeff j ∈ (f.coeff i).coeffs.toList := by
        rw [DensePoly.toList_eq_coeff_range]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      unfold commonDen
      rw [← Array.foldl_toList]
      simp only [← Array.foldl_toList]
      exact nestedLcmFold_dvd f.toList ha hq
    · rw [DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_of_not_gt hj)]
      change 1 ∣ commonDen f
      exact one_dvd _
  · rw [DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)]
    change 1 ∣ commonDen f
    exact one_dvd _

/-- The executable common denominator is positive. -/
theorem commonDen_pos (f : DensePoly (QAdjoin p x)) :
    0 < commonDen f := by
  unfold commonDen
  rw [← Array.foldl_toList]
  simp only [← Array.foldl_toList]
  change 0 < f.toList.foldl
    (fun den a => a.coeffs.toList.foldl
      (fun den q => Nat.lcm den q.den) den) 1
  exact nestedLcmFold_pos f.toList Nat.one_pos

/-- Clearing a rational coordinate against a divisible denominator has the
expected value after embedding into `ℂ`. -/
theorem clearRat_cast (den : Nat) (q : Rat) (hden : q.den ∣ den) :
    (clearRat den q : ℂ) = (den : ℂ) * (q : ℂ) := by
  have hrat : ((clearRat den q : Int) : Rat) = (den : Rat) * q := by
    rcases hden with ⟨k, rfl⟩
    unfold clearRat
    rw [Nat.mul_div_right _ q.den_pos]
    have hden_ne : ((q.den : Nat) : Rat) ≠ 0 := by
      simp [q.den_nz]
    have hq : ((q.num : Rat) / (q.den : Rat)) = q := by
      simpa [Rat.divInt_eq_div, Rat.intCast_natCast] using q.num_divInt_den
    calc
      ((q.num * Int.ofNat k : Int) : Rat) =
          (q.num : Rat) * (k : Rat) := by
        rw [Rat.intCast_mul, Int.ofNat_eq_natCast, Rat.intCast_natCast]
      _ = ((q.num : Rat) * (k : Rat) * (q.den : Rat)) /
          (q.den : Rat) := by
        exact (Rat.mul_div_cancel hden_ne).symm
      _ = ((q.den * k : Nat) : Rat) *
          ((q.num : Rat) / (q.den : Rat)) := by
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
      _ = ((q.den * k : Nat) : Rat) * q := by rw [hq]
  exact_mod_cast hrat

/-- The rectangular coefficient array used for the bivariate lift stores the
cleared coordinate at the corresponding outer and polynomial indices. -/
theorem coeff_clearedOuter (f : DensePoly (QAdjoin p x))
    {i j : Nat} (hi : i < f.size) (hj : j < p.degree?.getD 0) :
    ((clearedOuter f).coeff j).coeff i =
      clearRat (commonDen f) ((f.coeff i).coeffs.coeff j) := by
  unfold clearedOuter
  simp [DensePoly.coeff_ofCoeffs, hi, hj]

private theorem coeff_clearedOuter_eq (f : DensePoly (QAdjoin p x))
    {j : Nat} (hj : j < p.degree?.getD 0) :
    (clearedOuter f).coeff j = DensePoly.ofCoeffs
      ((List.range f.size).map fun i =>
        clearRat (commonDen f) ((f.coeff i).coeffs.coeff j)).toArray := by
  unfold clearedOuter
  simp [DensePoly.coeff_ofCoeffs, hj]

private theorem natDegree_toPolynomial_lt {R : Type*}
    [Semiring R] [DecidableEq R] (q : DensePoly R) {bound : Nat}
    (hbound : q.size ≤ bound) (hpos : 0 < bound) :
    (HexPolyMathlib.toPolynomial q).natDegree < bound := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases hzero : q.size = 0
  · rw [(DensePoly.degree?_eq_none_iff q).2 hzero]
    simp only [Option.getD_none]
    exact hpos
  · rw [DensePoly.degree?_eq_some_of_pos_size q (Nat.pos_of_ne_zero hzero),
      Option.getD_some]
    omega

end Roots

/-- Interpret a fixed-field dense polynomial at the selected embedding. -/
@[expose]
noncomputable def toPolynomialAt (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) : Polynomial ℂ :=
  f.toArray.foldr
    (fun a value => Polynomial.C (toComplex a rep h) +
      Polynomial.X * value) 0

private theorem coeff_hornerAt (coeffs : List (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (n : Nat) :
    (coeffs.foldr
        (fun (a : QAdjoin p x) (value : Polynomial ℂ) =>
          Polynomial.C (toComplex a rep h) + Polynomial.X * value) 0).coeff n =
      toComplex (coeffs.getD n 0) rep h := by
  induction coeffs generalizing n with
  | nil => simp [QAdjoin.map_zero]
  | cons a coeffs ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih n

private theorem array_toList_getDAt (coeffs : Array (QAdjoin p x)) (n : Nat) :
    coeffs.toList.getD n 0 = coeffs.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_toList]

/-- Semantic coefficients agree with fixed-coordinate evaluation. -/
theorem coeff_toPolynomialAt (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (n : Nat) :
    (QAdjoin.toPolynomialAt f rep h).coeff n =
      toComplex (f.coeff n) rep h := by
  rw [toPolynomialAt, ← Array.foldr_toList,
    coeff_hornerAt, array_toList_getDAt]
  rfl

/-- Fixed-field Horner interpretation is polynomial coefficient mapping by
the selected complex embedding. -/
theorem toPolynomialAt_eq_map [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.toPolynomialAt f rep h =
      (HexPolyMathlib.toPolynomial f).map (QAdjoin.embedding rep h) := by
  ext n
  rw [coeff_toPolynomialAt, Polynomial.coeff_map,
    HexPolyMathlib.coeff_toPolynomial]
  rfl

/-- Fixed-field executable zero detection agrees with semantic polynomial
zero. -/
theorem poly_isZero_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) :
    f.isZero ↔ QAdjoin.toPolynomialAt f rep h = 0 := by
  constructor
  · intro hf
    have hsize : f.size = 0 := (DensePoly.isZero_eq_true_iff f).mp hf
    have hfzero : f = 0 := by
      apply DensePoly.ext_coeff
      intro n
      exact DensePoly.coeff_eq_zero_of_size_le f (by omega)
    rw [toPolynomialAt_eq_map, hfzero,
      HexPolyMathlib.toPolynomial_zero, Polynomial.map_zero]
  · intro hpoly
    have hfzero : f = 0 := by
      apply DensePoly.ext_coeff
      intro n
      apply QAdjoin.toComplex_injective rep h
      change toComplex (f.coeff n) rep h =
        toComplex ((0 : DensePoly (QAdjoin p x)).coeff n) rep h
      rw [DensePoly.coeff_zero, QAdjoin.map_zero,
        ← coeff_toPolynomialAt, hpoly]
      simp
    subst f
    exact (DensePoly.isZero_eq_true_iff
      (0 : DensePoly (QAdjoin p x))).mpr DensePoly.size_zero

/-- A nonzero fixed-field polynomial has the expected semantic degree. -/
theorem natDegree_toPolynomialAt [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x)
    (_hf : !f.isZero) :
    (QAdjoin.toPolynomialAt f rep h).natDegree = f.degree?.getD 0 := by
  rw [toPolynomialAt_eq_map,
    Polynomial.natDegree_map_eq_of_injective
      (QAdjoin.embedding_injective rep h),
    HexPolyMathlib.natDegree_toPolynomial]

private theorem definingPolynomial_isRoot [ZPoly.CheckedIrreducible p]
    {y : ℂ} (hy : (HexRootsMathlib.toPolyℂ p).eval y = 0) :
    (definingPolynomial p).eval₂ (algebraMap Rat ℂ) y = 0 := by
  have hp : (HexPolyZMathlib.toPolyℚ p).eval₂
      (algebraMap Rat ℂ) y = 0 := by
    rw [Polynomial.eval₂_eq_eval_map]
    have hcomp :
        (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
          Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [show (HexPolyZMathlib.toPolyℚ p).map (algebraMap Rat ℂ) =
        HexRootsMathlib.toPolyℂ p by
      dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
      rw [Polynomial.map_map, hcomp]]
    exact hy
  rw [definingPolynomial, Polynomial.eval₂_smul, hp, mul_zero]

private noncomputable def conjugateEmbedding [ZPoly.CheckedIrreducible p]
    (y : ℂ) (hy : (HexRootsMathlib.toPolyℂ p).eval y = 0) :
    QAdjoin p x →+* ℂ :=
  (AdjoinRoot.lift (algebraMap Rat ℂ) y
    (definingPolynomial_isRoot hy)).comp toAdjoinRootHom

private theorem conjugateEmbedding_apply [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (y : ℂ)
    (hy : (HexRootsMathlib.toPolyℂ p).eval y = 0) :
    conjugateEmbedding y hy a =
      (HexPolyMathlib.toPolynomial a.coeffs).eval₂
        (algebraMap Rat ℂ) y := by
  unfold conjugateEmbedding
  change AdjoinRoot.lift (algebraMap Rat ℂ) y
      (definingPolynomial_isRoot hy) (toAdjoinRoot a) = _
  unfold toAdjoinRoot
  rw [AdjoinRoot.lift_mk]

private theorem conjugateEmbedding_injective [ZPoly.CheckedIrreducible p]
    (y : ℂ) (hy : (HexRootsMathlib.toPolyℂ p).eval y = 0) :
    Function.Injective (conjugateEmbedding (x := x) y hy) := by
  let : Fact (_root_.Irreducible (definingPolynomial p)) :=
    ⟨definingPolynomial_irreducible p⟩
  exact (AdjoinRoot.lift (algebraMap Rat ℂ) y
    (definingPolynomial_isRoot hy)).injective.comp
      toAdjoinRoot_bijective.1

namespace Roots

private theorem clearedOuter_evalAt [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (y t : ℂ)
    (hy : (HexRootsMathlib.toPolyℂ p).eval y = 0)
    (hf : 0 < f.size) :
    ((HexPolyMathlib.toPolynomial (clearedOuter f)).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y =
      (commonDen f : ℂ) *
        Polynomial.eval t ((HexPolyMathlib.toPolynomial f).map
          (conjugateEmbedding y hy)) := by
  let d := p.degree?.getD 0
  let den := commonDen f
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  have hd : 0 < d := ZPoly.CheckedIrreducible.pos_degree
  have houterSize : (clearedOuter f).size ≤ d := by
    unfold clearedOuter
    exact (DensePoly.size_ofCoeffs_le _).trans (by simp [d])
  have houterDeg :
      (HexPolyMathlib.toPolynomial (clearedOuter f)).natDegree < d :=
    natDegree_toPolynomial_lt _ houterSize hd
  have hinnerDeg (j : Nat) (hj : j < d) :
      (HexPolyMathlib.toPolynomial ((clearedOuter f).coeff j)).natDegree <
        f.size := by
    rw [coeff_clearedOuter_eq f hj]
    apply natDegree_toPolynomial_lt
    · exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    · exact hf
  have hpolyDeg :
      ((HexPolyMathlib.toPolynomial f).map
        (conjugateEmbedding y hy)).natDegree < f.size := by
    rw [Polynomial.natDegree_map_eq_of_injective
        (conjugateEmbedding_injective y hy),
      HexPolyMathlib.natDegree_toPolynomial,
      DensePoly.degree?_eq_some_of_pos_size f hf, Option.getD_some]
    omega
  have hcoordSize (i : Nat) : (f.coeff i).coeffs.size ≤ d := by
    by_cases hzero : (f.coeff i).coeffs.size = 0
    · simp [hzero]
    · have hdegree := (f.coeff i).degree_lt
      rw [DensePoly.degree?_eq_some_of_pos_size _
        (Nat.pos_of_ne_zero hzero), Option.getD_some] at hdegree
      omega
  have hcoordDeg (i : Nat) :
      (HexPolyMathlib.toPolynomial (f.coeff i).coeffs).natDegree < d :=
    natDegree_toPolynomial_lt _ (hcoordSize i) hd
  have hcoefficient (j : Nat) (hj : j < d) :
      ε ((clearedOuter f).coeff j) =
        ∑ i ∈ Finset.range f.size,
          (den : ℂ) * ((f.coeff i).coeffs.coeff j : ℂ) * t ^ i := by
    change (HexPolyMathlib.toPolynomial ((clearedOuter f).coeff j)).eval₂
        (Int.castRingHom ℂ) t = _
    rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℂ)
      (hinnerDeg j hj) t]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < f.size := Finset.mem_range.mp hi
    rw [HexPolyMathlib.coeff_toPolynomial,
      coeff_clearedOuter f hi' hj]
    change (clearRat (commonDen f) ((f.coeff i).coeffs.coeff j) : ℂ) *
        t ^ i = (den : ℂ) * ((f.coeff i).coeffs.coeff j : ℂ) * t ^ i
    rw [clearRat_cast (commonDen f) _ (coeffDen_dvd f i j)]
  have hcoordinate (i : Nat) :
      conjugateEmbedding y hy (f.coeff i) =
        ∑ j ∈ Finset.range d,
          ((f.coeff i).coeffs.coeff j : ℂ) * y ^ j := by
    rw [conjugateEmbedding_apply]
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap Rat ℂ)
      (hcoordDeg i) y]
    apply Finset.sum_congr rfl
    intro j hj
    rw [HexPolyMathlib.coeff_toPolynomial]
    rfl
  rw [Polynomial.eval_map]
  change (HexPolyMathlib.toPolynomial (clearedOuter f)).eval₂ ε y = _
  rw [Polynomial.eval₂_eq_sum_range' ε houterDeg y,
    Polynomial.eval_eq_sum_range' hpolyDeg t]
  have hleft :
      (∑ j ∈ Finset.range d,
        ε ((HexPolyMathlib.toPolynomial (clearedOuter f)).coeff j) *
          y ^ j) =
        ∑ j ∈ Finset.range d,
          (∑ i ∈ Finset.range f.size,
            (den : ℂ) * ((f.coeff i).coeffs.coeff j : ℂ) * t ^ i) *
              y ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [HexPolyMathlib.coeff_toPolynomial,
      hcoefficient j (Finset.mem_range.mp hj)]
  have hright :
      (∑ i ∈ Finset.range f.size,
        (((HexPolyMathlib.toPolynomial f).map
          (conjugateEmbedding y hy)).coeff i) * t ^ i) =
        ∑ i ∈ Finset.range f.size,
          (∑ j ∈ Finset.range d,
            ((f.coeff i).coeffs.coeff j : ℂ) * y ^ j) * t ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial, hcoordinate]
  rw [hleft, hright]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The integer bivariate lift specializes at the selected generator to the
fixed-field polynomial, scaled by its positive common denominator. -/
theorem clearedOuter_eval [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (t : ℂ) (hf : 0 < f.size) :
    ((HexPolyMathlib.toPolynomial (clearedOuter f)).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval rep.root =
      (commonDen f : ℂ) *
        Polynomial.eval t (QAdjoin.toPolynomialAt f rep h) := by
  have hy : (HexRootsMathlib.toPolyℂ p).eval rep.root = 0 :=
    HexRootsMathlib.RefinedIsolation.isRoot rep
  have hemb : conjugateEmbedding (x := x) rep.root hy = embedding rep h := by
    ext a
    rw [conjugateEmbedding_apply, embedding_apply]
    rfl
  rw [clearedOuter_evalAt f rep.root t hy hf, hemb,
    ← toPolynomialAt_eq_map]

/-- Every root at the selected fixed-field embedding is a root of the integer
norm eliminant. -/
theorem normEliminant_isRoot [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (t : ℂ) (hf : !f.isZero)
    (hroot : Polynomial.eval t (QAdjoin.toPolynomialAt f rep h) = 0) :
    (HexRootsMathlib.toPolyℂ (normEliminant f)).eval t = 0 := by
  have hfFalse : f.isZero = false := by
    simpa using hf
  have hfpos : 0 < f.size :=
    (DensePoly.isZero_eq_false_iff f).1 hfFalse
  have hpSize : 1 < p.liftOuter.size := by
    have hpRaw : p ≠ 0 :=
      HexRootsMathlib.RefinedIsolation.poly_ne_zero rep
    have hpPos : 0 < p.size := by
      apply Nat.pos_of_ne_zero
      intro hpZero
      exact hpRaw ((DensePoly.size_eq_zero_iff p).mp hpZero)
    have hpDegree : p.degree?.getD 0 = p.size - 1 := by
      rw [DensePoly.degree?_eq_some_of_pos_size p hpPos, Option.getD_some]
    have hpDegreePos := ZPoly.CheckedIrreducible.pos_degree (p := p)
    have hcoeff : p.liftOuter.coeff (p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun q : ZPoly => q.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size p hpPos hconst
    have hlift : p.size - 1 < p.liftOuter.size := by
      by_contra hnot
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega
  unfold normEliminant
  apply resultant_isRoot p.liftOuter (clearedOuter f) t rep.root
    (Or.inl hpSize)
  · rw [ZPoly.eval_liftOuter]
    exact HexRootsMathlib.RefinedIsolation.isRoot rep
  · rw [clearedOuter_eval f rep h t hfpos, hroot, mul_zero]

/-- The integer norm eliminant of a nonzero fixed-field polynomial is
nonzero. -/
theorem normEliminant_ne_zero [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (hf : !f.isZero) :
    normEliminant f ≠ 0 := by
  let P := HexRootsMathlib.toPolyℂ p
  let Q := HexPolyMathlib.toPolynomial f
  have hfFalse : f.isZero = false := by
    simpa using hf
  have hfpos : 0 < f.size :=
    (DensePoly.isZero_eq_false_iff f).1 hfFalse
  have hfne : f ≠ 0 := by
    intro hzero
    subst f
    simp at hfpos
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hfne
    apply (HexPolyMathlib.equiv (R := QAdjoin p x)).injective
    simpa only [HexPolyMathlib.equiv_apply,
      HexPolyMathlib.toPolynomial_zero] using hzero
  have hpSize : p.size ≠ 0 := by
    intro hzero
    have hdegree := ZPoly.CheckedIrreducible.pos_degree (p := p)
    rw [(DensePoly.degree?_eq_none_iff p).2 hzero] at hdegree
    simp at hdegree
  have hPne : P ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero p hpSize
  let : Fintype (P.rootSet ℂ) :=
    (Polynomial.rootSet_finite P ℂ).fintype
  let H (y : P.rootSet ℂ) : Polynomial ℂ :=
    Q.map (conjugateEmbedding y.1 (by
      apply (Polynomial.mem_rootSet_of_ne hPne).1
      simp [P, y.2]))
  have hHne (y : P.rootSet ℂ) : H y ≠ 0 := by
    unfold H
    apply (Polynomial.map_ne_zero_iff
      (conjugateEmbedding_injective y.1 _)).2
    exact hQne
  let bad : Set ℂ := ⋃ y : P.rootSet ℂ, (H y).rootSet ℂ
  have hbad : bad.Finite := by
    simpa only [bad] using
      Set.finite_iUnion fun y : P.rootSet ℂ =>
        Polynomial.rootSet_finite (H y) ℂ
  obtain ⟨t, ht⟩ := hbad.exists_notMem
  have htH (y : P.rootSet ℂ) : (H y).eval t ≠ 0 := by
    intro hroot
    apply ht
    apply Set.mem_iUnion_of_mem y
    exact (Polynomial.mem_rootSet_of_ne (hHne y)).2 hroot
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  let G := (HexPolyMathlib.toPolynomial (clearedOuter f)).map ε
  have hGnonroot (y : ℂ) (hy : P.eval y = 0) : G.eval y ≠ 0 := by
    have hyMem : y ∈ P.rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne hPne).2 hy
    let yRoot : P.rootSet ℂ := ⟨y, hyMem⟩
    have heval := clearedOuter_evalAt (x := x) f y t
      (by simpa [P] using hy) hfpos
    have hden : (commonDen f : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (commonDen_pos f))
    intro hzero
    have hproduct : (commonDen f : ℂ) * (H yRoot).eval t = 0 := by
      rw [← heval]
      simpa [G, ε, H, Q, yRoot]
    exact (mul_ne_zero hden (htH yRoot)) hproduct
  have hcoprime : IsCoprime P G := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℂ) ℂ P G).2
    intro y
    by_contra hboth
    push Not at hboth
    exact hGnonroot y (by
      simpa [Polynomial.aeval_def] using hboth.1) (by
      simpa [Polynomial.aeval_def] using hboth.2)
  have hresultant : Polynomial.resultant P G ≠ 0 :=
    Polynomial.resultant_ne_zero P G hcoprime
  let m := p.liftOuter.degree?.getD 0
  let n := (clearedOuter f).degree?.getD 0
  have hm : m = P.natDegree := by
    calc
      m = (HexPolyMathlib.toPolynomial p.liftOuter).natDegree := by
        simp [m, HexPolyMathlib.natDegree_toPolynomial]
      _ = p.degree?.getD 0 := ZPoly.natDegree_liftOuter p
      _ = P.natDegree := by
        simp [P]
  have hn : G.natDegree ≤ n := by
    dsimp only [G, n]
    rw [← HexPolyMathlib.natDegree_toPolynomial]
    exact Polynomial.natDegree_map_le
  have hnEq : n = G.natDegree + (n - G.natDegree) := by omega
  have hformal : Polynomial.resultant P G m n ≠ 0 := by
    rw [hm, hnEq, Polynomial.resultant_add_right_deg P G
      P.natDegree G.natDegree (n - G.natDegree) le_rfl,
      Polynomial.coeff_natDegree]
    exact mul_ne_zero
      (_root_.pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hPne)) hresultant
  intro hzero
  have hcorrespondence := congrArg ε
    (DensePoly.toPolynomial_resultant p.liftOuter (clearedOuter f))
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have hleft : ε (DensePoly.resultant p.liftOuter (clearedOuter f)) = 0 := by
    simpa [normEliminant] using congrArg ε hzero
  rw [hleft, ZPoly.map_liftOuterAt, show
      (HexPolyMathlib.toPolynomial (clearedOuter f)).map ε = G by rfl]
      at hcorrespondence
  apply hformal
  simpa [m, n] using hcorrespondence.symm

/-! ## The double-resultant evaluation eliminant

The candidate disambiguation eliminant is one integer polynomial per
component: `Res_y(p(y), Res_z(e(z), S - G(y, z)))` with `G = clearedOuter f`
and `e` the component's candidate eliminant, dilated by the common
denominator. The bounded zero test consumes exactly two facts about it:
nonvanishing, and membership of the true evaluation value among its roots. -/

section EvaluationEliminant

/-- The trivariate lift of a candidate eliminant keeps its coefficient array:
each integer coefficient becomes the doubly constant polynomial. -/
private theorem coeff_candidateLift (e : ZPoly) (n : Nat) :
    (candidateLift e).coeff n =
      DensePoly.C (DensePoly.C (e.coeff n)) := by
  unfold candidateLift
  rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  by_cases hn : n < e.size
  · have hnArray : n < e.toArray.size := by simpa using hn
    rw [Array.getElem?_eq_getElem hnArray]
    simp only [Option.map_some, Option.getD_some]
    congr 2
    rw [Array.getElem_eq_getD (Zero.zero : Int), DensePoly.toArray_getD]
  · have hnArray : e.toArray.size ≤ n := by simpa using Nat.le_of_not_gt hn
    rw [Array.getElem?_eq_none hnArray]
    simp only [Option.map_none, Option.getD_none]
    have hecoeff : e.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le e (Nat.le_of_not_gt hn)
    rw [hecoeff]
    rfl

/-- The trivariate candidate lift stores exactly as many coefficients as its
source. -/
private theorem size_candidateLift (e : ZPoly) :
    (candidateLift e).size = e.size := by
  by_cases hzero : e.size = 0
  · have hle : (candidateLift e).size ≤ e.size := by
      unfold candidateLift
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    omega
  · have hpos : 0 < e.size := Nat.pos_of_ne_zero hzero
    have hle : (candidateLift e).size ≤ e.size := by
      unfold candidateLift
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    have hcoeff : (candidateLift e).coeff (e.size - 1) ≠ 0 := by
      rw [coeff_candidateLift]
      intro hzero'
      have h0 := congrArg
        (fun q : DensePoly ZPoly => (q.coeff 0).coeff 0) hzero'
      simp at h0
      exact DensePoly.coeff_last_ne_zero_of_pos_size e hpos h0
    have hge : e.size ≤ (candidateLift e).size := by
      by_contra hnot
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega

/-- The stored coefficients of the shifted trivariate polynomial. -/
private theorem coeff_evalShifted (f : DensePoly (QAdjoin p x))
    {i : Nat} (hi : i < Nat.max f.size 1) :
    (evalShifted f).coeff i =
      DensePoly.ofCoeffs (((List.range (p.degree?.getD 0)).map fun j =>
        if i = 0 && j = 0 then
          DensePoly.ofCoeffs
            #[-clearRat (commonDen f) ((f.coeff i).coeffs.coeff j), 1]
        else
          DensePoly.C
            (-clearRat (commonDen f) ((f.coeff i).coeffs.coeff j))).toArray) := by
  unfold evalShifted
  simp [DensePoly.coeff_ofCoeffs, hi]

/-- The Mathlib commutative ring induced by the executable operations on
bivariate integer polynomials, proof-local like the `ZPoly` instance above. -/
@[implicit_reducible]
private noncomputable def denseZPolyCommRing : CommRing (DensePoly ZPoly) :=
  let s := (inferInstance : Lean.Grind.CommRing (DensePoly ZPoly))
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ := fun n => Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc := fun n => by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one,
        Lean.Grind.Semiring.natCast_succ] }

attribute [local instance] denseZPolyCommRing

private theorem denseZPolyIsDomain : IsDomain (DensePoly ZPoly) :=
  MulEquiv.isDomain (Polynomial ZPoly)
    (HexPolyMathlib.equiv (R := ZPoly)).toMulEquiv

attribute [local instance] denseZPolyIsDomain

/-- Specialize the evaluation variable to `s` and the generator variable to
`y` in a bivariate integer polynomial. -/
private noncomputable def evalOuter (s y : ℂ) : DensePoly ZPoly →+* ℂ :=
  (Polynomial.eval₂RingHom
    ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom) y).comp
    (HexPolyMathlib.equiv (R := ZPoly)).toRingHom

private theorem evalOuter_apply (s y : ℂ) (q : DensePoly ZPoly) :
    evalOuter s y q =
      ((HexPolyMathlib.toPolynomial q).map
        ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
          (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y := by
  rw [Polynomial.eval_map]
  rfl

/-- A hom-mapped common root kills the image of the executable resultant. -/
private theorem resultant_hom_eq_zero {S : Type} [CommRing S] [IsDomain S]
    [DecidableEq S] [Div S] [Hex.ExactDivLaws S]
    (F G : DensePoly S) (φ : S →+* ℂ) (z : ℂ)
    (hpos : 1 < F.size ∨ 1 < G.size)
    (hF : ((HexPolyMathlib.toPolynomial F).map φ).eval z = 0)
    (hG : ((HexPolyMathlib.toPolynomial G).map φ).eval z = 0) :
    φ (DensePoly.resultant F G) = 0 := by
  let F' : Polynomial ℂ := (HexPolyMathlib.toPolynomial F).map φ
  let G' : Polynomial ℂ := (HexPolyMathlib.toPolynomial G).map φ
  let m := F.degree?.getD 0
  let n := G.degree?.getD 0
  have hm : F'.natDegree ≤ m := by
    calc
      F'.natDegree ≤ (HexPolyMathlib.toPolynomial F).natDegree :=
        Polynomial.natDegree_map_le
      _ = m := by
        simp [m]
  have hn : G'.natDegree ≤ n := by
    calc
      G'.natDegree ≤ (HexPolyMathlib.toPolynomial G).natDegree :=
        Polynomial.natDegree_map_le
      _ = n := by
        simp [n]
  have hmn : 0 < m ∨ 0 < n := by
    rcases hpos with hFpos | hGpos
    · left
      dsimp only [m]
      rw [DensePoly.degree?_eq_some_of_pos_size F (by omega), Option.getD_some]
      omega
    · right
      dsimp only [n]
      rw [DensePoly.degree?_eq_some_of_pos_size G (by omega), Option.getD_some]
      omega
  have hresultant : Polynomial.resultant F' G' m n = 0 := by
    by_cases hboth : F' = 0 ∧ G' = 0
    · rcases hboth with ⟨hFzero, hGzero⟩
      rw [hFzero, hGzero, Polynomial.resultant_zero_zero]
      exact zero_pow (by omega)
    · have hne : F' ≠ 0 ∨ G' ≠ 0 := by
        by_cases hFzero : F' = 0
        · right
          intro hGzero
          exact hboth ⟨hFzero, hGzero⟩
        · exact Or.inl hFzero
      have hdefault : Polynomial.resultant F' G' = 0 :=
        DensePoly.resultant_eq_zero_of_common_eval F' G' z
          (by simpa [F'] using hF) (by simpa [G'] using hG) hne
      have hmEq : m = F'.natDegree + (m - F'.natDegree) := by omega
      have hnEq : n = G'.natDegree + (n - G'.natDegree) := by omega
      rw [hmEq, Polynomial.resultant_add_left_deg F' G' F'.natDegree n
        (m - F'.natDegree) le_rfl]
      rw [hnEq, Polynomial.resultant_add_right_deg F' G' F'.natDegree
        G'.natDegree (n - G'.natDegree) le_rfl]
      rw [hdefault]
      ring
  have hcorrespondence := congrArg φ
    (DensePoly.toPolynomial_resultant F G)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  rw [hcorrespondence]
  exact hresultant

/-- The specialization hom sends doubly constant polynomials to their
integer value. -/
private theorem evalOuter_C_C (s y : ℂ) (c : Int) :
    evalOuter s y (DensePoly.C (DensePoly.C c)) = (c : ℂ) := by
  change Polynomial.eval₂
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom) y
      (HexPolyMathlib.toPolynomial (DensePoly.C (DensePoly.C c))) = (c : ℂ)
  rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
  change Polynomial.eval₂ (Int.castRingHom ℂ) s
      (HexPolyMathlib.toPolynomial (DensePoly.C c)) = (c : ℂ)
  rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
  rfl

/-- The trivariate candidate lift specializes to the complex cast of its
source. -/
private theorem candidateLift_map (e : ZPoly) (s y : ℂ) :
    (HexPolyMathlib.toPolynomial (candidateLift e)).map (evalOuter s y) =
      HexRootsMathlib.toPolyℂ e := by
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    coeff_candidateLift, HexRootsMathlib.coeff_toPolyℂ, evalOuter_C_C]

/-- The shifted trivariate polynomial specializes to the difference between
the evaluation variable and the specialized bivariate lift. -/
private theorem evalShifted_map_eval [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (s y z : ℂ) (hf : 0 < f.size) :
    ((HexPolyMathlib.toPolynomial (evalShifted f)).map (evalOuter s y)).eval z =
      s - ((HexPolyMathlib.toPolynomial (clearedOuter f)).map
        ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) z).comp
          (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y := by
  let d := p.degree?.getD 0
  let den := commonDen f
  have hd : 0 < d := ZPoly.CheckedIrreducible.pos_degree
  have hN : Nat.max f.size 1 = f.size := Nat.max_eq_left hf
  have hshiftSize : (evalShifted f).size ≤ f.size := by
    unfold evalShifted
    refine (DensePoly.size_ofCoeffs_le _).trans ?_
    simp [hN]
  have hshiftDeg :
      (HexPolyMathlib.toPolynomial (evalShifted f)).natDegree < f.size :=
    natDegree_toPolynomial_lt _ hshiftSize hf
  have hcoefficient (i : Nat) (hi : i < f.size) :
      evalOuter s y ((evalShifted f).coeff i) =
        (if i = 0 then s else 0) -
          ∑ j ∈ Finset.range d,
            (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ) * y ^ j := by
    rw [coeff_evalShifted f (i := i) (by rw [hN]; exact hi)]
    set W := DensePoly.ofCoeffs (((List.range d).map fun j =>
      if i = 0 && j = 0 then
        DensePoly.ofCoeffs #[-clearRat den ((f.coeff i).coeffs.coeff j), 1]
      else
        DensePoly.C (-clearRat den ((f.coeff i).coeffs.coeff j))).toArray)
      with hW
    have hWsize : W.size ≤ d := by
      rw [hW]
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    have hWdeg : (HexPolyMathlib.toPolynomial W).natDegree < d :=
      natDegree_toPolynomial_lt _ hWsize hd
    change Polynomial.eval₂
        ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
          (HexPolyMathlib.equiv (R := Int)).toRingHom) y
        (HexPolyMathlib.toPolynomial W) = _
    rw [Polynomial.eval₂_eq_sum_range' _ hWdeg y]
    have hterm (j : Nat) (hj : j < d) :
        ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
          (HexPolyMathlib.equiv (R := Int)).toRingHom)
            ((HexPolyMathlib.toPolynomial W).coeff j) =
          (if i = 0 && j = 0 then s else 0) -
            (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ) := by
      rw [HexPolyMathlib.coeff_toPolynomial, hW, DensePoly.coeff_ofCoeffs,
        Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_map, List.getElem?_range hj]
      simp only [Option.map_some, Option.getD_some]
      by_cases hij : i = 0 && j = 0
      · rw [ite_eq_left hij, ite_eq_left hij]
        change Polynomial.eval₂ (Int.castRingHom ℂ) s
            (HexPolyMathlib.toPolynomial
              (DensePoly.ofCoeffs
                #[-clearRat den ((f.coeff i).coeffs.coeff j), 1])) = _
        have hlin : HexPolyMathlib.toPolynomial
            (DensePoly.ofCoeffs
              #[-clearRat den ((f.coeff i).coeffs.coeff j), (1 : Int)]) =
            Polynomial.C (-clearRat den ((f.coeff i).coeffs.coeff j)) +
              Polynomial.X := by
          ext k
          rw [HexPolyMathlib.coeff_toPolynomial, DensePoly.coeff_ofCoeffs,
            Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X]
          match k with
          | 0 => simp [Array.getD]
          | 1 => simp [Array.getD]
          | k + 2 =>
              rw [ite_eq_right (by omega), ite_eq_right (by omega)]
              rw [Array.getD_eq_getD_getElem?,
                Array.getElem?_eq_none (by simp), Option.getD_none, add_zero]
              rfl
        rw [hlin, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X]
        simp only [Int.coe_castRingHom]
        push_cast
        ring
      · rw [ite_eq_right hij, ite_eq_right hij]
        change Polynomial.eval₂ (Int.castRingHom ℂ) s
            (HexPolyMathlib.toPolynomial
              (DensePoly.C (-clearRat den ((f.coeff i).coeffs.coeff j)))) = _
        rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
        simp only [Int.coe_castRingHom]
        push_cast
        ring
    have hsum : (∑ j ∈ Finset.range d,
        ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) s).comp
          (HexPolyMathlib.equiv (R := Int)).toRingHom)
            ((HexPolyMathlib.toPolynomial W).coeff j) * y ^ j) =
        ∑ j ∈ Finset.range d,
          ((if i = 0 && j = 0 then s else 0) -
            (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ)) * y ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm j (Finset.mem_range.mp hj)]
    rw [hsum]
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [ite_eq_left rfl]
      rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb])
        (fun h0 => absurd (Finset.mem_range.mpr hd) h0)]
      simp
    · rw [ite_eq_right (by omega)]
      apply Finset.sum_eq_zero
      intro j _
      simp [hipos.ne']
  have houterSize : (clearedOuter f).size ≤ d := by
    unfold clearedOuter
    exact (DensePoly.size_ofCoeffs_le _).trans (by simp [d])
  have houterDeg :
      (HexPolyMathlib.toPolynomial (clearedOuter f)).natDegree < d :=
    natDegree_toPolynomial_lt _ houterSize hd
  have hinnerDeg (j : Nat) (hj : j < d) :
      (HexPolyMathlib.toPolynomial ((clearedOuter f).coeff j)).natDegree <
        f.size := by
    rw [coeff_clearedOuter_eq f hj]
    apply natDegree_toPolynomial_lt
    · exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    · exact hf
  have hclearedCoeff (j : Nat) (hj : j < d) :
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) z).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)
          ((HexPolyMathlib.toPolynomial (clearedOuter f)).coeff j) =
        ∑ i ∈ Finset.range f.size,
          (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ) * z ^ i := by
    rw [HexPolyMathlib.coeff_toPolynomial]
    change (HexPolyMathlib.toPolynomial ((clearedOuter f).coeff j)).eval₂
        (Int.castRingHom ℂ) z = _
    rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℂ) (hinnerDeg j hj) z]
    apply Finset.sum_congr rfl
    intro i hi
    rw [HexPolyMathlib.coeff_toPolynomial,
      coeff_clearedOuter f (Finset.mem_range.mp hi) hj]
    rfl
  rw [Polynomial.eval_map, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum_range' (evalOuter s y) hshiftDeg z,
    Polynomial.eval₂_eq_sum_range' _ houterDeg y]
  have hlhs : (∑ i ∈ Finset.range f.size,
      evalOuter s y ((HexPolyMathlib.toPolynomial (evalShifted f)).coeff i) *
        z ^ i) =
      ∑ i ∈ Finset.range f.size,
        ((if i = 0 then s else 0) -
          ∑ j ∈ Finset.range d,
            (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ) * y ^ j) *
          z ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [HexPolyMathlib.coeff_toPolynomial,
      hcoefficient i (Finset.mem_range.mp hi)]
  have hrhs : (∑ j ∈ Finset.range d,
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) z).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)
          ((HexPolyMathlib.toPolynomial (clearedOuter f)).coeff j) * y ^ j) =
      ∑ j ∈ Finset.range d,
        (∑ i ∈ Finset.range f.size,
          (clearRat den ((f.coeff i).coeffs.coeff j) : ℂ) * z ^ i) * y ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hclearedCoeff j (Finset.mem_range.mp hj)]
  rw [hlhs, hrhs]
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hindicator : (∑ i ∈ Finset.range f.size,
      (if i = 0 then s else 0) * z ^ i) = s := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb])
      (fun h0 => absurd (Finset.mem_range.mpr hf) h0)]
    simp
  rw [hindicator]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A checked-irreducible generator polynomial stores at least two
coefficients after the constant bivariate lift. -/
private theorem one_lt_size_liftOuter [ZPoly.CheckedIrreducible p] :
    1 < (ZPoly.liftOuter p).size := by
  have hpDegreePos := ZPoly.CheckedIrreducible.pos_degree (p := p)
  have hpPos : 0 < p.size := by
    by_contra hzero
    rw [(DensePoly.degree?_eq_none_iff p).2 (by omega)] at hpDegreePos
    simp at hpDegreePos
  have hcoeff : p.liftOuter.coeff (p.size - 1) ≠ 0 := by
    rw [ZPoly.coeff_liftOuter]
    intro hzero
    have hconst := congrArg (fun q : ZPoly => q.coeff 0) hzero
    simp at hconst
    exact DensePoly.coeff_last_ne_zero_of_pos_size p hpPos hconst
  have hlift : p.size - 1 < p.liftOuter.size := by
    by_contra hnot
    exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
  have hdeg2 : 1 < p.size := by
    rw [DensePoly.degree?_eq_some_of_pos_size p hpPos,
      Option.getD_some] at hpDegreePos
    omega
  omega

/-- Dilating by a nonzero factor reflects the zero polynomial. -/
private theorem eq_zero_of_dilate_eq_zero {c : Int} {q : ZPoly} (hc : c ≠ 0)
    (hzero : ZPoly.dilate c q = 0) : q = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun r : ZPoly => r.coeff n) hzero
  simp only [ZPoly.coeff_dilate, DensePoly.coeff_zero] at hcoeff
  rcases mul_eq_zero.mp hcoeff with hpow | hval
  · exact absurd hpow (_root_.pow_ne_zero n hc)
  · simpa using hval

/-- Complex roots transform contravariantly under integer dilation. -/
private theorem toPolyℂ_dilate_isRoot {c : Int} {q : ZPoly} {v : ℂ}
    (hroot : (HexRootsMathlib.toPolyℂ q).eval ((c : ℂ) * v) = 0) :
    (HexRootsMathlib.toPolyℂ (ZPoly.dilate c q)).IsRoot v := by
  have hmap : HexRootsMathlib.toPolyℂ (ZPoly.dilate c q) =
      (HexRootsMathlib.toPolyℂ q).comp
        (Polynomial.C (c : ℂ) * Polynomial.X) := by
    ext n
    rw [HexRootsMathlib.coeff_toPolyℂ, ZPoly.coeff_dilate,
      Polynomial.comp_C_mul_X_coeff, HexRootsMathlib.coeff_toPolyℂ]
    push_cast
    ring
  rw [Polynomial.IsRoot, hmap, Polynomial.eval_comp]
  simpa using hroot

/-- The evaluation eliminant vanishes at the evaluation of the fixed-field
polynomial at any root of the candidate eliminant and the selected
embedding. -/
theorem evalEliminant_isRoot [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (e : ZPoly) {z : ℂ}
    (hf : 0 < f.size) (he : 1 < e.size)
    (hz : (HexRootsMathlib.toPolyℂ e).IsRoot z) :
    (HexRootsMathlib.toPolyℂ (evalEliminant f e)).IsRoot
      (Polynomial.eval z (QAdjoin.toPolynomialAt f rep h)) := by
  set v := Polynomial.eval z (QAdjoin.toPolynomialAt f rep h) with hv
  have hinner : evalOuter ((commonDen f : ℂ) * v) rep.root
      (DensePoly.resultant (candidateLift e) (evalShifted f)) = 0 := by
    apply resultant_hom_eq_zero (candidateLift e) (evalShifted f)
      (evalOuter ((commonDen f : ℂ) * v) rep.root) z
      (Or.inl (by rw [size_candidateLift]; omega))
    · rw [candidateLift_map]
      exact hz
    · rw [evalShifted_map_eval f _ rep.root z hf,
        clearedOuter_eval f rep h z hf, ← hv]
      ring
  have houter := resultant_isRoot p.liftOuter
    (DensePoly.resultant (candidateLift e) (evalShifted f))
    ((commonDen f : ℂ) * v) rep.root
    (Or.inl one_lt_size_liftOuter)
    (by rw [ZPoly.eval_liftOuter]
        exact HexRootsMathlib.RefinedIsolation.isRoot rep)
    (by rw [← evalOuter_apply]
        exact hinner)
  show (HexRootsMathlib.toPolyℂ (evalEliminant f e)).eval v = 0
  unfold evalEliminant
  have hcast : ((Int.ofNat (commonDen f) : Int) : ℂ) = (commonDen f : ℂ) := by
    rfl
  apply toPolyℂ_dilate_isRoot
  rw [hcast]
  exact houter

/-- The evaluation eliminant of a nonzero fixed-field polynomial and a
positive-degree candidate eliminant is nonzero. -/
theorem evalEliminant_ne_zero [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (e : ZPoly)
    (hf : !f.isZero) (he : 1 < e.size) :
    evalEliminant f e ≠ 0 := by
  have hfFalse : f.isZero = false := by simpa using hf
  have hfpos : 0 < f.size := (DensePoly.isZero_eq_false_iff f).1 hfFalse
  let P := HexRootsMathlib.toPolyℂ p
  let E := HexRootsMathlib.toPolyℂ e
  have hpSize : p.size ≠ 0 := by
    intro hzero
    have hdeg := ZPoly.CheckedIrreducible.pos_degree (p := p)
    rw [(DensePoly.degree?_eq_none_iff p).2 hzero] at hdeg
    simp at hdeg
  have hPne : P ≠ 0 := HexRootsMathlib.toPolyℂ_ne_zero p hpSize
  have hEne : E ≠ 0 := HexRootsMathlib.toPolyℂ_ne_zero e (by omega)
  -- A specialization value avoiding every bivariate evaluation of the
  -- cleared lift at root pairs.
  let gval : ℂ × ℂ → ℂ := fun yz =>
    ((HexPolyMathlib.toPolynomial (clearedOuter f)).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) yz.2).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval yz.1
  let bad : Set ℂ := gval '' (P.rootSet ℂ ×ˢ E.rootSet ℂ)
  have hbad : bad.Finite :=
    ((Polynomial.rootSet_finite P ℂ).prod
      (Polynomial.rootSet_finite E ℂ)).image _
  obtain ⟨t, ht⟩ := hbad.exists_notMem
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  let inner : DensePoly ZPoly :=
    DensePoly.resultant (candidateLift e) (evalShifted f)
  let Inner : Polynomial ℂ := (HexPolyMathlib.toPolynomial inner).map ε
  -- The specialized inner eliminant does not vanish at any root of `P`.
  have hInner_nonzero (y : ℂ) (hy : P.eval y = 0) : Inner.eval y ≠ 0 := by
    have hyMem : y ∈ P.rootSet ℂ := (Polynomial.mem_rootSet_of_ne hPne).2 hy
    have hval : Inner.eval y = evalOuter t y inner := by
      rw [evalOuter_apply]
    rw [hval]
    have hcorr := congrArg (evalOuter t y)
      (DensePoly.toPolynomial_resultant (candidateLift e) (evalShifted f))
    rw [← Polynomial.resultant_map_map, candidateLift_map] at hcorr
    set W : Polynomial ℂ :=
      (HexPolyMathlib.toPolynomial (evalShifted f)).map (evalOuter t y)
      with hWdef
    have hm' : (candidateLift e).degree?.getD 0 = E.natDegree := by
      have hsize := size_candidateLift e
      rw [show E.natDegree = e.degree?.getD 0 from
        HexRootsMathlib.natDegree_toPolyℂ e,
        DensePoly.degree?_eq_some_of_pos_size _ (by omega),
        DensePoly.degree?_eq_some_of_pos_size _ (by omega),
        Option.getD_some, Option.getD_some, hsize]
    have hn' : W.natDegree ≤ (evalShifted f).degree?.getD 0 := by
      rw [hWdef, ← HexPolyMathlib.natDegree_toPolynomial]
      exact Polynomial.natDegree_map_le
    have hcoprime : IsCoprime E W := by
      apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (k := ℂ) ℂ E W).2
      intro w0
      by_contra hboth
      push Not at hboth
      have hEw : E.eval w0 = 0 := by
        simpa [Polynomial.aeval_def] using hboth.1
      have hWw : W.eval w0 = 0 := by
        simpa [Polynomial.aeval_def] using hboth.2
      apply ht
      have hWval := evalShifted_map_eval f t y w0 hfpos
      rw [hWdef] at hWw
      rw [hWw] at hWval
      refine ⟨(y, w0), ⟨hyMem, (Polynomial.mem_rootSet_of_ne hEne).2 hEw⟩, ?_⟩
      have hzero : t - gval (y, w0) = 0 := by
        simpa [gval] using hWval.symm
      have := sub_eq_zero.mp hzero
      exact this.symm
    have hresultant : Polynomial.resultant E W ≠ 0 :=
      Polynomial.resultant_ne_zero E W hcoprime
    have hformal : Polynomial.resultant E W
        ((candidateLift e).degree?.getD 0)
        ((evalShifted f).degree?.getD 0) ≠ 0 := by
      rw [hm']
      have hnEq : (evalShifted f).degree?.getD 0 =
          W.natDegree + ((evalShifted f).degree?.getD 0 - W.natDegree) := by
        omega
      rw [hnEq, Polynomial.resultant_add_right_deg E W E.natDegree
        W.natDegree ((evalShifted f).degree?.getD 0 - W.natDegree) le_rfl,
        Polynomial.coeff_natDegree]
      exact mul_ne_zero
        (_root_.pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hEne))
        hresultant
    rw [show evalOuter t y inner = Polynomial.resultant E W
        ((candidateLift e).degree?.getD 0)
        ((evalShifted f).degree?.getD 0) from hcorr]
    exact hformal
  -- Coprimality of the outer pair, hence a nonzero specialized value.
  have hcoprimeOuter : IsCoprime P Inner := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℂ) ℂ P Inner).2
    intro y
    by_contra hboth
    push Not at hboth
    exact hInner_nonzero y
      (by simpa [Polynomial.aeval_def] using hboth.1)
      (by simpa [Polynomial.aeval_def] using hboth.2)
  have hresultantOuter : Polynomial.resultant P Inner ≠ 0 :=
    Polynomial.resultant_ne_zero P Inner hcoprimeOuter
  let m := p.liftOuter.degree?.getD 0
  let n := inner.degree?.getD 0
  have hm : m = P.natDegree := by
    calc
      m = (HexPolyMathlib.toPolynomial p.liftOuter).natDegree := by
        simp [m, HexPolyMathlib.natDegree_toPolynomial]
      _ = p.degree?.getD 0 := ZPoly.natDegree_liftOuter p
      _ = P.natDegree := by
        simp [P]
  have hn : Inner.natDegree ≤ n := by
    dsimp only [Inner, n]
    rw [← HexPolyMathlib.natDegree_toPolynomial]
    exact Polynomial.natDegree_map_le
  have hformalOuter : Polynomial.resultant P Inner m n ≠ 0 := by
    rw [hm]
    have hnEq : n = Inner.natDegree + (n - Inner.natDegree) := by omega
    rw [hnEq, Polynomial.resultant_add_right_deg P Inner P.natDegree
      Inner.natDegree (n - Inner.natDegree) le_rfl,
      Polynomial.coeff_natDegree]
    exact mul_ne_zero
      (_root_.pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hPne))
      hresultantOuter
  intro hzero
  have hq0 : DensePoly.resultant p.liftOuter inner = 0 := by
    apply eq_zero_of_dilate_eq_zero (c := Int.ofNat (commonDen f))
    · intro hc
      have h0 : commonDen f = 0 := Int.ofNat.inj hc
      have hden := commonDen_pos f
      omega
    · exact hzero
  have hcorrOuter := congrArg ε
    (DensePoly.toPolynomial_resultant p.liftOuter inner)
  rw [← Polynomial.resultant_map_map, ZPoly.map_liftOuterAt] at hcorrOuter
  rw [hq0, _root_.map_zero] at hcorrOuter
  apply hformalOuter
  simpa [Inner, m, n] using hcorrOuter.symm

end EvaluationEliminant

/-- A positive-degree square-free norm-eliminant core forces the component
itself to be nonzero. -/
theorem size_pos_of_core_degree [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x))
    (hdegree : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).degree?.getD 0) :
    0 < f.size := by
  by_contra hnot
  have hzero : f = 0 := (DensePoly.size_eq_zero_iff f).mp (by omega)
  subst hzero
  have hcleared : clearedOuter (0 : DensePoly (QAdjoin p x)) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    unfold clearedOuter
    rw [DensePoly.coeff_ofCoeffs, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getElem?_map]
    cases hlt : (List.range (p.degree?.getD 0))[n]? with
    | none => rfl
    | some j =>
        simp only [Option.map_some, Option.getD_some, DensePoly.size_zero,
          List.range_zero, List.map_nil]
        rfl
  have hnorm : normEliminant (0 : DensePoly (QAdjoin p x)) = 0 := by
    unfold normEliminant
    rw [hcleared]
    have hlift := one_lt_size_liftOuter (p := p)
    have hliftZero : p.liftOuter.isZero = false :=
      (DensePoly.isZero_eq_false_iff _).2 (by omega)
    unfold DensePoly.resultant
    rw [hliftZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_left (show DensePoly.isZero (0 : DensePoly ZPoly) = true from rfl),
      ite_eq_right (by omega)]
  rw [hnorm] at hdegree
  have hcore : (ZPoly.squareFreeCore 0).degree?.getD 0 = 0 := by decide
  omega

/-- Every positive-degree fixed-field component satisfies the normalization
conditions needed by the component root driver. -/
theorem componentRoots?_total_of_degree [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (hdegree : 0 < f.degree?.getD 0) :
    (componentRoots? f multiplicity hMultiplicity rep h).isSome := by
  have hfpos : 0 < f.size := by
    by_contra hsize
    have hzero : f.size = 0 := by omega
    rw [(DensePoly.degree?_eq_none_iff f).2 hzero] at hdegree
    simp at hdegree
  have hfFalse : f.isZero = false :=
    (DensePoly.isZero_eq_false_iff f).2 hfpos
  have hf : !f.isZero := by simp [hfFalse]
  have hnorm : normEliminant f ≠ 0 := normEliminant_ne_zero f hf
  have hsemanticDegree :
      0 < (QAdjoin.toPolynomialAt f rep h).natDegree := by
    rw [natDegree_toPolynomialAt f rep h hf]
    exact hdegree
  obtain ⟨z, hz⟩ := Complex.exists_root
    (Polynomial.natDegree_pos_iff_degree_pos.mp hsemanticDegree)
  have hnormRoot :
      (HexRootsMathlib.toPolyℂ (normEliminant f)).IsRoot z :=
    normEliminant_isRoot f rep h z hf hz
  have hcoreRoot :
      (HexRootsMathlib.toPolyℂ
        (ZPoly.squareFreeCore (normEliminant f))).IsRoot z :=
    HexPolyZMathlib.isRoot_squareFreeCore hnorm hnormRoot
  have hcoreNe : ZPoly.squareFreeCore (normEliminant f) ≠ 0 :=
    ZPoly.squareFreeCore_ne_zero (normEliminant f) hnorm
  have hcoreSize : (ZPoly.squareFreeCore (normEliminant f)).size ≠ 0 := by
    intro hsize
    exact hcoreNe ((DensePoly.size_eq_zero_iff _).mp hsize)
  have hcoreDegree : 0 <
      (ZPoly.squareFreeCore (normEliminant f)).degree?.getD 0 := by
    by_contra hnot
    exact HexRootsMathlib.not_isRoot_of_degree_not_pos
      (ZPoly.squareFreeCore (normEliminant f)) hcoreSize hnot z hcoreRoot
  exact componentRoots?_total f multiplicity hMultiplicity rep h
    hnorm hcoreDegree

private theorem eval_hornerAt (coefficients : List (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (z : ℂ) :
    Polynomial.eval z
        (coefficients.foldr
          (fun coefficient value =>
            Polynomial.C (QAdjoin.toComplex coefficient rep h) +
              Polynomial.X * value)
          0) =
      (coefficients.map fun coefficient => QAdjoin.toComplex coefficient rep h).foldr
        (fun coefficient value => value * z + coefficient) 0 := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp only [List.foldr_cons, List.map_cons, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      rw [ih]
      ring

private theorem hornerBall_mem [ZPoly.CheckedIrreducible p]
    (coefficients : List (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) (zBall initBall : DyadicComplexBall)
    (prec : Int) (init : ℂ) (hz : z ∈ zBall.set)
    (hinit : init ∈ initBall.set) :
    coefficients.foldr
        (fun coefficient value => value * z + QAdjoin.toComplex coefficient rep h)
        init ∈
      (coefficients.foldr
        (fun coefficient value =>
          (coefficient.approx rep h prec).2.add (zBall.mul value))
        initBall).set := by
  induction coefficients with
  | nil => exact hinit
  | cons coefficient coefficients ih =>
      simpa only [List.foldr_cons, add_comm, mul_comm] using
        DyadicComplexBall.add_mem (QAdjoin.approx_sound coefficient rep h prec)
          (DyadicComplexBall.mul_mem hz ih)

private theorem foldr_map_horner (coefficients : List (QAdjoin p x))
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x) (z init : ℂ) :
    (coefficients.map fun coefficient => QAdjoin.toComplex coefficient rep h).foldr
        (fun coefficient value => value * z + coefficient) init =
      coefficients.foldr
        (fun coefficient value =>
          value * z + QAdjoin.toComplex coefficient rep h) init := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]

/-- Certified ball Horner evaluation encloses exact evaluation at the selected
embedding and candidate root. -/
theorem evalBall?_sound [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) (prec : Nat)
    {ball : DyadicComplexBall} (hrun : evalBall? f rep h candidate prec = some ball) :
    Polynomial.eval candidate.toComplex (QAdjoin.toPolynomialAt f rep h) ∈
      ball.set := by
  rw [evalBall?] at hrun
  obtain ⟨candidate', hrefine, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  have hroot : candidate'.1.root = candidate.toComplex := by
    calc
      candidate'.1.root = candidate.rep.root :=
        HexRootsMathlib.RefinedIsolation.refineTo_root candidate.rep
          ((prec : Int) + 1) .nkThenPellet hrefine
      _ = candidate.toComplex := by
        unfold AlgebraicRoot.toComplex
        rfl
  have hz : candidate.toComplex ∈ candidate'.1.1.square.toBall.set := by
    rw [← hroot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc candidate'.1)
  cases hback : f.toArray.back? with
  | none =>
      have hball : DyadicComplexBall.zero = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      have hempty : f.toArray = #[] := Array.back?_eq_none_iff.mp hback
      rw [QAdjoin.toPolynomialAt, hempty]
      simp [DyadicComplexBall.zero, DyadicComplexBall.set,
        DyadicComplexBall.center, DyadicComplexBall.realRadius]
  | some top =>
      have hball : f.toArray.foldr
          (fun coefficient value =>
            (coefficient.approx rep h (prec : Int)).2.add
              (candidate'.1.1.square.toBall.mul value))
          (top.approx rep h (prec : Int)).2
          (start := f.toArray.size - 1) = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      obtain ⟨pre, hprefix⟩ := Array.back?_eq_some_iff.mp hback
      have hlist : f.toArray.toList = pre.toList ++ [top] := by
        rw [hprefix, Array.toList_push]
      have hsize : f.toArray.size - 1 = pre.size := by
        rw [hprefix]
        simp
      have hfold :
          f.toArray.foldr
              (fun coefficient value =>
                (coefficient.approx rep h (prec : Int)).2.add
                  (candidate'.1.1.square.toBall.mul value))
              (top.approx rep h (prec : Int)).2
              (start := f.toArray.size - 1) =
            pre.toList.foldr
              (fun coefficient value =>
                (coefficient.approx rep h (prec : Int)).2.add
                  (candidate'.1.1.square.toBall.mul value))
              (top.approx rep h (prec : Int)).2 := by
        rw [hsize, Array.foldr_eq_foldr_extract]
        rw [hprefix, Array.extract_push_of_le (le_refl pre.size)]
        simp
      rw [hfold]
      have hvalue :
          Polynomial.eval candidate.toComplex
              (QAdjoin.toPolynomialAt f rep h) =
            pre.toList.foldr
              (fun coefficient value =>
                value * candidate.toComplex + QAdjoin.toComplex coefficient rep h)
              (QAdjoin.toComplex top rep h) := by
        have hpoly :
            f.toArray.toList.foldr
                (fun coefficient value =>
                  Polynomial.C (QAdjoin.toComplex coefficient rep h) +
                    Polynomial.X * value)
                0 = QAdjoin.toPolynomialAt f rep h := by
          rw [QAdjoin.toPolynomialAt, ← Array.foldr_toList]
        rw [← hpoly, eval_hornerAt, hlist, List.map_append,
          List.foldr_append]
        simp only [List.map_singleton, List.foldr_cons, List.foldr_nil]
        rw [zero_mul, zero_add]
        exact foldr_map_horner pre.toList rep h candidate.toComplex
          (QAdjoin.toComplex top rep h)
      rw [hvalue]
      exact hornerBall_mem pre.toList rep h candidate.toComplex
        candidate'.1.1.square.toBall (top.approx rep h (prec : Int)).2
        prec (QAdjoin.toComplex top rep h) hz
        (QAdjoin.approx_sound top rep h prec)

/-- Bounded disambiguation against the shared double-resultant evaluation
eliminant retains precisely the candidates at which the fixed-field
polynomial vanishes. -/
theorem retainZero?_correct [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot)
    (hf : 0 < f.size) {keep : Bool}
    (hkeep : retainZero? (evalEliminant f candidate.p)
      (evalMajorant f candidate.p) (evalBall? f rep h candidate) = some keep) :
    keep ↔ Polynomial.eval candidate.toComplex
      (QAdjoin.toPolynomialAt f rep h) = 0 := by
  have hene : candidate.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero candidate.rep
  have hepos : 0 < candidate.p.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hene ((DensePoly.size_eq_zero_iff candidate.p).mp hzero)
  have hesize : 1 < candidate.p.size := by
    have hdeg := candidate.pos_degree
    rw [DensePoly.degree?_eq_some_of_pos_size _ hepos,
      Option.getD_some] at hdeg
    omega
  have hfBool : !f.isZero := by
    simp [(DensePoly.isZero_eq_false_iff f).mpr hf]
  exact Hex.retainZero?_sound
    (evalEliminant_ne_zero f candidate.p hfBool hesize)
    (evalEliminant_isRoot f rep h candidate.p hf hesize
      (AlgebraicRoot.toComplex_isRoot candidate))
    (fun prec ball hball => evalBall?_sound f rep h candidate prec hball)
    hkeep

end Roots

/-- The fixed-field root driver always produces a checked root set. -/
theorem roots?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (QAdjoin.roots? f rep h).isSome := by
  rw [QAdjoin.roots?]
  split
  · simp
  split
  · simp
  · have hfold : ((Roots.yun f).foldlM
        (fun out component =>
          if hm : 0 < component.2 then do
            let found ← Roots.componentRoots? component.1 component.2 hm rep h
            found.foldlM Roots.mergeRoot out
          else
            none)
        #[]).isSome := by
      apply Roots.array_foldlM_isSome #[]
      intro out component hcomponent
      obtain ⟨hdegree, hMultiplicity⟩ :=
        Roots.yun_positive f component hcomponent
      rw [dite_eq_left hMultiplicity]
      obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
        (Roots.componentRoots?_total_of_degree component.1 component.2
          hMultiplicity rep h hdegree)
      rw [hfound]
      exact Roots.mergeRoots_isSome out found
    obtain ⟨roots, hroots⟩ := Option.isSome_iff_exists.mp hfold
    apply Option.isSome_iff_exists.mpr
    refine ⟨.finite (roots.mergeSort Roots.rootLe), ?_⟩
    rw [show (Roots.yun f).foldlM
        (fun out component =>
          if hm : 0 < component.2 then do
            let found ← Roots.componentRoots? component.1 component.2 hm rep h
            found.foldlM Roots.mergeRoot out
          else
            none)
        #[] = some roots by
      convert hroots]
    rfl

/-- The total fixed-field root API is exactly the output of its now-proved
total checked driver. -/
theorem roots?_eq_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.roots? f rep h = some (QAdjoin.roots f rep h) := by
  unfold QAdjoin.roots
  cases hrun : QAdjoin.roots? f rep h with
  | none =>
      have hsome := roots?_isSome f rep h
      simp [hrun] at hsome
  | some roots => simp

private theorem roots?_all_iff_isZero [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.roots? f rep h = some .all ↔ f.isZero := by
  rw [QAdjoin.roots?]
  split
  · simp_all
  split
  · simp_all
  · rename_i hzero hdegree
    simp only [hzero, Option.bind_eq_bind]
    cases hfold : (Roots.yun f).foldlM
        (fun out component =>
          if hm : 0 < component.2 then do
            let found ← Roots.componentRoots? component.1 component.2 hm rep h
            found.foldlM Roots.mergeRoot out
          else
            none)
        #[] <;> simp

/-- The fixed-field driver returns `.all` exactly for the zero polynomial. -/
theorem roots_all_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.roots f rep h = RootSet.all ↔
      QAdjoin.toPolynomialAt f rep h = 0 := by
  rw [← QAdjoin.poly_isZero_iff f rep h,
    ← roots?_all_iff_isZero f rep h, roots?_eq_roots]
  simp

end QAdjoin

/-! The completed root-semantics foundations must not inherit unfinished proofs. -/

/--
info: 'Hex.QAdjoin.Roots.sameValue?_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.sameValue?_sound

/--
info: 'Hex.QAdjoin.Roots.sameValue?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.sameValue?_isSome

/--
info: 'Hex.QAdjoin.Roots.retainZero?_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.retainZero?_correct

/--
info: 'Hex.QAdjoin.Roots.evalBall?_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.evalBall?_sound

end Hex
