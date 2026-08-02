/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.AlgebraicPoly
public import Mathlib.Algebra.Polynomial.Div

public section

/-!
# Correctness of algebraic root APIs

This module gives {name}`Hex.RootSet` a semantic interface independent of structural
equality on algebraic roots, then states completeness, multiplicity, and
normal-form contracts for both fixed-field and algebraic-coefficient drivers.
-/

namespace Hex

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

private theorem transported_root {p q : ZPoly} (h : p = q)
    (rep : RefinedIsolation p) :
    (h ▸ rep).root = rep.root := by
  cases h
  rfl

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
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
      (AlgebraicRoot.exact?_isSome a)
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp
      (AlgebraicRoot.exact?_isSome b)
    simp only [ha', hb'] at h
    have hsame : (a' == b') = same := Option.some.inj h
    rw [← hsame, AlgebraicNumber.beq_iff,
      AlgebraicRoot.exact?_sound a ha',
      AlgebraicRoot.exact?_sound b hb']

/-- Lazy-root comparison always succeeds, exactifying only when the enclosing
polynomials differ. -/
theorem sameValue?_isSome (a b : AlgebraicRoot) :
    (sameValue? a b).isSome := by
  rw [sameValue?]
  split
  · simp
  · obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
      (AlgebraicRoot.exact?_isSome a)
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp
      (AlgebraicRoot.exact?_isSome b)
    simp [ha', hb']

variable {p : ZPoly} {x : SimpleRoot p}

/-- Converting a fixed-field coefficient to a lazy root cannot fail. -/
theorem coeffRoot?_isSome [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (coeffRoot? a rep h).isSome := by
  rw [coeffRoot?]
  split
  · simp
  · obtain ⟨exact, hexact⟩ := Option.isSome_iff_exists.mp
      (QAdjoin.toAlgebraicNumber?_isSome a rep h)
    simp [hexact]

/-- Converting a fixed-field coefficient preserves its selected complex
value. -/
theorem coeffRoot?_sound [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) {root : AlgebraicRoot}
    (hrun : coeffRoot? a rep h = some root) :
    root.toComplex = QAdjoin.toComplex a rep h := by
  rw [coeffRoot?] at hrun
  split at hrun
  next hzero =>
    have hroot : AlgebraicNumber.zero.toRoot = root := Option.some.inj hrun
    rw [← hroot, AlgebraicNumber.toRoot_toComplex,
      show AlgebraicNumber.zero = (0 : AlgebraicNumber) by rfl,
      AlgebraicNumber.zero_toComplex]
    have ha : a = 0 := (QAdjoin.isZero_iff a).mp hzero
    subst a
    exact (QAdjoin.map_zero rep h).symm
  next hnonzero =>
    obtain ⟨canonical, hcanonical, hroot⟩ :=
      Option.bind_eq_some_iff.mp hrun
    have hroot' : canonical.toRoot = root := Option.some.inj hroot
    rw [← hroot', AlgebraicNumber.toRoot_toComplex,
      QAdjoin.toAlgebraicNumber?_sound a rep h hcanonical]

private theorem evalRootFold_isSome [ZPoly.CheckedIrreducible p]
    (coefficients : List (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate acc : AlgebraicRoot) :
    (coefficients.foldlM
      (fun (acc : AlgebraicRoot) (coeff : QAdjoin p x) => do
        let product ← acc.mul? candidate
        let coefficient ← coeffRoot? coeff rep h
        product.add? coefficient)
      acc).isSome := by
  induction coefficients generalizing acc with
  | nil => simp
  | cons coefficient coefficients ih =>
      obtain ⟨product, hproduct⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.mul?_isSome acc candidate)
      obtain ⟨coefficientRoot, hcoefficient⟩ := Option.isSome_iff_exists.mp
        (coeffRoot?_isSome coefficient rep h)
      obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp
        (AlgebraicRoot.add?_isSome product coefficientRoot)
      simpa [List.foldlM_cons, hproduct, hcoefficient, hnext] using ih next

private theorem evalRootFold_sound [ZPoly.CheckedIrreducible p]
    (coefficients : List (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate acc : AlgebraicRoot)
    {out : AlgebraicRoot}
    (hrun : coefficients.foldlM
      (fun (acc : AlgebraicRoot) (coeff : QAdjoin p x) => do
        let product ← acc.mul? candidate
        let coefficient ← coeffRoot? coeff rep h
        product.add? coefficient)
      acc = some out) :
    out.toComplex =
      (coefficients.map fun coefficient => QAdjoin.toComplex coefficient rep h).foldl
        (fun value coefficient => value * candidate.toComplex + coefficient)
        acc.toComplex := by
  induction coefficients generalizing acc out with
  | nil =>
      have hout : acc = out := by simpa using hrun
      subst out
      rfl
  | cons coefficient coefficients ih =>
      cases hproduct : acc.mul? candidate with
      | none => simp [List.foldlM_cons, hproduct] at hrun
      | some product =>
          cases hcoefficient : coeffRoot? coefficient rep h with
          | none => simp [List.foldlM_cons, hproduct, hcoefficient] at hrun
          | some coefficientRoot =>
              cases hnext : product.add? coefficientRoot with
              | none =>
                  simp [List.foldlM_cons, hproduct, hcoefficient, hnext] at hrun
              | some next =>
                  have htail : coefficients.foldlM
                      (fun (acc : AlgebraicRoot) (coeff : QAdjoin p x) => do
                        let product ← acc.mul? candidate
                        let coefficient ← coeffRoot? coeff rep h
                        product.add? coefficient)
                      next = some out := by
                    simpa [List.foldlM_cons, hproduct, hcoefficient, hnext]
                      using hrun
                  rw [ih next htail]
                  simp only [List.map_cons, List.foldl_cons]
                  rw [AlgebraicRoot.add?_sound product coefficientRoot hnext,
                    AlgebraicRoot.mul?_sound acc candidate hproduct,
                    coeffRoot?_sound coefficient rep h hcoefficient]

private theorem reverse_foldl_horner (coefficients : List ℂ) (z : ℂ) :
    coefficients.reverse.foldl
        (fun value coefficient => value * z + coefficient) 0 =
      coefficients.foldr
        (fun coefficient value => value * z + coefficient) 0 := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      rw [List.reverse_cons, List.foldl_append, ih]
      rfl

/-- Exact lazy Horner evaluation always succeeds. -/
theorem evalRoot?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) :
    (evalRoot? f rep h candidate).isSome := by
  exact evalRootFold_isSome f.toArray.reverse.toList rep h candidate
    AlgebraicNumber.zero.toRoot

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

private theorem mergeRootAux_isSome (candidate : RootCount) (index fuel : Nat)
    (roots : Array RootCount) :
    (mergeRootAux candidate index fuel roots).isSome := by
  induction fuel generalizing index roots with
  | zero => simp [mergeRootAux]
  | succ fuel ih =>
      rw [mergeRootAux]
      split
      · rename_i hi
        obtain ⟨same, hsame⟩ := Option.isSome_iff_exists.mp
          (sameValue?_isSome roots[index].root candidate.root)
        cases same <;> simp [hsame, ih]
      · simp

/-- Merging a root through a complete semantic scan cannot fail. -/
theorem mergeRoot_isSome (roots : Array RootCount) (candidate : RootCount) :
    (mergeRoot roots candidate).isSome := by
  exact mergeRootAux_isSome candidate 0 (roots.size + 1) roots

end QAdjoin.Roots

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

open scoped QAdjoinField

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

private theorem toPolynomialAt_eq_map [ZPoly.CheckedIrreducible p]
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

namespace Roots

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

/-- Exact lazy Horner evaluation denotes polynomial evaluation at the selected
fixed-field embedding and absolute candidate. -/
theorem evalRoot?_sound [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot)
    {out : AlgebraicRoot} (hrun : evalRoot? f rep h candidate = some out) :
    out.toComplex =
      Polynomial.eval candidate.toComplex (QAdjoin.toPolynomialAt f rep h) := by
  have hfold := evalRootFold_sound f.toArray.reverse.toList rep h candidate
    AlgebraicNumber.zero.toRoot hrun
  have harray : f.toArray.toList.reverse.toArray = f.toArray.reverse := by
    rw [← List.reverse_toArray, Array.toArray_toList]
  have hreverse : f.toArray.reverse.toList = f.toArray.toList.reverse := by
    symm
    exact congrArg Array.toList harray
  have hzero : AlgebraicNumber.zero.toRoot.toComplex = 0 := by
    rw [AlgebraicNumber.toRoot_toComplex,
      show AlgebraicNumber.zero = (0 : AlgebraicNumber) by rfl,
      AlgebraicNumber.zero_toComplex]
  have hpoly :
      f.toArray.toList.foldr
          (fun coefficient value =>
            Polynomial.C (QAdjoin.toComplex coefficient rep h) +
              Polynomial.X * value)
          0 = QAdjoin.toPolynomialAt f rep h := by
    rw [QAdjoin.toPolynomialAt, ← Array.foldr_toList]
  calc
    out.toComplex =
        (f.toArray.reverse.toList.map fun coefficient =>
          QAdjoin.toComplex coefficient rep h).foldl
          (fun value coefficient => value * candidate.toComplex + coefficient)
          AlgebraicNumber.zero.toRoot.toComplex := hfold
    _ = (f.toArray.toList.map fun coefficient =>
          QAdjoin.toComplex coefficient rep h).foldr
          (fun coefficient value => value * candidate.toComplex + coefficient) 0 := by
      rw [hreverse, List.map_reverse, hzero, reverse_foldl_horner]
    _ = Polynomial.eval candidate.toComplex
        (QAdjoin.toPolynomialAt f rep h) := by
      rw [← hpoly]
      exact (eval_hornerAt f.toArray.toList rep h candidate.toComplex).symm

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

end Roots

/-- The fixed-field root driver always produces a checked root set. -/
theorem roots?_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (QAdjoin.roots? f rep h).isSome := by
  sorry

/-- The fixed-field driver returns `.all` exactly for the zero polynomial. -/
theorem roots_all_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    QAdjoin.roots f rep h = RootSet.all ↔
      QAdjoin.toPolynomialAt f rep h = 0 := by
  sorry

/-- Semantic membership in the fixed-field output is exactly polynomial
vanishing. -/
theorem contains_roots_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    RootSet.Contains (QAdjoin.roots f rep h) z ↔
      Polynomial.eval z (QAdjoin.toPolynomialAt f rep h) = 0 := by
  sorry

/-- Fixed-field root multiplicities agree with Mathlib multiplicities. -/
theorem multiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    (QAdjoin.roots f rep h).multiplicityOf z =
      Polynomial.rootMultiplicity z (QAdjoin.toPolynomialAt f rep h) := by
  sorry

/-- The fixed-field driver produces positive multiplicities. -/
theorem roots_positive [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Positive (QAdjoin.roots f rep h) := by
  cases hroots : QAdjoin.roots f rep h with
  | all => trivial
  | finite roots =>
      intro entry _hentry
      exact entry.multiplicity_pos

/-- The fixed-field driver merges all semantic duplicates. -/
theorem roots_noDuplicates [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.NoDuplicates (QAdjoin.roots f rep h) := by
  sorry

/-- The fixed-field driver uses its deterministic canonical root order. -/
theorem roots_ordered [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Ordered (QAdjoin.roots f rep h) := by
  sorry

/-- For a nonzero fixed-field polynomial, the output multiplicities sum to
its degree. -/
theorem totalMultiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x)
    (hf : QAdjoin.toPolynomialAt f rep h ≠ 0) :
    (QAdjoin.roots f rep h).totalMultiplicity =
      (QAdjoin.toPolynomialAt f rep h).natDegree := by
  sorry

end QAdjoin

namespace AlgebraicPoly

/-- The algebraic-coefficient root driver always produces a checked root set. -/
theorem roots?_isSome (f : AlgebraicPoly) :
    f.roots?.isSome := by
  sorry

/-- The algebraic-coefficient driver returns `.all` exactly for the zero
polynomial. -/
theorem roots_all_iff (f : AlgebraicPoly) :
    f.roots = .all ↔ f.toPolynomial = 0 := by
  sorry

/-- Semantic membership in the algebraic-coefficient output is exactly
polynomial vanishing. -/
theorem contains_roots_iff (f : AlgebraicPoly) (z : ℂ) :
    RootSet.Contains f.roots z ↔
      Polynomial.eval z f.toPolynomial = 0 := by
  sorry

/-- Algebraic-coefficient root multiplicities agree with Mathlib. -/
theorem multiplicity_roots (f : AlgebraicPoly) (z : ℂ) :
    f.roots.multiplicityOf z =
      Polynomial.rootMultiplicity z f.toPolynomial := by
  sorry

/-- The algebraic-coefficient driver produces positive multiplicities. -/
theorem roots_positive (f : AlgebraicPoly) :
    RootSet.Positive f.roots := by
  cases hroots : f.roots with
  | all => trivial
  | finite roots =>
      intro entry _hentry
      exact entry.multiplicity_pos

/-- The algebraic-coefficient driver merges all semantic duplicates. -/
theorem roots_noDuplicates (f : AlgebraicPoly) :
    RootSet.NoDuplicates f.roots := by
  sorry

/-- The algebraic-coefficient driver uses its deterministic canonical order. -/
theorem roots_ordered (f : AlgebraicPoly) :
    RootSet.Ordered f.roots := by
  sorry

/-- For a nonzero algebraic-coefficient polynomial, output multiplicities sum
to its degree. -/
theorem totalMultiplicity_roots (f : AlgebraicPoly)
    (hf : f.toPolynomial ≠ 0) :
    f.roots.totalMultiplicity = f.toPolynomial.natDegree := by
  sorry

end AlgebraicPoly

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
info: 'Hex.QAdjoin.Roots.evalRoot?_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.evalRoot?_sound

/--
info: 'Hex.QAdjoin.Roots.evalBall?_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.Roots.evalBall?_sound

end Hex
