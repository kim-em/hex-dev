/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Approx
import HexMatrixMathlib.Vector
import Mathlib.FieldTheory.Minpoly.Finite

public section

/-!
# Canonicalization and exactification

The checked conversions in `hex-number-field` select canonical irreducible
representatives.  This module states both certificate soundness and the
completeness obligations that make their total wrappers semantically exact.
-/

namespace Hex

namespace AlgebraicNumber

/-- Forgetting minimality preserves the selected complex value. -/
theorem toRoot_toComplex (a : AlgebraicNumber) :
    a.toRoot.toComplex = a.toComplex := by
  rfl

/-- Canonicalization of an already normalized polynomial is total. -/
theorem ofNormalized?_isSome
    (p : ZPoly) (prim : ZPoly.Primitive p) (pos_lc : 0 < p.leadingCoeff)
    (pos_degree : 0 < p.degree?.getD 0)
    (checked : ZPoly.CheckedIrreducible p) (squarefree : HasOnlySimpleRoots p)
    (rep : RefinedIsolation p) :
    (AlgebraicNumber.ofNormalized? p prim pos_lc pos_degree checked
      squarefree rep).isSome := by
  rw [AlgebraicNumber.ofNormalized?_isSome_eq]
  split
  · simp
  · have hpne : p ≠ 0 := by
      intro hp
      rw [hp] at pos_degree
      simp at pos_degree
    have hisolate := HexRootsMathlib.isolate_isSome p squarefree hpne
      (separationDepth p : Int) .nkThenPellet
    cases hrun : isolate p squarefree (separationDepth p : Int) with
    | none => simp [hrun] at hisolate
    | some isolations =>
        have hmapSome := HexRootsMathlib.array_mapM_isSome
          (xs := isolations) (f := DyadicRootIsolation.toRefined?)
          (fun iso hiso => by
            unfold DyadicRootIsolation.toRefined?
            rw [dite_eq_left (HexRootsMathlib.isolate_refined p squarefree
              (separationDepth p : Int) .nkThenPellet hrun iso hiso)]
            rfl)
        cases hmap : isolations.mapM DyadicRootIsolation.toRefined? with
        | none => simp [hmap] at hmapSome
        | some refined =>
            obtain ⟨iso, hiso, hisoRoot⟩ :=
              HexRootsMathlib.isolate_root_mem_of_pos p squarefree
                (separationDepth p : Int) .nkThenPellet pos_degree hrun
                (HexRootsMathlib.RefinedIsolation.isRoot rep)
            obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
            have hi : i < isolations.size := by simpa using hiList
            obtain ⟨hsize, hget⟩ :=
              HexRootsMathlib.array_mapM_some_get hmap
            have hj : i < refined.size := by simpa [← hsize] using hi
            have hto := hget i hi hj
            have hraw : refined[i].1 = isolations[i] := by
              rw [DyadicRootIsolation.toRefined?] at hto
              split at hto
              · exact (congrArg Subtype.val (Option.some.inj hto)).symm
              · simp at hto
            have harrIso : isolations[i] = iso := by
              rw [← hidx]
              exact (Array.getElem_toList hi).symm
            have hroot :
                HexRootsMathlib.RefinedIsolation.root refined[i] = rep.root := by
              change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 =
                HexRootsMathlib.RefinedIsolation.root rep
              rw [hraw, harrIso]
              exact hisoRoot
            have hsame : refined[i].sameRoot rep = true :=
              HexRootsMathlib.RefinedIsolation.sameRoot_eq_true_iff
                refined[i] rep |>.mpr <|
                (HexRootsMathlib.RefinedIsolation.intersects_iff_root_eq
                  refined[i] rep).mpr hroot
            have hfindSome :
                (refined.toList.find? fun r => r.sameRoot rep).isSome = true := by
              rw [List.find?_isSome]
              exact ⟨refined[i], by simp, hsame⟩
            unfold AlgebraicNumber.canonicalRep?
            split
            · simp_all
            · split
              · simp_all
              · split
                · simp_all
                · rfl

end AlgebraicNumber

namespace AlgebraicRoot

/-- Trying a factor is semantically sound whenever every root of that factor
is a root of the enclosing polynomial. -/
theorem exactFactor?_sound (a : AlgebraicRoot) (q : ZPoly)
    (hq : ∀ z : ℂ, (HexRootsMathlib.toPolyℂ q).IsRoot z →
      (HexRootsMathlib.toPolyℂ a.p).IsRoot z)
    {b : AlgebraicNumber} (h : a.exactFactor? q = some b) :
    b.toComplex = a.toComplex := by
  unfold AlgebraicRoot.exactFactor? at h
  split at h
  · rename_i hprim
    split at h
    · rename_i hpos
      split at h
      · rename_i hdegree
        split at h
        · rename_i hirred
          split at h
          · rename_i hsimple
            obtain ⟨isolations, _hisolate, h⟩ :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨refined, _hrefined, h⟩ :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨comparable, _hcomparable, h⟩ :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨matching, hmatching, hnormalized⟩ :=
              Option.bind_eq_some_iff.mp h
            have hmatch := List.find?_some
              (p := fun r : RefinedIsolation q =>
                decide ((mahlerPrec a.p : Int) ≤ r.1.square.prec) &&
                  r.1.square.discsMeet a.rep.1.square)
              hmatching
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
            have hmatchingRoot :
                (HexRootsMathlib.toPolyℂ a.p).IsRoot matching.root :=
              hq matching.root
                (HexRootsMathlib.RefinedIsolation.isRoot matching)
            have hroot : matching.root = a.rep.root :=
              HexRootsMathlib.DyadicSquare.root_eq_of_discsMeet
                (HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep)
                hmatch.1 a.rep.property hmatchingRoot
                (HexRootsMathlib.RefinedIsolation.isRoot a.rep)
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc matching)
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep)
                hmatch.2
            have hout := AlgebraicNumber.ofNormalized?_toComplex
              q hprim hpos hdegree ⟨hirred, hdegree⟩ hsimple matching
              hnormalized
            change b.toComplex = a.rep.root
            exact hout.trans hroot
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A normalized irreducible factor containing the selected root always
survives isolation, refinement, and canonicalization. -/
theorem exactFactor?_isSome (a : AlgebraicRoot) (q : ZPoly)
    (hprim : ZPoly.content q = 1) (hpos : 0 < q.leadingCoeff)
    (hdegree : 0 < q.degree?.getD 0)
    (hirred : ZPoly.isIrreducible q = true)
    (hsimple : HasOnlySimpleRoots q)
    (hroot : (HexRootsMathlib.toPolyℂ q).IsRoot a.toComplex) :
    (a.exactFactor? q).isSome := by
  unfold AlgebraicRoot.exactFactor?
  rw [dite_eq_left hprim, dite_eq_left hpos, dite_eq_left hdegree, dite_eq_left hirred,
    dite_eq_left hsimple]
  have hqne : q ≠ 0 := by
    intro hq
    rw [hq] at hdegree
    simp at hdegree
  have hisolate := HexRootsMathlib.isolate_isSome q hsimple hqne
    (separationDepth q : Int) .nkThenPellet
  cases hrun : isolate q hsimple (separationDepth q : Int) with
  | none => simp [hrun] at hisolate
  | some isolations =>
      have hmapSome := HexRootsMathlib.array_mapM_isSome
        (xs := isolations) (f := DyadicRootIsolation.toRefined?)
        (fun iso hiso => by
          unfold DyadicRootIsolation.toRefined?
          rw [dite_eq_left (HexRootsMathlib.isolate_refined q hsimple
            (separationDepth q : Int) .nkThenPellet hrun iso hiso)]
          rfl)
      cases hmap : isolations.mapM DyadicRootIsolation.toRefined? with
      | none => simp [hmap] at hmapSome
      | some refined =>
          have hrefineSome := HexRootsMathlib.array_mapM_isSome
            (xs := refined)
            (f := fun r : RefinedIsolation q =>
              (r.refineTo? (mahlerPrec a.p : Int)).unattach)
            (fun r _hr => by
              have hsome :=
                HexRootsMathlib.RefinedIsolation.refineTo?_isSome_mixed
                  r (mahlerPrec a.p : Int)
              cases hrun' : r.refineTo? (mahlerPrec a.p : Int)
                  .nkThenPellet with
              | none => simp [hrun'] at hsome
              | some out => simp)
          cases hrefine : refined.mapM (fun r : RefinedIsolation q =>
              (r.refineTo? (mahlerPrec a.p : Int)).unattach) with
          | none => simp [hrefine] at hrefineSome
          | some comparable =>
              obtain ⟨iso, hiso, hisoRoot⟩ :=
                HexRootsMathlib.isolate_root_mem_of_pos q hsimple
                  (separationDepth q : Int) .nkThenPellet hdegree hrun hroot
              obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
              have hi : i < isolations.size := by simpa using hiList
              obtain ⟨hmapSize, hmapGet⟩ :=
                HexRootsMathlib.array_mapM_some_get hmap
              have hj : i < refined.size := by
                simpa [← hmapSize] using hi
              have hto := hmapGet i hi hj
              have hraw : refined[i].1 = isolations[i] := by
                rw [DyadicRootIsolation.toRefined?] at hto
                split at hto
                · exact (congrArg Subtype.val (Option.some.inj hto)).symm
                · simp at hto
              have harrIso : isolations[i] = iso := by
                rw [← hidx]
                exact (Array.getElem_toList hi).symm
              have hrefinedRoot :
                  HexRootsMathlib.RefinedIsolation.root refined[i] =
                    a.rep.root := by
                change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 =
                  HexRootsMathlib.RefinedIsolation.root a.rep
                rw [hraw, harrIso]
                exact hisoRoot
              obtain ⟨hrefineSize, hrefineGet⟩ :=
                HexRootsMathlib.array_mapM_some_get hrefine
              have hk : i < comparable.size := by
                simpa [← hrefineSize] using hj
              have hget := hrefineGet i hj hk
              cases hrun' : refined[i].refineTo? (mahlerPrec a.p : Int)
                  .nkThenPellet with
              | none => simp [hrun'] at hget
              | some out =>
                  simp only [hrun', Option.unattach_some] at hget
                  have hout : out.1 = comparable[i] := Option.some.inj hget
                  have hprec := Hex.RefinedIsolation.refineTo?_precision
                    refined[i] (mahlerPrec a.p : Int)
                      (strategy := .nkThenPellet) hrun'
                  rw [hout] at hprec
                  have hcomparableRoot :
                      HexRootsMathlib.RefinedIsolation.root comparable[i] =
                        a.rep.root := by
                    rw [← hout]
                    exact
                      (HexRootsMathlib.RefinedIsolation.refineTo_root
                        refined[i] (mahlerPrec a.p : Int) .nkThenPellet
                          hrun').trans hrefinedRoot
                  have hmeet : comparable[i].1.square.discsMeet
                      a.rep.1.square = true := by
                    by_contra hnot
                    have hfalse := Bool.eq_false_of_not_eq_true hnot
                    have hdisj :=
                      HexRootsMathlib.DyadicSquare.closedDisc_disjoint_of_discsMeet_eq_false
                        comparable[i].1.square a.rep.1.square hfalse
                    have hmem : HexRootsMathlib.RefinedIsolation.root comparable[i] ∈
                        HexRootsMathlib.DyadicSquare.closedDisc a.rep.1.square := by
                      rw [hcomparableRoot]
                      exact HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep
                    exact (Set.disjoint_left.mp hdisj)
                      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc
                        comparable[i]) hmem
                  have hmatching :
                      (comparable.find? fun r =>
                        decide ((mahlerPrec a.p : Int) ≤ r.1.square.prec) &&
                          r.1.square.discsMeet a.rep.1.square).isSome := by
                    simp
                    exact ⟨comparable[i], by
                      simp, hprec, hmeet⟩
                  cases hfind : comparable.find? fun r =>
                      decide ((mahlerPrec a.p : Int) ≤ r.1.square.prec) &&
                        r.1.square.discsMeet a.rep.1.square with
                  | none => simp [hfind] at hmatching
                  | some matching =>
                      have hnormalized := AlgebraicNumber.ofNormalized?_isSome
                        q hprim hpos hdegree ⟨hirred, hdegree⟩ hsimple matching
                      simpa [hmap, hrefine, hfind] using hnormalized

private theorem exactFold_some (a : AlgebraicRoot)
    (entries : List (ZPoly × Nat)) (b : AlgebraicNumber) :
    entries.foldl
        (fun found entry =>
          match found with
          | some b => some b
          | none => a.exactFactor? entry.1)
        (some b) = some b := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rw [List.foldl_cons]
      exact ih

private theorem exactFold_witness (a : AlgebraicRoot)
    (entries : List (ZPoly × Nat)) {b : AlgebraicNumber}
    (h : entries.foldl
        (fun found entry =>
          match found with
          | some b => some b
          | none => a.exactFactor? entry.1)
        none = some b) :
    ∃ entry ∈ entries, a.exactFactor? entry.1 = some b := by
  induction entries with
  | nil => simp at h
  | cons entry entries ih =>
      rw [List.foldl_cons] at h
      cases hfactor : a.exactFactor? entry.1 with
      | none =>
          simp only [hfactor] at h
          obtain ⟨witness, hmem, hwitness⟩ := ih h
          exact ⟨witness, List.mem_cons_of_mem entry hmem, hwitness⟩
      | some c =>
          simp only [hfactor, exactFold_some] at h
          cases h
          exact ⟨entry, List.mem_cons_self, hfactor⟩

private theorem exactFold_isSome_of_mem (a : AlgebraicRoot)
    (entries : List (ZPoly × Nat)) {entry : ZPoly × Nat}
    (hentry : entry ∈ entries) (hfactor : (a.exactFactor? entry.1).isSome) :
    (entries.foldl
      (fun found entry =>
        match found with
        | some b => some b
        | none => a.exactFactor? entry.1)
      none).isSome := by
  cases hrun : a.exactFactor? entry.1 with
  | none => simp [hrun] at hfactor
  | some b =>
      induction entries with
      | nil => simp at hentry
      | cons head tail ih =>
          rw [List.foldl_cons]
          by_cases heq : head = entry
          · subst head
            rw [hrun, exactFold_some]
            simp
          · have htail : entry ∈ tail :=
              (List.mem_cons.mp hentry).resolve_left (Ne.symm heq)
            cases hhead : a.exactFactor? head.1 with
            | none => simpa [hhead] using ih htail
            | some c =>
                change (tail.foldl
                  (fun found entry =>
                    match found with
                    | some b => some b
                    | none => a.exactFactor? entry.1)
                  (some c)).isSome
                rw [exactFold_some]
                simp

/-- Every successful exactification denotes the original selected root. -/
theorem exact?_sound (a : AlgebraicRoot) {b : AlgebraicNumber}
    (h : a.exact? = some b) :
    b.toComplex = a.toComplex := by
  rw [AlgebraicRoot.exact?] at h
  rw [← Array.foldl_toList] at h
  obtain ⟨entry, hentry, hfactor⟩ := exactFold_witness a _ h
  have hdvdℤ := HexBerlekampZassenhausMathlib.factorize_entry_dvd a.p
    (Array.mem_toList_iff.mp hentry)
  have hdvdℂ : HexRootsMathlib.toPolyℂ entry.1 ∣
      HexRootsMathlib.toPolyℂ a.p := by
    obtain ⟨r, hr⟩ := hdvdℤ
    refine ⟨r.map (Int.castRingHom ℂ), ?_⟩
    have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) hr
    simpa [HexRootsMathlib.toPolyℂ, Polynomial.map_mul] using hm
  exact exactFactor?_sound a entry.1
    (fun z hz => hz.dvd hdvdℂ) hfactor

/-- Factor selection and isolation always find the canonical representative. -/
theorem exact?_isSome (a : AlgebraicRoot) :
    a.exact?.isSome := by
  have hpne : a.p ≠ 0 := by
    intro hp
    have hdegree := a.pos_degree
    rw [hp] at hdegree
    simp at hdegree
  obtain ⟨entry, hentry, hentryRoot⟩ :=
    HexBerlekampZassenhausMathlib.factorize_exists_root a.p hpne
      (by simpa [HexRootsMathlib.toPolyℂ] using
        AlgebraicRoot.toComplex_isRoot a)
  have hprim :=
    HexBerlekampZassenhausMathlib.factorize_entries_primitive_of_chosen_raw_primitive
      a.p hpne entry hentry
  have hpos :=
    HexBerlekampZassenhausMathlib.factorize_entries_leadingCoeff_pos
      a.p entry hentry
  have hdegree :=
    HexBerlekampZassenhausMathlib.factorize_entries_degree_pos
      a.p hpne entry hentry
  have hirredProp :=
    HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit
      a.p entry hentry
  have hirred : ZPoly.isIrreducible entry.1 = true :=
    (Hex.ZPoly.isIrreducible_iff
      entry.1).mpr hirredProp
  let checked : ZPoly.CheckedIrreducible entry.1 := ⟨hirred, hdegree⟩
  let : ZPoly.CheckedIrreducible entry.1 := checked
  have hentryNe : entry.1 ≠ 0 := by
    intro hq
    rw [hq] at hdegree
    simp at hdegree
  have hsimple : HasOnlySimpleRoots entry.1 :=
    (HexRootsMathlib.hasOnlySimpleRoots_iff_separable entry.1
      hentryNe).mpr (ZPoly.CheckedIrreducible.separable entry.1)
  have hfactor := exactFactor?_isSome a entry.1 hprim hpos hdegree
    hirred hsimple (by
      simpa [HexRootsMathlib.toPolyℂ] using hentryRoot)
  rw [AlgebraicRoot.exact?, ← Array.foldl_toList]
  exact exactFold_isSome_of_mem a _
    (Array.mem_toList_iff.mpr hentry) hfactor

/-- The total canonicalization wrapper preserves the represented value. -/
theorem exact_toComplex (a : AlgebraicRoot) :
    a.exact.toComplex = a.toComplex := by
  cases h : a.exact? with
  | none =>
      have hsome := exact?_isSome a
      simp [h] at hsome
  | some b =>
      simpa [AlgebraicRoot.exact, h] using exact?_sound a h

end AlgebraicRoot

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

open scoped QAdjoinField

private theorem range_findSome?_eq_some {α : Type*} {n : Nat}
    {f : Nat → Option α} {a : α}
    (h : (List.range n).findSome? f = some a) :
    ∃ i, i < n ∧ f i = some a ∧ (∀ j < i, f j = none) := by
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨before, found, after, hrange, hfound, hbefore⟩ := h
  rw [List.range_eq_range'] at hrange
  obtain ⟨k, hkn, hbeforeRange, hafterRange⟩ :=
    List.range'_eq_append_iff.mp hrange
  have hcons := hafterRange.symm
  rw [List.range'_eq_cons_iff] at hcons
  have hkfound : k = found := by omega
  subst found
  have hklt : k < n := by omega
  have hprior : ∀ j < k, f j = none := by
    intro j hj
    apply hbefore j
    rw [hbeforeRange]
    simp [List.mem_range']
    omega
  exact ⟨k, hklt, hfound, hprior⟩

private theorem relationPoly_coeff {k : Nat} (coeffs : Vector Rat k)
    (i : Fin k) :
    (relationPoly coeffs).coeff i.val = -coeffs[i] := by
  rw [relationPoly, DensePoly.coeff_ofCoeffs]
  simp [Array.getD, Array.getElem_push]

private theorem relationPoly_coeff_top {k : Nat} (coeffs : Vector Rat k) :
    (relationPoly coeffs).coeff k = 1 := by
  rw [relationPoly, DensePoly.coeff_ofCoeffs]
  have hsize : (coeffs.toArray.map fun c => -c).size = k := by simp
  simp [Array.getD, Array.getElem_push, hsize]

private theorem relationPoly_size {k : Nat} (coeffs : Vector Rat k) :
    (relationPoly coeffs).size = k + 1 := by
  apply Nat.le_antisymm
  · exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
  · by_contra h
    have hle : (relationPoly coeffs).size ≤ k := by omega
    have hzero := DensePoly.coeff_eq_zero_of_size_le
      (relationPoly coeffs) hle
    rw [relationPoly_coeff_top coeffs] at hzero
    norm_num at hzero

private theorem relationPoly_natDegree {k : Nat} (coeffs : Vector Rat k) :
    (HexPolyMathlib.toPolynomial (relationPoly coeffs)).natDegree = k := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  simp [DensePoly.degree?, relationPoly_size coeffs]

private theorem adjoinRoot_repr [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (i : Fin (definingPolynomial p).natDegree) :
    (AdjoinRoot.powerBasisAux' (definingPolynomial_monic p)).repr
        (toAdjoinRoot a) i = a.coeffs.coeff i.val := by
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, toAdjoinRoot,
    AdjoinRoot.modByMonicHom_mk]
  rw [(Polynomial.modByMonic_eq_self_iff
    (definingPolynomial_monic p)).mpr]
  · rw [HexPolyMathlib.coeff_toPolynomial]
  · apply Polynomial.degree_lt_degree
    rw [HexPolyMathlib.natDegree_toPolynomial,
      natDegree_definingPolynomial]
    exact a.degree_lt

private noncomputable def adjoinRootAlgEquiv [ZPoly.CheckedIrreducible p] :
    QAdjoin p x ≃ₐ[Rat] AdjoinRoot (definingPolynomial p) :=
  AlgEquiv.ofRingEquiv
      (f := adjoinRootEquiv (p := p) (x := x)) fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change toAdjoinRoot (r • (1 : QAdjoin p x)) =
      r • (1 : AdjoinRoot (definingPolynomial p))
    rw [toAdjoinRoot_smul, toAdjoinRoot_one]

private theorem natPow_succ [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := pow_succ a n

private theorem krylovPowers_get [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (n : Nat)
    (i : Fin (n + 1)) :
    (krylovPowers a n).get i = a ^ i.val := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change (krylovPowers a 0).get 0 = natPow a 0
      unfold krylovPowers Vector.get natPow
      rfl
  | succ n ih =>
      by_cases hi : i = Fin.last (n + 1)
      · subst i
        simp [krylovPowers, ih]
        exact (natPow_succ a n).symm
      · let j : Fin (n + 1) := ⟨i.val, by
          have hilast : i.val ≠ n + 1 := by
            intro hval
            apply hi
            exact Fin.ext hval
          omega⟩
        have hij : i = Fin.castSucc j := Fin.ext rfl
        rw [hij]
        simp [krylovPowers, ih]

private theorem krylovOrbit_get [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (i : Fin (p.degree?.getD 0 + 1)) :
    a.krylovOrbit.get i = a ^ i.val := by
  exact krylovPowers_get a _ i

private theorem vecMul_of_linear [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) (coeffs : Vector Rat k)
    (hlinear : ∑ i : Fin k, coeffs[i] • a ^ i.val = a ^ k) :
    Matrix.vecMul coeffs
        (Matrix.ofFn fun i : Fin k => fun j : Fin (p.degree?.getD 0) =>
          (a ^ i.val).coeffs.coeff j) =
      Vector.ofFn fun j : Fin (p.degree?.getD 0) =>
        (a ^ k).coeffs.coeff j := by
  have himage := congrArg (adjoinRootEquiv (p := p) (x := x)) hlinear
  simp only [map_sum, adjoinRootEquiv_apply, toAdjoinRoot_smul] at himage
  let B := AdjoinRoot.powerBasisAux' (definingPolynomial_monic p)
  have hrepr := congrArg B.repr himage
  apply Vector.ext
  intro j _hj
  have hjlt : j < (definingPolynomial p).natDegree := by
    rw [natDegree_definingPolynomial]
    exact _hj
  let j' : Fin (definingPolynomial p).natDegree := ⟨j, hjlt⟩
  have hj := congrArg (fun v => v j') hrepr
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply,
    Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hj
  have hrepr' (b : QAdjoin p x) :
      (B.repr (toAdjoinRoot b)) j' = b.coeffs.coeff j := by
    simpa [B, j'] using adjoinRoot_repr b j'
  rw [hrepr' (a ^ k)] at hj
  have hsum :
      (∑ i : Fin k, coeffs[i] *
        (B.repr (toAdjoinRoot (a ^ i.val))) j') =
        ∑ i : Fin k, coeffs[i] * (a ^ i.val).coeffs.coeff j := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hrepr' (a ^ i.val)]
  rw [hsum] at hj
  let jf : Fin (p.degree?.getD 0) := ⟨j, _hj⟩
  change (coeffs * (Matrix.ofFn fun i : Fin k =>
    fun j : Fin (p.degree?.getD 0) => (a ^ i.val).coeffs.coeff j))[jf] =
      (Vector.ofFn fun j : Fin (p.degree?.getD 0) =>
        (a ^ k).coeffs.coeff j)[jf]
  rw [Matrix.getElem_vecMul, HexMatrixMathlib.dotProduct_eq]
  have hentry (i : Fin k) :
      (Matrix.getRow (Matrix.ofFn fun i : Fin k =>
        fun j : Fin (p.degree?.getD 0) =>
          (a ^ i.val).coeffs.coeff j) i)[jf] =
        (a ^ i.val).coeffs.coeff jf.val := by
    rw [← Matrix.getElem_eq_getRow, Matrix.getElem_ofFn]
  simpa [dotProduct, Matrix.col, hentry, jf, mul_comm] using hj

private theorem relationAt?_isSome_of_linear [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) (coeffs : Vector Rat k)
    (hk : k ≤ p.degree?.getD 0)
    (hlinear : ∑ i : Fin k, coeffs[i] • a ^ i.val = a ^ k) :
    (a.relationAt? a.krylovOrbit k).isSome := by
  let previous : Matrix Rat k (p.degree?.getD 0) :=
    Matrix.ofFn fun i j =>
      (a.krylovOrbit.get ⟨i.val, by omega⟩).coeffs.coeff j
  let target : Vector Rat (p.degree?.getD 0) :=
    Vector.ofFn fun j =>
      (a.krylovOrbit.get ⟨k, Nat.lt_succ_of_le hk⟩).coeffs.coeff j
  have hcoords : Matrix.vecMul coeffs previous = target := by
    simpa [previous, target, krylovOrbit_get] using
      vecMul_of_linear a k coeffs hlinear
  have hnotnone : Matrix.spanCoeffs previous target ≠ none := by
    intro hnone
    exact (Matrix.spanCoeffs_eq_none_iff previous target).mp hnone
      ⟨coeffs, hcoords⟩
  unfold relationAt?
  dsimp only
  rw [dite_eq_left hk]
  cases hspan : Matrix.spanCoeffs previous target with
  | none => exact (hnotnone hspan).elim
  | some found => simp

private theorem minpoly_relation [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) :
    let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
    let d := (minpoly Rat b).natDegree
    0 < d ∧ d ≤ p.degree?.getD 0 ∧
      (a.relationAt? a.krylovOrbit d).isSome := by
  let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
  let : Module.Free Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).free_adjoinRoot
  let : Module.Finite Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).finite_adjoinRoot
  have hbint : IsIntegral Rat b := IsIntegral.of_finite Rat b
  let m : Polynomial Rat := minpoly Rat b
  let d : Nat := m.natDegree
  have hmonic : m.Monic := minpoly.monic hbint
  have hdpos : 0 < d := minpoly.natDegree_pos hbint
  have hdle : d ≤ p.degree?.getD 0 := by
    have hbound := minpoly.natDegree_le (A := Rat) b
    have hfinrank : Module.finrank Rat
        (AdjoinRoot (definingPolynomial p)) =
        (definingPolynomial p).natDegree :=
      (AdjoinRoot.powerBasis' (definingPolynomial_monic p)).finrank
    rw [hfinrank] at hbound
    simpa [d, m, natDegree_definingPolynomial] using hbound
  let coeffs : Vector Rat d := Vector.ofFn fun i => -m.coeff i.val
  have hbzero := minpoly.aeval Rat b
  have hblinear : ∑ i : Fin d, coeffs[i] • b ^ i.val = b ^ d := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
      hmonic.coeff_natDegree] at hbzero
    have hcoeff (i : Fin d) : coeffs[i] = -m.coeff i.val := by
      simp [coeffs]
    simp_rw [hcoeff]
    simp only [neg_smul, Finset.sum_neg_distrib]
    rw [neg_eq_iff_add_eq_zero]
    rw [← Fin.sum_univ_eq_sum_range] at hbzero
    simpa [d, m] using hbzero
  have halinear : ∑ i : Fin d, coeffs[i] • a ^ i.val = a ^ d := by
    apply (adjoinRootEquiv (p := p) (x := x)).injective
    simp only [map_sum, adjoinRootEquiv_apply, toAdjoinRoot_smul]
    have hpow (i : Nat) : toAdjoinRoot (a ^ i) = toAdjoinRoot a ^ i := by
      change adjoinRootEquiv (a ^ i) = adjoinRootEquiv a ^ i
      rw [map_pow]
    simp_rw [hpow]
    simpa [b] using hblinear
  have hrelation := relationAt?_isSome_of_linear a d coeffs hdle halinear
  exact ⟨hdpos, hdle, hrelation⟩

private theorem minpoly?_isSome [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) : a.minpoly?.isSome := by
  let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
  let d := (minpoly Rat b).natDegree
  obtain ⟨hdpos, hdle, hrelation⟩ :
      0 < d ∧ d ≤ p.degree?.getD 0 ∧
        (a.relationAt? a.krylovOrbit d).isSome := by
    simpa [b, d] using minpoly_relation a
  unfold minpoly?
  rw [List.findSome?_isSome_iff]
  refine ⟨d - 1, ?_, ?_⟩
  · simp
    omega
  · rw [Nat.sub_add_cancel (n := d) (m := 1) hdpos]
    exact hrelation

private theorem span_relation [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) (coeffs : Vector Rat k)
    (hspan : Matrix.spanCoeffs
        (Matrix.ofFn fun i : Fin k => fun j : Fin (p.degree?.getD 0) =>
          (a ^ i.val).coeffs.coeff j)
        (Vector.ofFn fun j : Fin (p.degree?.getD 0) =>
          (a ^ k).coeffs.coeff j) = some coeffs) :
    Polynomial.aeval a
      (HexPolyMathlib.toPolynomial (relationPoly coeffs)) = 0 := by
  have hcoords := Matrix.spanCoeffs_sound _ _ _ hspan
  have hlinear : ∑ i : Fin k, coeffs[i] • a ^ i.val = a ^ k := by
    apply (adjoinRootEquiv (p := p) (x := x)).injective
    simp only [map_sum, adjoinRootEquiv_apply, toAdjoinRoot_smul]
    let B := AdjoinRoot.powerBasisAux' (definingPolynomial_monic p)
    apply B.repr.injective
    ext j
    simp only [map_sum, map_smulₛₗ, RingHom.id_apply,
      Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hrepr (b : QAdjoin p x) :
        (B.repr (toAdjoinRoot b)) j = b.coeffs.coeff j.val := by
      simpa [B] using adjoinRoot_repr b j
    rw [hrepr (a ^ k)]
    have hsum :
        (∑ i : Fin k, coeffs[i] *
          (B.repr (toAdjoinRoot (a ^ i.val))) j) =
        ∑ i : Fin k, coeffs[i] * (a ^ i.val).coeffs.coeff j.val := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrepr (a ^ i.val)]
    rw [hsum]
    have hjlt : j.val < p.degree?.getD 0 := by
      rw [← natDegree_definingPolynomial p]
      exact j.isLt
    let j' : Fin (p.degree?.getD 0) := ⟨j.val, hjlt⟩
    have hj := congrArg
      (fun v : Vector Rat (p.degree?.getD 0) => v[j']) hcoords
    change (coeffs * (Matrix.ofFn fun i : Fin k =>
      fun j : Fin (p.degree?.getD 0) => (a ^ i.val).coeffs.coeff j))[j'] =
        (Vector.ofFn fun j : Fin (p.degree?.getD 0) =>
          (a ^ k).coeffs.coeff j)[j'] at hj
    rw [Matrix.getElem_vecMul, HexMatrixMathlib.dotProduct_eq] at hj
    have hentry (i : Fin k) :
        (Matrix.getRow (Matrix.ofFn fun i : Fin k =>
          fun j : Fin (p.degree?.getD 0) =>
            (a ^ i.val).coeffs.coeff j) i)[j'] =
          (a ^ i.val).coeffs.coeff j'.val := by
      rw [← Matrix.getElem_eq_getRow, Matrix.getElem_ofFn]
    have hj' :
        (∑ i : Fin k, (a ^ i.val).coeffs.coeff j.val * coeffs[i]) =
          (a ^ k).coeffs.coeff j.val := by
      simpa [dotProduct, Matrix.col, hentry, j',
        natDegree_definingPolynomial] using hj
    calc
      _ = ∑ i : Fin k, (a ^ i.val).coeffs.coeff j.val * coeffs[i] := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact mul_comm _ _
      _ = _ := hj'
  rw [Polynomial.aeval_def, HexPolyMathlib.eval₂_toPolynomial]
  rw [relationPoly_size, Finset.sum_range_succ, relationPoly_coeff_top]
  have hlow :
      (∑ i ∈ Finset.range k,
        (algebraMap Rat (QAdjoin p x)) ((relationPoly coeffs).coeff i) * a ^ i) =
        -∑ i : Fin k, coeffs[i] • a ^ i.val := by
    rw [← Finset.sum_neg_distrib, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [relationPoly_coeff coeffs ⟨i, hik⟩,
      (algebraMap Rat (QAdjoin p x)).map_neg]
    simp [hik, Algebra.smul_def]
  rw [hlow, hlinear]
  simp

private theorem relationAt?_sound [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) {q : ZPoly}
    (hq : a.relationAt? a.krylovOrbit k = some q) :
    Polynomial.aeval a (HexPolyZMathlib.toPolyℚ q) = 0 := by
  unfold relationAt? at hq
  dsimp only at hq
  split at hq
  · obtain ⟨coeffs, hspan, rfl⟩ := Option.map_eq_some_iff.mp hq
    have hspan' : Matrix.spanCoeffs
        (Matrix.ofFn fun i : Fin k =>
          fun j : Fin (p.degree?.getD 0) =>
            (a ^ i.val).coeffs.coeff j)
        (Vector.ofFn fun j : Fin (p.degree?.getD 0) =>
          (a ^ k).coeffs.coeff j) = some coeffs := by
      simpa only [krylovOrbit_get] using hspan
    have hrel := span_relation a k coeffs hspan'
    rcases ZPoly.ratPolyPrimitivePart_rational_associate
        (relationPoly coeffs) with ⟨u, hu⟩
    have hrelation_ne : relationPoly coeffs ≠ 0 := by
      intro hzero
      have htop := relationPoly_coeff_top coeffs
      rw [hzero] at htop
      simp at htop
    have hu_ne : u ≠ 0 := by
      intro hzero
      rw [hzero] at hu
      simp at hu
      exact hrelation_ne hu
    have hpoly := congrArg HexPolyMathlib.toPolynomial hu
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly] at hpoly
    have hscaled :
        (algebraMap Rat (QAdjoin p x)) u *
          Polynomial.aeval a
            (HexPolyZMathlib.toPolyℚ
              (ZPoly.ratPolyPrimitivePart (relationPoly coeffs))) = 0 := by
      simpa [hpoly] using hrel
    exact (mul_eq_zero.mp hscaled).resolve_left
      (by simpa using (algebraMap Rat (QAdjoin p x)).injective.ne hu_ne)
  · simp at hq

private theorem relationAt?_natDegree [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) {q : ZPoly}
    (hq : a.relationAt? a.krylovOrbit k = some q) :
    (HexPolyZMathlib.toPolyℚ q).natDegree = k := by
  unfold relationAt? at hq
  dsimp only at hq
  split at hq
  · obtain ⟨coeffs, _hspan, rfl⟩ := Option.map_eq_some_iff.mp hq
    rcases ZPoly.ratPolyPrimitivePart_rational_associate
        (relationPoly coeffs) with ⟨u, hu⟩
    have hrelation_ne : relationPoly coeffs ≠ 0 := by
      intro hzero
      have htop := relationPoly_coeff_top coeffs
      rw [hzero] at htop
      simp at htop
    have hu_ne : u ≠ 0 := by
      intro hzero
      rw [hzero] at hu
      simp at hu
      exact hrelation_ne hu
    have hpoly := congrArg HexPolyMathlib.toPolynomial hu
    rw [HexPolyMathlib.toPolynomial_scale,
      HexPolyZMathlib.toPolynomial_toRatPoly] at hpoly
    have hdegree := congrArg Polynomial.natDegree hpoly
    rw [relationPoly_natDegree, Polynomial.natDegree_C_mul hu_ne] at hdegree
    exact hdegree.symm
  · simp at hq

private theorem relationAt?_degree [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (k : Nat) {q : ZPoly}
    (hq : a.relationAt? a.krylovOrbit k = some q) :
    q.degree?.getD 0 = k := by
  have hdegree := relationAt?_natDegree a k hq
  rw [HexPolyZMathlib.toPolyℚ,
    Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom Rat)),
    HexPolyMathlib.natDegree_toPolynomial] at hdegree
  exact hdegree

private theorem minpoly?_sound [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) {q : ZPoly} (hq : a.minpoly? = some q) :
    Polynomial.aeval a (HexPolyZMathlib.toPolyℚ q) = 0 := by
  unfold minpoly? at hq
  obtain ⟨k, _hk, hrelation⟩ := List.exists_of_findSome?_eq_some hq
  exact relationAt?_sound a (k + 1) hrelation

private theorem minpoly?_natDegree [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) {q : ZPoly} (hq : a.minpoly? = some q) :
    let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
    (HexPolyZMathlib.toPolyℚ q).natDegree = (minpoly Rat b).natDegree := by
  let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
  let d := (minpoly Rat b).natDegree
  let : Module.Free Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).free_adjoinRoot
  let : Module.Finite Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).finite_adjoinRoot
  have hbint : IsIntegral Rat b := IsIntegral.of_finite Rat b
  unfold minpoly? at hq
  dsimp only at hq
  obtain ⟨i, hi, hrelation, hprior⟩ := range_findSome?_eq_some hq
  have hqdegree := relationAt?_natDegree a (i + 1) hrelation
  have hqrootA := relationAt?_sound a (i + 1) hrelation
  let E := adjoinRootAlgEquiv (p := p) (x := x)
  have hqrootB : Polynomial.aeval b (HexPolyZMathlib.toPolyℚ q) = 0 := by
    change Polynomial.aeval (E a) (HexPolyZMathlib.toPolyℚ q) = 0
    rw [Polynomial.aeval_algEquiv]
    simp [hqrootA]
  have hqne : HexPolyZMathlib.toPolyℚ q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hdvd : minpoly Rat b ∣ HexPolyZMathlib.toPolyℚ q :=
    minpoly.dvd Rat b hqrootB
  have hdle : d ≤ i + 1 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hqne
    have hbase : d ≤ (HexPolyZMathlib.toPolyℚ q).natDegree := by
      simpa [d] using this
    exact hbase.trans_eq hqdegree
  obtain ⟨hdpos, _hdbound, hdrelation⟩ :
      0 < d ∧ d ≤ p.degree?.getD 0 ∧
        (a.relationAt? a.krylovOrbit d).isSome := by
    simpa [b, d] using minpoly_relation a
  have hile : i + 1 ≤ d := by
    by_contra hnot
    have hdlt : d < i + 1 := Nat.lt_of_not_ge hnot
    have hnone := hprior (d - 1) (by omega)
    have hnone' : a.relationAt? a.krylovOrbit d = none := by
      simpa [Nat.sub_add_cancel (n := d) (m := 1) hdpos] using hnone
    rw [hnone'] at hdrelation
    simp at hdrelation
  have hid : i + 1 = d := Nat.le_antisymm hile hdle
  exact hqdegree.trans hid

private theorem minpoly?_certificates [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) {q : ZPoly} (hq : a.minpoly? = some q) :
    ZPoly.content q = 1 ∧ 0 < q.leadingCoeff ∧
      0 < q.degree?.getD 0 ∧ ZPoly.isIrreducible q = true ∧
      HasOnlySimpleRoots q := by
  have hdegreeMin := minpoly?_natDegree a hq
  have hrootA := minpoly?_sound a hq
  have hfind := hq
  unfold minpoly? at hfind
  dsimp only at hfind
  obtain ⟨i, hi, hrelation, _hprior⟩ :=
    range_findSome?_eq_some hfind
  have hrelation' := hrelation
  unfold relationAt? at hrelation
  dsimp only at hrelation
  rw [dite_eq_left (by omega : i + 1 ≤ p.degree?.getD 0)] at hrelation
  obtain ⟨coeffs, _hspan, rfl⟩ := Option.map_eq_some_iff.mp hrelation
  have hrelationNe : relationPoly coeffs ≠ 0 := by
    intro hzero
    have htop := relationPoly_coeff_top coeffs
    rw [hzero] at htop
    simp at htop
  have hpos : 0 < (ZPoly.ratPolyPrimitivePart
      (relationPoly coeffs)).leadingCoeff :=
    ZPoly.leadingCoeff_ratPolyPrimitivePart_pos_of_ne_zero
      (relationPoly coeffs) hrelationNe
  have hdegreeEq := relationAt?_degree a (i + 1) hrelation'
  have hdegree : 0 < (ZPoly.ratPolyPrimitivePart
      (relationPoly coeffs)).degree?.getD 0 := by omega
  have hqne : ZPoly.ratPolyPrimitivePart (relationPoly coeffs) ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hcontentNe : ZPoly.content
      (ZPoly.ratPolyPrimitivePart (relationPoly coeffs)) ≠ 0 := by
    intro hcontent
    have hreconstruct := ZPoly.content_mul_primitivePart
      (ZPoly.ratPolyPrimitivePart (relationPoly coeffs))
    rw [hcontent] at hreconstruct
    apply hqne
    simpa using hreconstruct.symm
  have hprim : ZPoly.Primitive
      (ZPoly.ratPolyPrimitivePart (relationPoly coeffs)) :=
    ZPoly.ratPolyPrimitivePart_primitive (relationPoly coeffs) hcontentNe
  let q := ZPoly.ratPolyPrimitivePart (relationPoly coeffs)
  let b : AdjoinRoot (definingPolynomial p) := toAdjoinRoot a
  let : Module.Free Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).free_adjoinRoot
  let : Module.Finite Rat (AdjoinRoot (definingPolynomial p)) :=
    (definingPolynomial_monic p).finite_adjoinRoot
  have hbint : IsIntegral Rat b := IsIntegral.of_finite Rat b
  let E := adjoinRootAlgEquiv (p := p) (x := x)
  have hrootB : Polynomial.aeval b (HexPolyZMathlib.toPolyℚ q) = 0 := by
    change Polynomial.aeval (E a) (HexPolyZMathlib.toPolyℚ q) = 0
    rw [Polynomial.aeval_algEquiv]
    simpa [q] using congrArg E hrootA
  have hqRatNe : HexPolyZMathlib.toPolyℚ q ≠ 0 := by
    intro hzero
    have hdegzero := congrArg Polynomial.natDegree hzero
    rw [Polynomial.natDegree_zero] at hdegzero
    have hratDegree : (HexPolyZMathlib.toPolyℚ q).natDegree =
        q.degree?.getD 0 := by
      rw [HexPolyZMathlib.toPolyℚ,
        Polynomial.natDegree_map_eq_of_injective
          (RingHom.injective_int (Int.castRingHom Rat)),
        HexPolyMathlib.natDegree_toPolynomial]
    rw [hratDegree] at hdegzero
    exact (Nat.ne_of_gt (by simpa [q] using hdegree)) hdegzero
  have hdvd : minpoly Rat b ∣ HexPolyZMathlib.toPolyℚ q :=
    minpoly.dvd Rat b hrootB
  have hdegreeMin' : (HexPolyZMathlib.toPolyℚ q).natDegree =
      (minpoly Rat b).natDegree := by
    simpa [q, b] using hdegreeMin
  have hassoc : Associated (minpoly Rat b) (HexPolyZMathlib.toPolyℚ q) :=
    Polynomial.associated_of_dvd_of_natDegree_le hdvd hqRatNe
      hdegreeMin'.le
  have hirredRat : Irreducible (HexPolyZMathlib.toPolyℚ q) :=
    hassoc.irreducible (minpoly.irreducible hbint)
  have hprimPoly : (HexPolyZMathlib.toPolynomial q).IsPrimitive :=
    HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive q (by
      simpa [q] using hprim)
  have hirredPoly : Irreducible (HexPolyZMathlib.toPolynomial q) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hprimPoly).mpr (by simpa [HexPolyZMathlib.toPolyℚ] using hirredRat)
  have hirredProp : ZPoly.Irreducible q :=
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible
      q).mpr hirredPoly
  have hirred : ZPoly.isIrreducible q = true :=
    (Hex.ZPoly.isIrreducible_iff q).mpr
      hirredProp
  let checked : ZPoly.CheckedIrreducible q := ⟨hirred, by
    simpa [q] using hdegree⟩
  let : ZPoly.CheckedIrreducible q := checked
  have hsimple : HasOnlySimpleRoots q :=
    (HexRootsMathlib.hasOnlySimpleRoots_iff_separable q (by simpa [q] using hqne)).mpr
      (ZPoly.CheckedIrreducible.separable q)
  exact ⟨by simpa [q, ZPoly.Primitive] using hprim,
    by simpa [q] using hpos, by simpa [q] using hdegree,
    hirred, hsimple⟩

private theorem minpoly?_complexRoot [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) {q : ZPoly} (hq : a.minpoly? = some q) :
    (HexPolyZMathlib.toPolyℚ q).eval₂ (algebraMap Rat ℂ)
      (toComplex a rep h) = 0 := by
  have hroot := minpoly?_sound a hq
  have hcomp :
      (algebraMap Rat ℂ).comp (RingHom.id Rat) =
        (embedding rep h).comp (algebraMap Rat (QAdjoin p x)) := by
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply]
    exact ((embedding rep h).map_rat_algebraMap r).symm
  have hmapped := Polynomial.map_aeval_eq_aeval_map hcomp
    (HexPolyZMathlib.toPolyℚ q) a
  rw [hroot, (embedding rep h).map_zero] at hmapped
  simpa [Polynomial.aeval_def] using hmapped.symm

private theorem dist_center_le_of_meets
    {b c : DyadicComplexBall} (hb : 0 ≤ b.realRadius)
    (hc : 0 ≤ c.realRadius) (h : b.meets c = true) :
    dist b.center c.center ≤ b.realRadius + c.realRadius := by
  have hdy :
      GaussDyadic.distSq (b.re, b.im) (c.re, c.im) ≤
        (b.radius + c.radius) * (b.radius + c.radius) := by
    simpa [DyadicComplexBall.meets] using of_decide_eq_true h
  have hreal := HexRootsMathlib.Dyadic.toReal_le_toReal_iff.mpr hdy
  apply (sq_le_sq₀ dist_nonneg (add_nonneg hb hc)).mp
  simpa only [HexRootsMathlib.Dyadic.toReal_mul,
    HexRootsMathlib.Dyadic.toReal_add,
    HexRootsMathlib.DyadicSquare.toReal_distSq,
    DyadicComplexBall.center, DyadicComplexBall.realRadius,
    pow_two] using hreal

private theorem meets_of_mem {b c : DyadicComplexBall} {z : ℂ}
    (hb : z ∈ b.set) (hc : z ∈ c.set) : b.meets c = true := by
  have hb' : dist b.center z ≤ b.realRadius := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hb
  have hc' : dist z c.center ≤ c.realRadius :=
    Metric.mem_closedBall.mp hc
  have hrb : 0 ≤ b.realRadius := dist_nonneg.trans hb'
  have hrc : 0 ≤ c.realRadius := dist_nonneg.trans hc'
  have hdist : dist b.center c.center ≤
      b.realRadius + c.realRadius := by
    exact (dist_triangle b.center z c.center).trans
      (add_le_add hb' hc')
  have hsq : dist b.center c.center ^ 2 ≤
      (b.realRadius + c.realRadius) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg hrb hrc)).mpr hdist
  have hreal :
      HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.distSq (b.re, b.im) (c.re, c.im)) ≤
        HexRootsMathlib.Dyadic.toReal
          ((b.radius + c.radius) * (b.radius + c.radius)) := by
    simpa only [HexRootsMathlib.Dyadic.toReal_mul,
      HexRootsMathlib.Dyadic.toReal_add,
      HexRootsMathlib.DyadicSquare.toReal_distSq,
      DyadicComplexBall.center, DyadicComplexBall.realRadius,
      pow_two] using hsq
  have hdy := HexRootsMathlib.Dyadic.toReal_le_toReal_iff.mp hreal
  simpa [DyadicComplexBall.meets] using decide_eq_true hdy

private theorem toBall_radius_lt_rootDist {q : ZPoly} (hq : q ≠ 0)
    {s : DyadicSquare} (hprec : (mahlerPrec q : Int) ≤ s.prec)
    {z w : ℂ} (hz : (HexRootsMathlib.toPolyℂ q).IsRoot z)
    (hw : (HexRootsMathlib.toPolyℂ q).IsRoot w) (hne : z ≠ w) :
    s.toBall.realRadius < ‖z - w‖ / 4 := by
  have hpow : (2 : ℝ) ^ (-s.prec) ≤
      (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  rw [DyadicSquare.toBall, DyadicComplexBall.realRadius,
    HexRootsMathlib.DyadicSquare.radiusHi_eq,
    HexRootsMathlib.DyadicSquare.halfWidth_eq]
  calc
    (2 : ℝ) ^ (-s.prec) *
        HexRootsMathlib.Dyadic.toReal sqrt2Hi =
        (2 : ℝ) ^ (-s.prec) * (1449 / 1024 : ℝ) := by
      congr 1
      norm_num [sqrt2Hi, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec]
    _ ≤ (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) *
        (1449 / 1024 : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ < ‖z - w‖ / 4 :=
      HexRootsMathlib.mahlerPrec_separates q hq z w hz hw hne

/-- A sufficiently small certified ball can meet a refined isolation only at
the root it contains. -/
theorem root_eq_of_meetsBall {q : ZPoly} (hq : q ≠ 0)
    (r : RefinedIsolation q) {z : ℂ}
    (hz : (HexRootsMathlib.toPolyℂ q).IsRoot z)
    {b : DyadicComplexBall} (hzmem : z ∈ b.set)
    (hbradius : b.realRadius ≤ (2 : ℝ) ^ (-(mahlerPrec q : ℤ)))
    (hmeet : r.1.square.meetsBall b = true) :
    r.root = z := by
  have hrmem : r.root ∈ r.1.square.toBall.set := by
    rw [DyadicComplexBall.set, Metric.mem_closedBall]
    change dist r.root (HexRootsMathlib.DyadicSquare.center r.1.square) ≤
      HexRootsMathlib.Dyadic.toReal r.1.square.radiusHi
    exact (Metric.mem_closedBall.mp
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc r)).trans
        (HexRootsMathlib.DyadicSquare.radius_lt_radiusHi r.1.square).le
  have hrnonneg : 0 ≤ r.1.square.toBall.realRadius :=
    dist_nonneg.trans (Metric.mem_closedBall.mp hrmem)
  have hbnonneg : 0 ≤ b.realRadius :=
    dist_nonneg.trans (Metric.mem_closedBall.mp hzmem)
  have hcenters := dist_center_le_of_meets hrnonneg hbnonneg (by
    simpa [DyadicSquare.meetsBall] using hmeet)
  by_contra hne
  have hrradius : r.1.square.toBall.realRadius < ‖r.root - z‖ / 4 :=
    toBall_radius_lt_rootDist hq r.property
      (HexRootsMathlib.RefinedIsolation.isRoot r) hz hne
  have hbasepos : 0 < (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) := by
    positivity
  have hbase_lt :
      (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) <
        (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) * (1449 / 1024 : ℝ) := by
    nlinarith
  have hbradius' : b.realRadius < ‖r.root - z‖ / 4 :=
    hbradius.trans_lt <| hbase_lt.trans <|
      HexRootsMathlib.mahlerPrec_separates q hq r.root z
        (HexRootsMathlib.RefinedIsolation.isRoot r) hz hne
  have hrcenter : dist r.root r.1.square.toBall.center ≤
      r.1.square.toBall.realRadius :=
    Metric.mem_closedBall.mp hrmem
  have hbcenter : dist b.center z ≤ b.realRadius := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hzmem
  have hdist : dist r.root z ≤
      2 * (r.1.square.toBall.realRadius + b.realRadius) := by
    calc
      dist r.root z ≤
          dist r.root r.1.square.toBall.center +
            dist r.1.square.toBall.center z := dist_triangle _ _ _
      _ ≤ dist r.root r.1.square.toBall.center +
          (dist r.1.square.toBall.center b.center + dist b.center z) := by
        simpa only [add_assoc] using add_le_add_right
          (dist_triangle r.1.square.toBall.center b.center z)
          (dist r.root r.1.square.toBall.center)
      _ ≤ r.1.square.toBall.realRadius +
          ((r.1.square.toBall.realRadius + b.realRadius) + b.realRadius) :=
        add_le_add hrcenter (add_le_add hcenters hbcenter)
      _ = 2 * (r.1.square.toBall.realRadius + b.realRadius) := by ring
  rw [Complex.dist_eq] at hdist
  have : ‖r.root - z‖ < ‖r.root - z‖ := by
    nlinarith [hrradius, hbradius']
  exact (lt_irrefl _ this)

/-- Successful conversion out of fixed coordinates preserves their value at
the selected embedding. -/
theorem toAlgebraicNumber?_sound [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) {b : AlgebraicNumber}
    (hb : a.toAlgebraicNumber? rep h = some b) :
    b.toComplex = toComplex a rep h := by
  unfold QAdjoin.toAlgebraicNumber? at hb
  obtain ⟨q, hq, hb⟩ := Option.bind_eq_some_iff.mp hb
  split at hb
  · rename_i hprim
    split at hb
    · rename_i hpos
      split at hb
      · rename_i hdegree
        split at hb
        · rename_i hirred
          split at hb
          · rename_i hsimple
            obtain ⟨isolations, hisolate, hb⟩ :=
              Option.bind_eq_some_iff.mp hb
            obtain ⟨refined, hrefined, hb⟩ :=
              Option.bind_eq_some_iff.mp hb
            obtain ⟨threaded, hthreaded, hb⟩ :=
              Option.bind_eq_some_iff.mp hb
            obtain ⟨matching, hmatching, hnormalized⟩ :=
              Option.bind_eq_some_iff.mp hb
            let requested : Int := mahlerPrec q
            let target : Int := requested +
              (approxGuardBits rep.1.square a.coeffs : Int)
            let valueBall := evalRatBall a.coeffs threaded.1.1.square target
            have hmeet : matching.1.square.meetsBall valueBall = true := by
              simpa [valueBall, target, requested] using
                List.find?_some hmatching
            have hvalueMem : toComplex a rep h ∈ valueBall.set := by
              have hsound := QAdjoin.approx_sound a rep h requested
              unfold QAdjoin.approx at hsound
              dsimp only at hsound
              rw [hthreaded] at hsound
              simpa [valueBall, target, requested] using hsound
            have hvalueRadius : valueBall.realRadius ≤
                (2 : ℝ) ^ (-(mahlerPrec q : ℤ)) := by
              have hradius := QAdjoin.approx_radius a rep h requested
              unfold QAdjoin.approx at hradius
              dsimp only at hradius
              rw [hthreaded] at hradius
              simpa [valueBall, target, requested] using hradius
            have hrootRat := minpoly?_complexRoot a rep h hq
            have hcomp :
                (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
                  Int.castRingHom ℂ := RingHom.ext_int _ _
            have hmap :
                (HexPolyZMathlib.toPolyℚ q).map (algebraMap Rat ℂ) =
                  HexRootsMathlib.toPolyℂ q := by
              dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
              rw [Polynomial.map_map, hcomp]
            have hroot :
                (HexRootsMathlib.toPolyℂ q).IsRoot (toComplex a rep h) := by
              rw [Polynomial.IsRoot.def, ← hmap, Polynomial.eval_map]
              exact hrootRat
            have hqne : q ≠ 0 := by
              intro hzero
              rw [hzero] at hdegree
              simp at hdegree
            have hrootEq : matching.root = toComplex a rep h :=
              root_eq_of_meetsBall hqne matching hroot hvalueMem
                hvalueRadius hmeet
            have hout := AlgebraicNumber.ofNormalized?_toComplex
              q hprim hpos hdegree ⟨hirred, hdegree⟩ hsimple matching
              hnormalized
            exact hout.trans hrootEq
          · simp at hb
        · simp at hb
      · simp at hb
    · simp at hb
  · simp at hb

/-- The minimal-polynomial and isolation search for fixed coordinates always
finds a canonical representative. -/
theorem toAlgebraicNumber?_isSome [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (a.toAlgebraicNumber? rep h).isSome := by
  have hmin := minpoly?_isSome a
  cases hq : a.minpoly? with
  | none => simp [hq] at hmin
  | some q =>
      obtain ⟨hprim, hpos, hdegree, hirred, hsimple⟩ :=
        minpoly?_certificates a hq
      unfold QAdjoin.toAlgebraicNumber?
      simp only [hq, Option.bind_eq_bind, Option.bind_some]
      rw [dite_eq_left hprim, dite_eq_left hpos, dite_eq_left hdegree,
        dite_eq_left hirred, dite_eq_left hsimple]
      have hqne : q ≠ 0 := by
        intro hzero
        rw [hzero] at hdegree
        simp at hdegree
      have hisolate := HexRootsMathlib.isolate_isSome q hsimple hqne
        (separationDepth q : Int) .nkThenPellet
      cases hrun : isolate q hsimple (separationDepth q : Int) with
      | none => simp [hrun] at hisolate
      | some isolations =>
          have hmapSome := HexRootsMathlib.array_mapM_isSome
            (xs := isolations) (f := DyadicRootIsolation.toRefined?)
            (fun iso hiso => by
              unfold DyadicRootIsolation.toRefined?
              rw [dite_eq_left (HexRootsMathlib.isolate_refined q hsimple
                (separationDepth q : Int) .nkThenPellet hrun iso hiso)]
              rfl)
          cases hmap : isolations.mapM DyadicRootIsolation.toRefined? with
          | none => simp [hmap] at hmapSome
          | some refined =>
              have hrootRat := minpoly?_complexRoot a rep h hq
              have hcomp :
                  (algebraMap Rat ℂ).comp (Int.castRingHom Rat) =
                    Int.castRingHom ℂ := RingHom.ext_int _ _
              have hpolyMap :
                  (HexPolyZMathlib.toPolyℚ q).map (algebraMap Rat ℂ) =
                    HexRootsMathlib.toPolyℂ q := by
                dsimp [HexPolyZMathlib.toPolyℚ, HexRootsMathlib.toPolyℂ]
                rw [Polynomial.map_map, hcomp]
              have hroot :
                  (HexRootsMathlib.toPolyℂ q).IsRoot
                    (toComplex a rep h) := by
                rw [Polynomial.IsRoot.def, ← hpolyMap,
                  Polynomial.eval_map]
                exact hrootRat
              obtain ⟨iso, hiso, hisoRoot⟩ :=
                HexRootsMathlib.isolate_root_mem_of_pos q hsimple
                  (separationDepth q : Int) .nkThenPellet hdegree hrun hroot
              obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
              have hi : i < isolations.size := by simpa using hiList
              obtain ⟨hmapSize, hmapGet⟩ :=
                HexRootsMathlib.array_mapM_some_get hmap
              have hj : i < refined.size := by
                simpa [← hmapSize] using hi
              have hto := hmapGet i hi hj
              have hraw : refined[i].1 = isolations[i] := by
                rw [DyadicRootIsolation.toRefined?] at hto
                split at hto
                · exact (congrArg Subtype.val (Option.some.inj hto)).symm
                · simp at hto
              have harrIso : isolations[i] = iso := by
                rw [← hidx]
                exact (Array.getElem_toList hi).symm
              have hrefinedRoot :
                  HexRootsMathlib.RefinedIsolation.root refined[i] =
                    toComplex a rep h := by
                change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 =
                  toComplex a rep h
                rw [hraw, harrIso]
                exact hisoRoot
              let requested : Int := mahlerPrec q
              let target : Int := requested +
                (approxGuardBits rep.1.square a.coeffs : Int)
              have hthreadSome :=
                Hex.RefinedIsolation.refineTo?_isSome rep target
              cases hthreaded : rep.refineTo? target .nkThenPellet with
              | none => simp [hthreaded] at hthreadSome
              | some threaded =>
                  let valueBall :=
                    evalRatBall a.coeffs threaded.1.1.square target
                  have hvalueMem :
                      toComplex a rep h ∈ valueBall.set := by
                    have hsound := QAdjoin.approx_sound a rep h requested
                    unfold QAdjoin.approx at hsound
                    dsimp only at hsound
                    rw [hthreaded] at hsound
                    simpa [valueBall, target, requested] using hsound
                  have hcandMem :
                      toComplex a rep h ∈
                        refined[i].1.square.toBall.set := by
                    rw [← hrefinedRoot]
                    exact DyadicComplexBall.mem_toBall
                      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc
                        refined[i])
                  have hmeet : refined[i].1.square.meetsBall valueBall = true := by
                    simpa [DyadicSquare.meetsBall] using
                      meets_of_mem hcandMem hvalueMem
                  have hmatching :
                      (refined.find? fun r =>
                        r.1.square.meetsBall valueBall).isSome := by
                    simp
                    exact ⟨refined[i], by
                      simp, hmeet⟩
                  cases hfind : refined.find? fun r =>
                      r.1.square.meetsBall valueBall with
                  | none => simp [hfind] at hmatching
                  | some matching =>
                      have hnormalized :=
                        AlgebraicNumber.ofNormalized?_isSome q hprim hpos
                          hdegree ⟨hirred, hdegree⟩ hsimple matching
                      simpa [hmap, hthreaded, hfind, valueBall, target,
                        requested] using hnormalized

/-- The total fixed-presentation conversion preserves the selected complex
value. -/
theorem toAlgebraicNumber_toComplex [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (a.toAlgebraicNumber rep h).toComplex = toComplex a rep h := by
  cases hb : a.toAlgebraicNumber? rep h with
  | none =>
      have hsome := toAlgebraicNumber?_isSome a rep h
      simp [hb] at hsome
  | some b =>
      simpa [QAdjoin.toAlgebraicNumber, hb] using
        toAlgebraicNumber?_sound a rep h hb

end QAdjoin

/-! The total exactification headlines must not inherit an unfinished proof. -/

/--
info: 'Hex.AlgebraicRoot.exact?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.exact?_isSome

/--
info: 'Hex.AlgebraicRoot.exact_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicRoot.exact_toComplex

/--
info: 'Hex.QAdjoin.toAlgebraicNumber?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.toAlgebraicNumber?_isSome

/--
info: 'Hex.QAdjoin.toAlgebraicNumber_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QAdjoin.toAlgebraicNumber_toComplex

end Hex
