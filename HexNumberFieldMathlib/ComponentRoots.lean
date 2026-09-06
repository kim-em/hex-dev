/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Roots
import Mathlib.Data.Prod.Lex

public section

/-!
# Semantics of fixed-field component root isolation

This module proves semantic contracts for the norm-isolation and selected-
embedding filter used on one square-free Yun component.
-/

namespace Hex.PolyQuot.Roots

variable {p : ZPoly} {x : SimpleRoot p}

private theorem intListLe_iff (as bs : List Int) :
    intListLe as bs ↔ as ≤ bs := by
  induction as generalizing bs with
  | nil =>
      constructor
      · intro _
        apply le_of_not_gt
        intro h
        cases h
      · intro _
        trivial
  | cons a as ih =>
      cases bs with
      | nil => simp [intListLe]
      | cons b bs =>
          by_cases hab : a < b
          · constructor
            · intro _
              exact le_of_lt (List.Lex.rel hab)
            · intro _
              simp [intListLe, hab]
          · by_cases hba : b < a
            · constructor
              · simp [intListLe, hab, hba]
              · intro hle
                exact (not_lt_of_ge hle (List.Lex.rel hba)).elim
            · have heq : a = b :=
                le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
              subst b
              rw [intListLe]
              simp only [lt_irrefl, ↓reduceIte]
              constructor
              · intro hle
                exact List.cons_le_cons a ((ih bs).mp hle)
              · intro hle
                rcases hle.lt_or_eq with hlt | heq
                · cases hlt with
                  | rel h => exact (lt_irrefl a h).elim
                  | cons h => exact (ih bs).mpr (le_of_lt h)
                · exact (ih bs).mpr (le_of_eq (congrArg List.tail heq))

private noncomputable def rootKey (a : RootCount) :
    List Int ×ₗ (Rat ×ₗ (Rat ×ₗ Int)) :=
  toLex (a.root.p.toArray.toList,
    toLex (a.root.rep.1.square.re.toRat,
      toLex (a.root.rep.1.square.im.toRat, a.root.rep.1.square.prec)))

private theorem rootPolynomial_eq_of_coefficients_eq (a b : RootCount)
    (hcoeff : a.root.p.toArray.toList = b.root.p.toArray.toList) :
    a.root.p = b.root.p := by
  have harr : a.root.p.toArray = b.root.p.toArray :=
    Array.toList_inj.mp hcoeff
  apply DensePoly.ext_coeff
  intro n
  rw [← DensePoly.toArray_getD, harr, DensePoly.toArray_getD]

private theorem rootLe_iff (a b : RootCount) :
    rootLe a b ↔ rootKey a ≤ rootKey b := by
  by_cases hp : a.root.p = b.root.p
  · by_cases hre : a.root.rep.1.square.re = b.root.rep.1.square.re
    · by_cases him : a.root.rep.1.square.im = b.root.rep.1.square.im
      · simp [rootLe, rootKey, hp, hre, him,
          Prod.Lex.toLex_le_toLex]
      · have hratIm : a.root.rep.1.square.im.toRat ≠
            b.root.rep.1.square.im.toRat := by
          intro hrat
          exact him (Dyadic.toRat_inj.mp hrat)
        simp [rootLe, rootKey, hp, hre, him, hratIm,
          Prod.Lex.toLex_le_toLex, Dyadic.toRat_lt_toRat_iff]
    · have hratRe : a.root.rep.1.square.re.toRat ≠
          b.root.rep.1.square.re.toRat := by
        intro hrat
        exact hre (Dyadic.toRat_inj.mp hrat)
      simp [rootLe, rootKey, hp, hre, hratRe,
        Prod.Lex.toLex_le_toLex, Dyadic.toRat_inj,
        Dyadic.toRat_lt_toRat_iff]
  · have hcoeff : a.root.p.toArray.toList ≠
        b.root.p.toArray.toList := by
      intro heq
      exact hp (rootPolynomial_eq_of_coefficients_eq a b heq)
    unfold rootKey
    rw [rootLe, ite_eq_left (by simpa using hp), intListLe_iff,
      Prod.Lex.toLex_le_toLex]
    constructor
    · intro hle
      exact Or.inl (lt_of_le_of_ne hle hcoeff)
    · rintro (hlt | ⟨heq, _⟩)
      · exact le_of_lt hlt
      · exact (hcoeff heq).elim

private theorem rootLe_trans (a b c : RootCount) :
    rootLe a b → rootLe b c → rootLe a c := by
  simpa only [rootLe_iff] using
    (le_trans : rootKey a ≤ rootKey b →
      rootKey b ≤ rootKey c → rootKey a ≤ rootKey c)

private theorem rootLe_total (a b : RootCount) :
    rootLe a b || rootLe b a := by
  apply Bool.or_eq_true_iff.mpr
  rcases le_total (rootKey a) (rootKey b) with hab | hba
  · exact Or.inl (rootLe_iff a b |>.mpr hab)
  · exact Or.inr (rootLe_iff b a |>.mpr hba)

private theorem list_foldlM_sound {A B : Type*}
    {step : B → A → Option B} {property : B → Prop}
    (items : List A) (init final : B)
    (hinit : property init)
    (hstep : ∀ state item next, item ∈ items →
      step state item = some next → property state → property next)
    (hrun : items.foldlM step init = some final) :
    property final := by
  induction items generalizing init with
  | nil =>
      have hfinal : init = final := by simpa using hrun
      simpa [hfinal] using hinit
  | cons item items ih =>
      cases hnext : step init item with
      | none => simp [List.foldlM_cons, hnext] at hrun
      | some next =>
          have htail : items.foldlM step next = some final := by
            simpa [List.foldlM_cons, hnext] using hrun
          exact ih next (hstep init item next (by simp) hnext hinit)
            (fun state tail next hmem =>
              hstep state tail next (by simp [hmem])) htail

private theorem list_foldlM_split {A B : Type*}
    {step : B → A → Option B} {items : List A} {item : A}
    {init final : B} (hitem : item ∈ items)
    (hrun : items.foldlM step init = some final) :
    ∃ pre suffix state next,
      items = pre ++ item :: suffix ∧
        pre.foldlM step init = some state ∧
        step state item = some next ∧
        suffix.foldlM step next = some final := by
  obtain ⟨pre, suffix, rfl⟩ := List.mem_iff_append.mp hitem
  cases hprefix : pre.foldlM step init with
  | none => simp [List.foldlM_append, hprefix] at hrun
  | some state =>
      cases hnext : step state item with
      | none =>
          simp [List.foldlM_append, hprefix, List.foldlM_cons, hnext] at hrun
      | some next =>
          refine ⟨pre, suffix, state, next, rfl, hprefix, hnext, ?_⟩
          simpa [List.foldlM_append, hprefix, List.foldlM_cons, hnext]
            using hrun

/-- Every entry returned by a successful component run is a root at the
selected embedding and carries the requested multiplicity. -/
theorem componentRoots?_sound [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) {roots : Array RootCount}
    (hrun : componentRoots? f multiplicity hMultiplicity rep h = some roots) :
    ∀ entry ∈ roots.toList,
      Polynomial.eval entry.root.toComplex (PolyQuot.toPolynomialAt f rep h) = 0 ∧
        entry.multiplicity = multiplicity := by
  unfold componentRoots? at hrun
  dsimp only at hrun
  split at hrun
  next hprim =>
    change ZPoly.Primitive (ZPoly.squareFreeCore (normEliminant f)) at hprim
    split at hrun
    next hpos =>
      split at hrun
      next hdegree =>
        split at hrun
        next hsimple =>
          cases hisolate : isolate (ZPoly.squareFreeCore (normEliminant f))
              hsimple (separationDepth
                (ZPoly.squareFreeCore (normEliminant f)) : Int) with
          | none => simp [hisolate] at hrun
          | some isolations =>
              rw [hisolate] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              cases hrefined : isolations.mapM
                  DyadicRootIsolation.toRefined? with
              | none =>
                  rw [hrefined] at hrun
                  simp at hrun
              | some refined =>
                  rw [hrefined] at hrun
                  simp only [Option.bind_some] at hrun
                  rw [← Array.foldlM_toList] at hrun
                  apply list_foldlM_sound refined.toList #[] roots (by simp)
                    (hrun := hrun)
                    (property := fun out => ∀ entry ∈ out.toList,
                      Polynomial.eval entry.root.toComplex
                          (PolyQuot.toPolynomialAt f rep h) = 0 ∧
                        entry.multiplicity = multiplicity)
                  · intro out candidateRep next _hcandidate hstep hout
                    let candidate : AlgebraicRoot :=
                      { p := ZPoly.squareFreeCore (normEliminant f)
                        prim := hprim
                        pos_lc := hpos
                        pos_degree := hdegree
                        squarefree := hsimple
                        x := SimpleRoot.mk candidateRep
                        rep := candidateRep
                        rep_mk := rfl }
                    cases hkeep : retainZero?
                        (evalEliminant f
                          (ZPoly.squareFreeCore (normEliminant f)))
                        (evalMajorant f candidate.p)
                        (evalBall? f rep h candidate) with
                    | none =>
                        simp [candidate, hkeep] at hstep
                    | some keep =>
                        cases keep with
                        | false =>
                            have hnext : out = next := by
                              simpa [candidate, hkeep] using hstep
                            simpa [← hnext] using hout
                        | true =>
                            have hnext : out.push
                                { root := candidate
                                  multiplicity
                                  multiplicity_pos := hMultiplicity } = next := by
                              simpa [candidate, hkeep] using hstep
                            rw [← hnext]
                            intro entry hentry
                            rw [Array.toList_push, List.mem_append,
                              List.mem_singleton] at hentry
                            rcases hentry with hentry | rfl
                            · exact hout entry hentry
                            · constructor
                              · exact (retainZero?_correct f rep h candidate
                                  (size_pos_of_core_degree f hdegree)
                                  hkeep).mp rfl
                              · rfl
        next hsimple => simp at hrun
      next hdegree => simp at hrun
    next hpos => simp at hrun
  next hprim => simp at hrun

/-- Every semantic root of a nonzero component occurs in a successful
component run with the requested multiplicity. -/
theorem componentRoots?_complete [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (multiplicity : Nat)
    (hMultiplicity : 0 < multiplicity) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (hf : !f.isZero) {roots : Array RootCount}
    (hrun : componentRoots? f multiplicity hMultiplicity rep h = some roots)
    (z : ℂ) (hz : Polynomial.eval z (PolyQuot.toPolynomialAt f rep h) = 0) :
    ∃ entry ∈ roots.toList,
      entry.root.toComplex = z ∧ entry.multiplicity = multiplicity := by
  have hnorm : normEliminant f ≠ 0 := normEliminant_ne_zero f hf
  have hnormRoot :
      (HexRootsMathlib.toPolyℂ (normEliminant f)).IsRoot z :=
    normEliminant_isRoot f rep h z hf hz
  have hcoreRoot :
      (HexRootsMathlib.toPolyℂ
        (ZPoly.squareFreeCore (normEliminant f))).IsRoot z :=
    HexPolyZMathlib.isRoot_squareFreeCore hnorm hnormRoot
  unfold componentRoots? at hrun
  dsimp only at hrun
  split at hrun
  next hprim =>
    change ZPoly.Primitive (ZPoly.squareFreeCore (normEliminant f)) at hprim
    split at hrun
    next hpos =>
      split at hrun
      next hdegree =>
        split at hrun
        next hsimple =>
          cases hisolate : isolate (ZPoly.squareFreeCore (normEliminant f))
              hsimple (separationDepth
                (ZPoly.squareFreeCore (normEliminant f)) : Int) with
          | none => simp [hisolate] at hrun
          | some isolations =>
              rw [hisolate] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              cases hrefined : isolations.mapM
                  DyadicRootIsolation.toRefined? with
              | none =>
                  rw [hrefined] at hrun
                  simp at hrun
              | some refined =>
                  rw [hrefined] at hrun
                  simp only [Option.bind_some] at hrun
                  rw [← Array.foldlM_toList] at hrun
                  obtain ⟨iso, hiso, hisoRoot⟩ :=
                    HexRootsMathlib.isolate_root_mem_of_pos
                      (ZPoly.squareFreeCore (normEliminant f)) hsimple
                      (separationDepth
                        (ZPoly.squareFreeCore (normEliminant f)) : Int)
                      .nkThenPellet hdegree hisolate hcoreRoot
                  obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
                  have hi : i < isolations.size := by simpa using hiList
                  obtain ⟨hmapSize, hmapGet⟩ :=
                    HexRootsMathlib.array_mapM_some_get hrefined
                  have hj : i < refined.size := by
                    simpa [← hmapSize] using hi
                  have hto := hmapGet i hi hj
                  have hrawIso : refined[i].1 = isolations[i] := by
                    rw [DyadicRootIsolation.toRefined?] at hto
                    split at hto
                    · exact (congrArg Subtype.val (Option.some.inj hto)).symm
                    · simp at hto
                  have harrIso : isolations[i] = iso := by
                    rw [← hidx]
                    exact (Array.getElem_toList hi).symm
                  have hrefinedRoot :
                      HexRootsMathlib.RefinedIsolation.root refined[i] = z := by
                    change HexRootsMathlib.DyadicRootIsolation.root
                      refined[i].1 = z
                    rw [hrawIso, harrIso]
                    exact hisoRoot
                  have hcandMem : refined[i] ∈ refined.toList :=
                    Array.getElem_mem_toList hj
                  obtain ⟨_prefix, suffix, state, next, _hitems, _hprefix,
                      hcandidateStep, hsuffix⟩ :=
                    list_foldlM_split hcandMem hrun
                  let candidate : AlgebraicRoot :=
                    { p := ZPoly.squareFreeCore (normEliminant f)
                      prim := hprim
                      pos_lc := hpos
                      pos_degree := hdegree
                      squarefree := hsimple
                      x := SimpleRoot.mk refined[i]
                      rep := refined[i]
                      rep_mk := rfl }
                  have hcandidateValue : candidate.toComplex = z := by
                    exact hrefinedRoot
                  obtain ⟨keep, hkeep⟩ := Option.isSome_iff_exists.mp
                    (retainZero?_isSome
                      (evalEliminant f
                        (ZPoly.squareFreeCore (normEliminant f)))
                      f rep h candidate)
                  have hcandidateZero : Polynomial.eval candidate.toComplex
                      (PolyQuot.toPolynomialAt f rep h) = 0 := by
                    rw [hcandidateValue]
                    exact hz
                  have hkeepTrue : keep = true := by
                    cases keep with
                    | false =>
                        have hfalse := (retainZero?_correct f rep h candidate
                          (size_pos_of_core_degree f hdegree)
                          hkeep).mpr hcandidateZero
                        simp at hfalse
                    | true => rfl
                  let selected : RootCount :=
                    { root := candidate
                      multiplicity
                      multiplicity_pos := hMultiplicity }
                  have hnext : state.push selected = next := by
                    simpa [candidate, selected, hkeep, hkeepTrue]
                      using hcandidateStep
                  rw [← hnext] at hsuffix
                  apply list_foldlM_sound suffix (state.push selected) roots
                    (property := fun out => ∃ entry ∈ out.toList,
                      entry.root.toComplex = z ∧
                        entry.multiplicity = multiplicity)
                    (by
                      refine ⟨selected, ?_, ?_, rfl⟩
                      · simp [selected]
                      · exact hcandidateValue)
                    (hrun := hsuffix)
                  intro out candidateRep next _hcandidate hstep hout
                  let candidate' : AlgebraicRoot :=
                    { p := ZPoly.squareFreeCore (normEliminant f)
                      prim := hprim
                      pos_lc := hpos
                      pos_degree := hdegree
                      squarefree := hsimple
                      x := SimpleRoot.mk candidateRep
                      rep := candidateRep
                      rep_mk := rfl }
                  cases hkeep' : retainZero?
                      (evalEliminant f
                        (ZPoly.squareFreeCore (normEliminant f)))
                      (evalMajorant f candidate'.p)
                      (evalBall? f rep h candidate') with
                  | none =>
                      simp [candidate', hkeep'] at hstep
                  | some keep' =>
                      cases keep' with
                      | false =>
                          have hnext' : out = next := by
                            simpa [candidate', hkeep'] using hstep
                          simpa [← hnext'] using hout
                      | true =>
                          have hnext' : out.push
                              { root := candidate'
                                multiplicity
                                multiplicity_pos := hMultiplicity } = next := by
                            simpa [candidate', hkeep'] using hstep
                          rcases hout with ⟨entry, hentry, hvalue, hmult⟩
                          refine ⟨entry, ?_, hvalue, hmult⟩
                          rw [← hnext', Array.toList_push,
                            List.mem_append]
                          exact Or.inl hentry
        next hsimple => simp at hrun
      next hdegree => simp at hrun
    next hpos => simp at hrun
  next hprim => simp at hrun

private theorem mergeRootList_contains (candidate : RootCount)
    (roots out : List RootCount)
    (hrun : mergeRootList candidate roots = some out) (z : ℂ) :
    (∃ entry ∈ out, entry.root.toComplex = z) ↔
      candidate.root.toComplex = z ∨
        ∃ entry ∈ roots, entry.root.toComplex = z := by
  induction roots generalizing out with
  | nil =>
      have hout : out = [candidate] := by
        simpa [mergeRootList] using hrun.symm
      subst out
      simp
  | cons current roots ih =>
      cases hsame : sameValue? current.root candidate.root with
      | none => simp [mergeRootList, hsame] at hrun
      | some same =>
          cases same with
          | true =>
              have hout : out =
                  { root := current.root
                    multiplicity := candidate.multiplicity
                    multiplicity_pos := candidate.multiplicity_pos } :: roots := by
                simpa [mergeRootList, hsame] using hrun.symm
              subst out
              have hvalue : current.root.toComplex =
                  candidate.root.toComplex :=
                (sameValue?_sound current.root candidate.root hsame).mp rfl
              simp [hvalue]
          | false =>
              cases htail : mergeRootList candidate roots with
              | none => simp [mergeRootList, hsame, htail] at hrun
              | some tail =>
                  have hout : out = current :: tail := by
                    simpa [mergeRootList, hsame, htail] using hrun.symm
                  subst out
                  simp only [List.mem_cons, exists_eq_or_imp]
                  rw [ih tail htail]
                  tauto

private theorem mergeRootList_value (candidate : RootCount)
    (roots out : List RootCount)
    (hrun : mergeRootList candidate roots = some out) (z : ℂ) (r : Nat)
    (hroots : ∀ entry ∈ roots, entry.root.toComplex = z →
      entry.multiplicity = r)
    (hcandidate : candidate.root.toComplex = z →
      candidate.multiplicity = r) :
    ∀ entry ∈ out, entry.root.toComplex = z →
      entry.multiplicity = r := by
  induction roots generalizing out with
  | nil =>
      have hout : out = [candidate] := by
        simpa [mergeRootList] using hrun.symm
      subst out
      simpa using hcandidate
  | cons current roots ih =>
      cases hsame : sameValue? current.root candidate.root with
      | none => simp [mergeRootList, hsame] at hrun
      | some same =>
          cases same with
          | true =>
              have hout : out =
                  { root := current.root
                    multiplicity := candidate.multiplicity
                    multiplicity_pos := candidate.multiplicity_pos } :: roots := by
                simpa [mergeRootList, hsame] using hrun.symm
              subst out
              intro entry hentry hvalue
              simp only [List.mem_cons] at hentry
              rcases hentry with hentry | hentry
              · subst entry
                exact hcandidate <|
                  ((sameValue?_sound current.root candidate.root hsame).mp
                    rfl).symm.trans hvalue
              · exact hroots entry (by simp [hentry]) hvalue
          | false =>
              cases htail : mergeRootList candidate roots with
              | none => simp [mergeRootList, hsame, htail] at hrun
              | some tail =>
                  have hout : out = current :: tail := by
                    simpa [mergeRootList, hsame, htail] using hrun.symm
                  subst out
                  intro entry hentry hvalue
                  simp only [List.mem_cons] at hentry
                  rcases hentry with hentry | hentry
                  · subst entry
                    exact hroots current (by simp) hvalue
                  · apply ih tail htail
                    · intro prior hprior
                      exact hroots prior (by simp [hprior])
                    · exact hentry
                    · exact hvalue

private theorem mergeRootList_nodup (candidate : RootCount)
    (roots out : List RootCount)
    (hrun : mergeRootList candidate roots = some out)
    (hnodup : roots.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex) :
    out.Pairwise fun a b => a.root.toComplex ≠ b.root.toComplex := by
  induction roots generalizing out with
  | nil =>
      have hout : out = [candidate] := by
        simpa [mergeRootList] using hrun.symm
      subst out
      simp
  | cons current roots ih =>
      have hpair := List.pairwise_cons.mp hnodup
      cases hsame : sameValue? current.root candidate.root with
      | none => simp [mergeRootList, hsame] at hrun
      | some same =>
          cases same with
          | true =>
              have hout : out =
                  { root := current.root
                    multiplicity := candidate.multiplicity
                    multiplicity_pos := candidate.multiplicity_pos } :: roots := by
                simpa [mergeRootList, hsame] using hrun.symm
              subst out
              exact List.pairwise_cons.mpr hpair
          | false =>
              cases htail : mergeRootList candidate roots with
              | none => simp [mergeRootList, hsame, htail] at hrun
              | some tail =>
                  have hout : out = current :: tail := by
                    simpa [mergeRootList, hsame, htail] using hrun.symm
                  subst out
                  apply List.pairwise_cons.mpr
                  refine ⟨?_, ih tail htail hpair.2⟩
                  intro entry hentry heq
                  have hcontains := (mergeRootList_contains candidate roots
                    tail htail entry.root.toComplex).mp
                    ⟨entry, hentry, rfl⟩
                  rcases hcontains with hcand | ⟨prior, hprior, hvalue⟩
                  · have hcurCand : current.root.toComplex ≠
                        candidate.root.toComplex := by
                      intro hsameValue
                      have hfalse :=
                        (sameValue?_sound current.root candidate.root
                          hsame).mpr hsameValue
                      simp at hfalse
                    exact hcurCand (heq.trans hcand.symm)
                  · exact hpair.1 prior hprior (heq.trans hvalue.symm)

private theorem mergeRoot_nodup (roots out : Array RootCount)
    (candidate : RootCount) (hrun : mergeRoot roots candidate = some out)
    (hnodup : roots.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex) :
    out.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex := by
  cases hmerged : mergeRootList candidate roots.toList with
  | none => simp [mergeRoot, hmerged] at hrun
  | some merged =>
      have hout : out = merged.toArray := by
        simpa [mergeRoot, hmerged] using hrun.symm
      subst out
      simpa using mergeRootList_nodup candidate roots.toList merged
        hmerged hnodup

private theorem mergeRoot_value (roots out : Array RootCount)
    (candidate : RootCount) (hrun : mergeRoot roots candidate = some out)
    (z : ℂ) (r : Nat)
    (hroots : ∀ entry ∈ roots.toList, entry.root.toComplex = z →
      entry.multiplicity = r)
    (hcandidate : candidate.root.toComplex = z →
      candidate.multiplicity = r) :
    ∀ entry ∈ out.toList, entry.root.toComplex = z →
      entry.multiplicity = r := by
  cases hmerged : mergeRootList candidate roots.toList with
  | none => simp [mergeRoot, hmerged] at hrun
  | some merged =>
      have hout : out = merged.toArray := by
        simpa [mergeRoot, hmerged] using hrun.symm
      subst out
      simpa using mergeRootList_value candidate roots.toList merged
        hmerged z r hroots hcandidate

private theorem mergeRoot_contains (roots out : Array RootCount)
    (candidate : RootCount) (hrun : mergeRoot roots candidate = some out)
    (z : ℂ) :
    (∃ entry ∈ out.toList, entry.root.toComplex = z) ↔
      candidate.root.toComplex = z ∨
        ∃ entry ∈ roots.toList, entry.root.toComplex = z := by
  cases hmerged : mergeRootList candidate roots.toList with
  | none => simp [mergeRoot, hmerged] at hrun
  | some merged =>
      have hout : out = merged.toArray := by
        simpa [mergeRoot, hmerged] using hrun.symm
      subst out
      simpa using mergeRootList_contains candidate roots.toList merged
        hmerged z

private theorem mergeRoots_nodup (roots candidates out : Array RootCount)
    (hrun : candidates.foldlM mergeRoot roots = some out)
    (hnodup : roots.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex) :
    out.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex := by
  rw [← Array.foldlM_toList] at hrun
  apply list_foldlM_sound candidates.toList roots out hnodup
    (property := fun state => state.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex)
    (hrun := hrun)
  intro state candidate next _ hstep hstate
  exact mergeRoot_nodup state next candidate hstep hstate

private theorem mergeRoots_value (roots candidates out : Array RootCount)
    (hrun : candidates.foldlM mergeRoot roots = some out)
    (z : ℂ) (r : Nat)
    (hroots : ∀ entry ∈ roots.toList, entry.root.toComplex = z →
      entry.multiplicity = r)
    (hcandidates : ∀ entry ∈ candidates.toList,
      entry.root.toComplex = z → entry.multiplicity = r) :
    ∀ entry ∈ out.toList, entry.root.toComplex = z →
      entry.multiplicity = r := by
  rw [← Array.foldlM_toList] at hrun
  apply list_foldlM_sound candidates.toList roots out hroots
    (property := fun state => ∀ entry ∈ state.toList,
      entry.root.toComplex = z → entry.multiplicity = r)
    (hrun := hrun)
  intro state candidate next hcandidate hstep hstate
  exact mergeRoot_value state next candidate hstep z r hstate
    (hcandidates candidate hcandidate)

private theorem mergeRoots_contains (roots candidates out : Array RootCount)
    (hrun : candidates.foldlM mergeRoot roots = some out) (z : ℂ) :
    (∃ entry ∈ out.toList, entry.root.toComplex = z) ↔
      (∃ entry ∈ roots.toList, entry.root.toComplex = z) ∨
        ∃ entry ∈ candidates.toList, entry.root.toComplex = z := by
  have list_contains : ∀ (items : List RootCount) (state : Array RootCount),
      items.foldlM mergeRoot state = some out →
        ((∃ entry ∈ out.toList, entry.root.toComplex = z) ↔
          (∃ entry ∈ state.toList, entry.root.toComplex = z) ∨
            ∃ entry ∈ items, entry.root.toComplex = z) := by
    intro items
    induction items with
    | nil =>
        intro state hlist
        have hout : state = out := by simpa using hlist
        subst out
        simp
    | cons candidate items ih =>
        intro state hlist
        cases hnext : mergeRoot state candidate with
        | none => simp [List.foldlM_cons, hnext] at hlist
        | some next =>
            have htail : items.foldlM mergeRoot next = some out := by
              simpa [List.foldlM_cons, hnext] using hlist
            rw [ih next htail, mergeRoot_contains state next candidate hnext z]
            simp only [List.mem_cons, exists_eq_or_imp]
            constructor
            · rintro ((hcandidate | hstate) | hitems)
              · exact Or.inr (Or.inl hcandidate)
              · exact Or.inl hstate
              · exact Or.inr (Or.inr hitems)
            · rintro (hstate | hcandidate | hitems)
              · exact Or.inl (Or.inr hstate)
              · exact Or.inl (Or.inl hcandidate)
              · exact Or.inr hitems
  exact list_contains candidates.toList roots (by simpa using hrun)

private theorem componentFold_contains [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x)
    (components : List (DensePoly (PolyQuot p x) × Nat))
    (hall : ∀ component ∈ components,
      0 < component.1.degree?.getD 0 ∧ 0 < component.2)
    (state out : Array RootCount)
    (hrun : components.foldlM
      (fun out component =>
        if hm : 0 < component.2 then do
          let found ← componentRoots? component.1 component.2 hm rep h
          found.foldlM mergeRoot out
        else
          none)
      state = some out) (z : ℂ) :
    (∃ entry ∈ out.toList, entry.root.toComplex = z) ↔
      (∃ entry ∈ state.toList, entry.root.toComplex = z) ∨
        ∃ component ∈ components,
          Polynomial.eval z
            (PolyQuot.toPolynomialAt component.1 rep h) = 0 := by
  induction components generalizing state with
  | nil =>
      have hout : state = out := by simpa using hrun
      subst out
      simp
  | cons component components ih =>
      have hcomponent := hall component (by simp)
      rw [List.foldlM_cons, dite_eq_left hcomponent.2] at hrun
      cases hfound : componentRoots? component.1 component.2 hcomponent.2 rep h with
      | none => simp [hfound] at hrun
      | some found =>
          cases hnext : found.foldlM mergeRoot state with
          | none => simp [hfound, hnext] at hrun
          | some next =>
              have htail : components.foldlM
                  (fun out component =>
                    if hm : 0 < component.2 then do
                      let found ← componentRoots? component.1 component.2 hm rep h
                      found.foldlM mergeRoot out
                    else
                      none)
                  next = some out := by
                simpa [hfound, hnext] using hrun
              have hcomponentNonzero : !component.1.isZero := by
                have hsize : 0 < component.1.size := by
                  by_contra hzero
                  have hsizeZero : component.1.size = 0 := by omega
                  rw [(DensePoly.degree?_eq_none_iff component.1).2 hsizeZero]
                    at hcomponent
                  simp at hcomponent
                have hfalse : component.1.isZero = false :=
                  (DensePoly.isZero_eq_false_iff component.1).2 hsize
                simp [hfalse]
              have hfoundIff :
                  (∃ entry ∈ found.toList, entry.root.toComplex = z) ↔
                    Polynomial.eval z
                      (PolyQuot.toPolynomialAt component.1 rep h) = 0 := by
                constructor
                · rintro ⟨entry, hentry, rfl⟩
                  exact (componentRoots?_sound component.1 component.2
                    hcomponent.2 rep h hfound entry hentry).1
                · intro hzero
                  obtain ⟨entry, hentry, hvalue, _hmult⟩ :=
                    componentRoots?_complete component.1 component.2
                      hcomponent.2 rep h hcomponentNonzero hfound z hzero
                  exact ⟨entry, hentry, hvalue⟩
              rw [ih (fun item hitem => hall item (by simp [hitem])) next htail,
                mergeRoots_contains state found next hnext z, hfoundIff]
              simp only [List.mem_cons, exists_eq_or_imp]
              constructor
              · rintro ((hstate | hcomponentRoot) | hcomponents)
                · exact Or.inl hstate
                · exact Or.inr (Or.inl hcomponentRoot)
                · exact Or.inr (Or.inr hcomponents)
              · rintro (hstate | hcomponentRoot | hcomponents)
                · exact Or.inl (Or.inl hstate)
                · exact Or.inl (Or.inr hcomponentRoot)
                · exact Or.inr hcomponents

private theorem componentFold_nodup [ZPoly.CheckedIrreducible p]
    (rep : RefinedIsolation p) (h : SimpleRoot.mk rep = x)
    (components : List (DensePoly (PolyQuot p x) × Nat))
    (hall : ∀ component ∈ components,
      0 < component.1.degree?.getD 0 ∧ 0 < component.2)
    (state out : Array RootCount)
    (hrun : components.foldlM
      (fun out component =>
        if hm : 0 < component.2 then do
          let found ← componentRoots? component.1 component.2 hm rep h
          found.foldlM mergeRoot out
        else
          none)
      state = some out)
    (hnodup : state.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex) :
    out.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex := by
  apply list_foldlM_sound components state out hnodup
    (property := fun roots => roots.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex)
    (hrun := hrun)
  intro roots component next hcomponent hstep hroots
  have hpositive := (hall component hcomponent).2
  rw [dite_eq_left hpositive] at hstep
  cases hfound : componentRoots? component.1 component.2 hpositive rep h with
  | none => simp [hfound] at hstep
  | some found =>
      rw [hfound] at hstep
      exact mergeRoots_nodup roots found next hstep hroots

private theorem componentFold_value [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x)
    (hf : PolyQuot.toPolynomialAt f rep h ≠ 0)
    (hdegree : 0 < f.degree?.getD 0)
    (state out : Array RootCount)
    (hrun : (yun f).toList.foldlM
      (fun out component =>
        if hm : 0 < component.2 then do
          let found ← componentRoots? component.1 component.2 hm rep h
          found.foldlM mergeRoot out
        else
          none)
      state = some out) (z : ℂ)
    (hstate : ∀ entry ∈ state.toList, entry.root.toComplex = z →
      entry.multiplicity =
        (PolyQuot.toPolynomialAt f rep h).rootMultiplicity z) :
    ∀ entry ∈ out.toList, entry.root.toComplex = z →
      entry.multiplicity =
        (PolyQuot.toPolynomialAt f rep h).rootMultiplicity z := by
  let embedding := PolyQuot.embedding rep h
  have hmap (g : DensePoly (PolyQuot p x)) :
      toPolynomialMap embedding g = PolyQuot.toPolynomialAt g rep h := by
    rw [toPolynomialMap_eq_map]
    exact (PolyQuot.toPolynomialAt_eq_map g rep h).symm
  have hfMap : toPolynomialMap embedding f ≠ 0 := by
    rw [hmap]
    exact hf
  apply list_foldlM_sound (yun f).toList state out hstate
    (property := fun roots => ∀ entry ∈ roots.toList,
      entry.root.toComplex = z → entry.multiplicity =
        (PolyQuot.toPolynomialAt f rep h).rootMultiplicity z)
    (hrun := hrun)
  intro roots component next hcomponent hstep hroots
  have hpositive := (yun_positive f component hcomponent).2
  rw [dite_eq_left hpositive] at hstep
  cases hfound : componentRoots? component.1 component.2 hpositive rep h with
  | none => simp [hfound] at hstep
  | some found =>
      rw [hfound] at hstep
      apply mergeRoots_value roots found next hstep z
        ((PolyQuot.toPolynomialAt f rep h).rootMultiplicity z) hroots
      intro entry hentry hvalue
      have hentrySound := componentRoots?_sound component.1 component.2
        hpositive rep h hfound entry hentry
      have hcomponentRoot :
          (toPolynomialMap embedding component.1).IsRoot z := by
        rw [hmap]
        rw [← hvalue]
        exact hentrySound.1
      rw [hentrySound.2,
        yun_sound embedding f hfMap hdegree z component hcomponent
          hcomponentRoot,
        hmap]

end Hex.PolyQuot.Roots

namespace Hex.PolyQuot

variable {p : ZPoly} {x : SimpleRoot p}

private theorem findMultiplicity_eq (entries : List RootCount) (z : ℂ)
    (r : Nat)
    (hvalue : ∀ entry ∈ entries, entry.root.toComplex = z →
      entry.multiplicity = r)
    (hcontains : (∃ entry ∈ entries, entry.root.toComplex = z) ↔ 0 < r) :
    ((entries.find? fun entry => entry.root.toComplex = z).map
      (fun entry => entry.multiplicity)).getD 0 = r := by
  classical
  induction entries with
  | nil =>
      have hr : r = 0 := by
        by_contra hr
        have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        simpa using hcontains.mpr hrpos
      simp [hr]
  | cons entry entries ih =>
      by_cases hz : entry.root.toComplex = z
      · have hmultiplicity := hvalue entry (by simp) hz
        simp [List.find?, hz, hmultiplicity]
      · have htail := ih
          (fun tail htail => hvalue tail (by simp [htail]))
          (by simpa [hz] using hcontains)
        simpa [List.find?, hz] using htail

private theorem findMultiplicity_mem (entries : List RootCount)
    (hnodup : entries.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex)
    (entry : RootCount) (hentry : entry ∈ entries) :
    ((entries.find? fun candidate =>
      candidate.root.toComplex = entry.root.toComplex).map
        (fun candidate => candidate.multiplicity)).getD 0 =
      entry.multiplicity := by
  classical
  induction entries with
  | nil => simp at hentry
  | cons current entries ih =>
      have hpair := List.pairwise_cons.mp hnodup
      rcases List.mem_cons.mp hentry with rfl | hentry
      · simp [List.find?]
      · have hne := hpair.1 entry hentry
        simpa [List.find?, hne] using ih hpair.2 hentry

private theorem sum_eq_valueSum (entries : List RootCount)
    (hnodup : entries.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex)
    (value : ℂ → Nat)
    (hvalue : ∀ entry ∈ entries,
      value entry.root.toComplex = entry.multiplicity) :
    (entries.map fun entry => entry.multiplicity).sum =
      ∑ z ∈ (entries.map fun entry => entry.root.toComplex).toFinset,
        value z := by
  classical
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      have hpair := List.pairwise_cons.mp hnodup
      have hnotmem : entry.root.toComplex ∉
          (entries.map fun tail => tail.root.toComplex).toFinset := by
        intro hmem
        rw [List.mem_toFinset] at hmem
        obtain ⟨tail, htail, hvalue⟩ := List.mem_map.mp hmem
        exact hpair.1 tail htail hvalue.symm
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert hnotmem]
      rw [hvalue entry (by simp),
        ih hpair.2 (fun tail htail => hvalue tail (by simp [htail]))]

private theorem foldlMultiplicity_eq_sum (entries : List RootCount) :
    entries.foldl (fun total entry => total + entry.multiplicity) 0 =
      (entries.map fun entry => entry.multiplicity).sum := by
  have aux : ∀ (items : List RootCount) (total : Nat),
      items.foldl (fun sum entry => sum + entry.multiplicity) total =
        total + (items.map fun entry => entry.multiplicity).sum := by
    intro items
    induction items with
    | nil => simp
    | cons entry items ih =>
        intro total
        rw [List.foldl_cons, ih]
        simp [Nat.add_assoc]
  simpa using aux entries 0

/-- Semantic membership in the fixed-field output is exactly polynomial
vanishing. -/
theorem contains_roots_iff [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    RootSet.Contains (PolyQuot.roots f rep h) z ↔
      Polynomial.eval z (PolyQuot.toPolynomialAt f rep h) = 0 := by
  by_cases hzero : PolyQuot.toPolynomialAt f rep h = 0
  · have hall : PolyQuot.roots f rep h = .all :=
      (roots_all_iff f rep h).2 hzero
    rw [hall, hzero]
    simp [RootSet.Contains]
  · have hf : !f.isZero := by
      by_contra hnot
      have hisZero : f.isZero := by
        cases hvalue : f.isZero <;> simp_all
      exact hzero ((PolyQuot.poly_isZero_iff f rep h).1 hisZero)
    have hdegreeEq : (PolyQuot.toPolynomialAt f rep h).natDegree =
        f.degree?.getD 0 :=
      PolyQuot.natDegree_toPolynomialAt f rep h hf
    by_cases hdegree : f.degree?.getD 0 = 0
    · have heq := roots?_eq_roots f rep h
      have hfFalse : f.isZero = false := by
        cases hvalue : f.isZero <;> simp_all
      rw [PolyQuot.roots?, ite_eq_right (by simpa using hfFalse),
        ite_eq_left hdegree] at heq
      have hroots : PolyQuot.roots f rep h = .finite #[] :=
        (Option.some.inj heq).symm
      constructor
      · simp [hroots, RootSet.Contains]
      · intro hroot
        have hnatDegree :
            (PolyQuot.toPolynomialAt f rep h).natDegree = 0 := by
          rw [hdegreeEq, hdegree]
        have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hnatDegree
        rw [hconstant] at hroot
        simp only [Polynomial.eval_C] at hroot
        exfalso
        apply hzero
        rw [hconstant, hroot, Polynomial.C_0]
    · have hdegreePos : 0 < f.degree?.getD 0 := Nat.pos_of_ne_zero hdegree
      have heq := roots?_eq_roots f rep h
      have hfFalse : f.isZero = false := by
        cases hvalue : f.isZero <;> simp_all
      rw [PolyQuot.roots?, ite_eq_right (by simpa using hfFalse),
        ite_eq_right hdegree] at heq
      cases hfold : (Roots.yun f).foldlM
          (fun out component =>
            if hm : 0 < component.2 then do
              let found ← Roots.componentRoots? component.1 component.2 hm rep h
              found.foldlM Roots.mergeRoot out
            else
              none)
          #[] with
      | none =>
          rw [hfold] at heq
          simp at heq
      | some raw =>
          rw [hfold] at heq
          have hroots : PolyQuot.roots f rep h =
              .finite (raw.mergeSort Roots.rootLe) :=
            (Option.some.inj heq).symm
          have hraw :
              (∃ entry ∈ raw.toList, entry.root.toComplex = z) ↔
                ∃ component ∈ (Roots.yun f).toList,
                  Polynomial.eval z
                    (PolyQuot.toPolynomialAt component.1 rep h) = 0 := by
            have hfoldList : (Roots.yun f).toList.foldlM
                (fun out component =>
                  if hm : 0 < component.2 then do
                    let found ← Roots.componentRoots? component.1 component.2
                      hm rep h
                    found.foldlM Roots.mergeRoot out
                  else
                    none)
                #[] = some raw := by
              simpa using hfold
            simpa using Roots.componentFold_contains rep h
              (Roots.yun f).toList
              (fun component hcomponent =>
                Roots.yun_positive f component hcomponent)
              #[] raw hfoldList z
          have hcomponents :
              (∃ component ∈ (Roots.yun f).toList,
                Polynomial.eval z
                  (PolyQuot.toPolynomialAt component.1 rep h) = 0) ↔
                Polynomial.eval z (PolyQuot.toPolynomialAt f rep h) = 0 := by
            let embedding := PolyQuot.embedding rep h
            have hmap (g : DensePoly (PolyQuot p x)) :
                Roots.toPolynomialMap embedding g =
                  PolyQuot.toPolynomialAt g rep h := by
              rw [Roots.toPolynomialMap_eq_map]
              exact (PolyQuot.toPolynomialAt_eq_map g rep h).symm
            have hfMap : Roots.toPolynomialMap embedding f ≠ 0 := by
              rw [hmap]
              exact hzero
            constructor
            · rintro ⟨component, hcomponent, hcomponentRoot⟩
              have hrootMap :
                  (Roots.toPolynomialMap embedding component.1).IsRoot z := by
                rw [hmap]
                exact hcomponentRoot
              have hm := Roots.yun_sound embedding f hfMap hdegreePos z
                component hcomponent hrootMap
              have hpositive := (Roots.yun_positive f component hcomponent).2
              have hmultPositive : 0 <
                  (Roots.toPolynomialMap embedding f).rootMultiplicity z := by
                rwa [← hm]
              have hinputRoot :=
                (Polynomial.rootMultiplicity_pos hfMap).mp hmultPositive
              rw [hmap] at hinputRoot
              exact hinputRoot
            · intro hinputRoot
              have hinputMap :
                  (Roots.toPolynomialMap embedding f).IsRoot z := by
                rw [hmap]
                exact hinputRoot
              obtain ⟨component, hcomponent, hcomponentRoot, _hm⟩ :=
                Roots.yun_complete embedding f hfMap hdegreePos z hinputMap
              refine ⟨component, hcomponent, ?_⟩
              rw [← hmap]
              exact hcomponentRoot
          rw [hroots, RootSet.Contains]
          constructor
          · rintro ⟨entry, hentry, hvalue⟩
            apply hcomponents.mp
            apply hraw.mp
            refine ⟨entry, ?_, hvalue⟩
            have hentrySorted : entry ∈ raw.mergeSort Roots.rootLe := by
              simpa using hentry
            have hentryArray : entry ∈ raw :=
              (Array.mem_mergeSort (le := Roots.rootLe)).mp hentrySorted
            simpa using hentryArray
          · intro hinputRoot
            obtain ⟨entry, hentry, hvalue⟩ :=
              hraw.mpr (hcomponents.mpr hinputRoot)
            refine ⟨entry, ?_, hvalue⟩
            have hentryArray : entry ∈ raw := by
              simpa using hentry
            simpa using
              ((Array.mem_mergeSort (le := Roots.rootLe)).mpr hentryArray)

/-- Fixed-field root multiplicities agree with Mathlib multiplicities. -/
theorem multiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) :
    (PolyQuot.roots f rep h).multiplicityOf z =
      Polynomial.rootMultiplicity z (PolyQuot.toPolynomialAt f rep h) := by
  classical
  let polynomial := PolyQuot.toPolynomialAt f rep h
  by_cases hzero : polynomial = 0
  · have hall : PolyQuot.roots f rep h = .all :=
      (roots_all_iff f rep h).2 hzero
    rw [hall]
    change RootSet.all.multiplicityOf z =
      Polynomial.rootMultiplicity z polynomial
    rw [hzero]
    simp [RootSet.multiplicityOf]
  · have hfinite : ∃ entries,
        PolyQuot.roots f rep h = .finite entries := by
      cases hroots : PolyQuot.roots f rep h with
      | all =>
          exact (hzero ((roots_all_iff f rep h).1 hroots)).elim
      | finite entries => exact ⟨entries, rfl⟩
    obtain ⟨entries, hroots⟩ := hfinite
    rw [hroots, RootSet.multiplicityOf]
    apply findMultiplicity_eq entries.toList z
        (Polynomial.rootMultiplicity z polynomial)
    · intro entry hentry hvalue
      have hf : !f.isZero := by
        by_contra hnot
        have hisZero : f.isZero := by
          cases hvalueZero : f.isZero <;> simp_all
        exact hzero ((PolyQuot.poly_isZero_iff f rep h).1 hisZero)
      have hdegreeEq : polynomial.natDegree = f.degree?.getD 0 :=
        PolyQuot.natDegree_toPolynomialAt f rep h hf
      by_cases hdegree : f.degree?.getD 0 = 0
      · have hcontains : RootSet.Contains (PolyQuot.roots f rep h) z := by
          rw [hroots, RootSet.Contains]
          exact ⟨entry, hentry, hvalue⟩
        have hroot := (contains_roots_iff f rep h z).mp hcontains
        have hrootPoly : Polynomial.eval z polynomial = 0 := hroot
        have hnatDegree : polynomial.natDegree = 0 := by
          rw [hdegreeEq, hdegree]
        have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hnatDegree
        rw [hconstant] at hrootPoly
        simp only [Polynomial.eval_C] at hrootPoly
        exact (hzero (by rw [hconstant, hrootPoly, Polynomial.C_0])).elim
      · have hdegreePos : 0 < f.degree?.getD 0 :=
          Nat.pos_of_ne_zero hdegree
        have heq := roots?_eq_roots f rep h
        have hfFalse : f.isZero = false := by
          cases hvalueZero : f.isZero <;> simp_all
        rw [PolyQuot.roots?, ite_eq_right (by simpa using hfFalse),
          ite_eq_right hdegree] at heq
        cases hfold : (Roots.yun f).foldlM
            (fun out component =>
              if hm : 0 < component.2 then do
                let found ← Roots.componentRoots? component.1 component.2 hm rep h
                found.foldlM Roots.mergeRoot out
              else
                none)
            #[] with
        | none =>
            rw [hfold] at heq
            simp at heq
        | some raw =>
            rw [hfold, hroots] at heq
            have hentries : entries = raw.mergeSort Roots.rootLe := by
              simpa using heq.symm
            subst entries
            have hentrySorted : entry ∈ raw.mergeSort Roots.rootLe := by
              simpa using hentry
            have hentryRaw : entry ∈ raw :=
              (Array.mem_mergeSort (le := Roots.rootLe)).mp hentrySorted
            have hfoldList : (Roots.yun f).toList.foldlM
                (fun out component =>
                  if hm : 0 < component.2 then do
                    let found ← Roots.componentRoots? component.1 component.2
                      hm rep h
                    found.foldlM Roots.mergeRoot out
                  else
                    none)
                #[] = some raw := by
              simpa using hfold
            apply Roots.componentFold_value f rep h hzero hdegreePos
              #[] raw hfoldList z (by simp) entry (by simpa using hentryRaw)
            exact hvalue
    · have hsemantics := contains_roots_iff f rep h z
      rw [hroots, RootSet.Contains] at hsemantics
      have hpositive : 0 < Polynomial.rootMultiplicity z polynomial ↔
          Polynomial.eval z polynomial = 0 := by
        simpa [polynomial] using
          (Polynomial.rootMultiplicity_pos hzero)
      exact hsemantics.trans hpositive.symm

/-- The fixed-field driver produces positive multiplicities. -/
theorem roots_positive [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Positive (PolyQuot.roots f rep h) := by
  cases hroots : PolyQuot.roots f rep h with
  | all => trivial
  | finite roots =>
      intro entry _hentry
      exact entry.multiplicity_pos

/-- The fixed-field driver merges all semantic duplicates. -/
theorem roots_noDuplicates [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.NoDuplicates (PolyQuot.roots f rep h) := by
  have heq := roots?_eq_roots f rep h
  rw [PolyQuot.roots?] at heq
  split at heq
  next _ =>
    have hroots : PolyQuot.roots f rep h = .all :=
      (Option.some.inj heq).symm
    rw [hroots]
    trivial
  next _ =>
    split at heq
    next _ =>
      have hroots : PolyQuot.roots f rep h = .finite #[] :=
        (Option.some.inj heq).symm
      rw [hroots]
      simp [RootSet.NoDuplicates]
    next _ =>
      cases hfold : (Roots.yun f).foldlM
          (fun out component =>
            if hm : 0 < component.2 then do
              let found ← Roots.componentRoots? component.1 component.2 hm rep h
              found.foldlM Roots.mergeRoot out
            else
              none)
          #[] with
      | none =>
          rw [hfold] at heq
          simp at heq
      | some raw =>
          rw [hfold] at heq
          have hroots : PolyQuot.roots f rep h =
              .finite (raw.mergeSort Roots.rootLe) :=
            (Option.some.inj heq).symm
          rw [hroots]
          have hfoldList : (Roots.yun f).toList.foldlM
              (fun out component =>
                if hm : 0 < component.2 then do
                  let found ← Roots.componentRoots? component.1 component.2
                    hm rep h
                  found.foldlM Roots.mergeRoot out
                else
                  none)
              #[] = some raw := by
            simpa using hfold
          have hraw : raw.toList.Pairwise fun a b =>
              a.root.toComplex ≠ b.root.toComplex :=
            Roots.componentFold_nodup rep h (Roots.yun f).toList
              (fun component hcomponent =>
                Roots.yun_positive f component hcomponent)
              #[] raw hfoldList (by simp)
          rw [RootSet.NoDuplicates, Array.toList_mergeSort]
          exact ((List.mergeSort_perm raw.toList Roots.rootLe).pairwise_iff
            (fun hne => hne.symm)).mpr hraw

/-- The fixed-field driver uses its deterministic canonical root order. -/
theorem roots_ordered [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    RootSet.Ordered (PolyQuot.roots f rep h) := by
  have heq := roots?_eq_roots f rep h
  rw [PolyQuot.roots?] at heq
  split at heq
  next _ =>
    have hroots : PolyQuot.roots f rep h = .all :=
      (Option.some.inj heq).symm
    rw [hroots]
    trivial
  next _ =>
    split at heq
    next _ =>
      have hroots : PolyQuot.roots f rep h = .finite #[] :=
        (Option.some.inj heq).symm
      rw [hroots]
      simp [RootSet.Ordered]
    next _ =>
      cases hfold : (Roots.yun f).foldlM
          (fun out component =>
            if hm : 0 < component.2 then do
              let found ← Roots.componentRoots? component.1 component.2 hm rep h
              found.foldlM Roots.mergeRoot out
            else
              none)
          #[] with
      | none =>
          rw [hfold] at heq
          simp at heq
      | some raw =>
          rw [hfold] at heq
          have hroots : PolyQuot.roots f rep h =
              .finite (raw.mergeSort Roots.rootLe) :=
            (Option.some.inj heq).symm
          rw [hroots, RootSet.Ordered]
          exact Array.pairwise_mergeSort Roots.rootLe_trans Roots.rootLe_total

/-- For a nonzero fixed-field polynomial, the output multiplicities sum to
its degree. -/
theorem totalMultiplicity_roots [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x)
    (hf : PolyQuot.toPolynomialAt f rep h ≠ 0) :
    (PolyQuot.roots f rep h).totalMultiplicity =
      (PolyQuot.toPolynomialAt f rep h).natDegree := by
  classical
  let polynomial := PolyQuot.toPolynomialAt f rep h
  have hfinite : ∃ entries,
      PolyQuot.roots f rep h = .finite entries := by
    cases hroots : PolyQuot.roots f rep h with
    | all => exact (hf ((roots_all_iff f rep h).1 hroots)).elim
    | finite entries => exact ⟨entries, rfl⟩
  obtain ⟨entries, hroots⟩ := hfinite
  have hnodup : entries.toList.Pairwise fun a b =>
      a.root.toComplex ≠ b.root.toComplex := by
    have hresult := roots_noDuplicates f rep h
    rw [hroots, RootSet.NoDuplicates] at hresult
    exact hresult
  have hentryMultiplicity : ∀ entry ∈ entries.toList,
      Polynomial.rootMultiplicity entry.root.toComplex polynomial =
        entry.multiplicity := by
    intro entry hentry
    have hlookup : (RootSet.finite entries).multiplicityOf
        entry.root.toComplex = entry.multiplicity := by
      unfold RootSet.multiplicityOf
      exact findMultiplicity_mem entries.toList hnodup entry hentry
    rw [← hlookup, ← hroots]
    exact (multiplicity_roots f rep h entry.root.toComplex).symm
  have hsum :
      (entries.toList.map fun entry => entry.multiplicity).sum =
        ∑ z ∈ (entries.toList.map fun entry =>
          entry.root.toComplex).toFinset,
          Polynomial.rootMultiplicity z polynomial :=
    sum_eq_valueSum entries.toList hnodup
      (fun z => Polynomial.rootMultiplicity z polynomial)
      hentryMultiplicity
  have hvalues :
      (entries.toList.map fun entry => entry.root.toComplex).toFinset =
        polynomial.roots.toFinset := by
    ext z
    simp only [List.mem_toFinset, List.mem_map, Multiset.mem_toFinset]
    constructor
    · rintro ⟨entry, hentry, rfl⟩
      apply (Polynomial.mem_roots hf).2
      have hcontains : RootSet.Contains (PolyQuot.roots f rep h)
          entry.root.toComplex := by
        rw [hroots, RootSet.Contains]
        exact ⟨entry, hentry, rfl⟩
      exact (contains_roots_iff f rep h entry.root.toComplex).mp hcontains
    · intro hroot
      have heval := (Polynomial.mem_roots hf).1 hroot
      have hcontains := (contains_roots_iff f rep h z).mpr heval
      rw [hroots, RootSet.Contains] at hcontains
      exact hcontains
  have hcount :
      (∑ z ∈ polynomial.roots.toFinset,
        Polynomial.rootMultiplicity z polynomial) = polynomial.roots.card := by
    simpa only [Polynomial.count_roots] using
      (Multiset.toFinset_sum_count_eq polynomial.roots)
  rw [hroots, RootSet.totalMultiplicity, ← Array.foldl_toList,
    foldlMultiplicity_eq_sum entries.toList, hsum, hvalues, hcount]
  exact IsAlgClosed.card_roots_eq_natDegree

end Hex.PolyQuot
