/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Exact

public section

/-!
# Semantics of lazy and canonical arithmetic

Each checked lazy operation has a soundness theorem and a bounded-search
completeness theorem. These imply the corresponding theorem for the total
fallback wrapper, and exactification transfers it to canonical algebraic
numbers.
-/

namespace Hex

noncomputable section

section

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

local instance : IsDomain ZPoly :=
  MulEquiv.isDomain (Polynomial Int)
    (HexPolyMathlib.equiv (R := Int)).toMulEquiv

private noncomputable def evalZPoly (t : ℂ) : ZPoly →+* ℂ :=
  (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
    (HexPolyMathlib.equiv (R := Int)).toRingHom

private theorem ZPoly.map_liftOuter (p : ZPoly) (t : ℂ) :
    (HexPolyMathlib.toPolynomial p.liftOuter).map (evalZPoly t) =
      HexRootsMathlib.toPolyℂ p := by
  ext n
  rw [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial,
    ZPoly.coeff_liftOuter, HexRootsMathlib.coeff_toPolyℂ]
  change Polynomial.eval₂ (Int.castRingHom ℂ) t
      (HexPolyMathlib.toPolynomial (DensePoly.C (p.coeff n))) =
    (p.coeff n : ℂ)
  rw [HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
  rfl

private theorem ZPoly.natDegree_liftOuter (p : ZPoly) :
    (HexPolyMathlib.toPolynomial p.liftOuter).natDegree =
      p.degree?.getD 0 := by
  rw [HexPolyMathlib.natDegree_toPolynomial]
  by_cases hp : p.size = 0
  · have hlift : p.liftOuter.size = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold ZPoly.liftOuter
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp [hp])
    rw [(DensePoly.degree?_eq_none_iff p.liftOuter).2 hlift,
      (DensePoly.degree?_eq_none_iff p).2 hp]
  · have hppos : 0 < p.size := Nat.pos_of_ne_zero hp
    have hliftLe : p.liftOuter.size ≤ p.size := by
      unfold ZPoly.liftOuter
      exact (DensePoly.size_ofCoeffs_le _).trans (by simp)
    have hcoeff : p.liftOuter.coeff (p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun q : ZPoly => q.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size p hppos hconst
    have hliftGe : p.size ≤ p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    have hsize : p.liftOuter.size = p.size := Nat.le_antisymm hliftLe hliftGe
    rw [DensePoly.degree?_eq_some_of_pos_size p hppos,
      DensePoly.degree?_eq_some_of_pos_size p.liftOuter (by omega),
      Option.getD_some, Option.getD_some, hsize]

private theorem evalZPoly_X (t : ℂ) : evalZPoly t ZPoly.X = t := by
  simp [evalZPoly, ZPoly.X, HexPolyMathlib.equiv_apply,
    HexPolyMathlib.toPolynomial_monomial,
    Polynomial.monomial_one_one_eq_X]

private theorem resultant_eval_eq_zero_of_common_root
    (f g : DensePoly ZPoly) (t y : ℂ)
    (hpos : 1 < f.size ∨ 1 < g.size)
    (hf : ((HexPolyMathlib.toPolynomial f).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0)
    (hg : ((HexPolyMathlib.toPolynomial g).map
      ((Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
        (HexPolyMathlib.equiv (R := Int)).toRingHom)).eval y = 0) :
    (HexRootsMathlib.toPolyℂ (DensePoly.resultant f g)).eval t = 0 := by
  let ε : ZPoly →+* ℂ :=
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ) t).comp
      (HexPolyMathlib.equiv (R := Int)).toRingHom
  let F : Polynomial ℂ := (HexPolyMathlib.toPolynomial f).map ε
  let G : Polynomial ℂ := (HexPolyMathlib.toPolynomial g).map ε
  let m := f.degree?.getD 0
  let n := g.degree?.getD 0
  have hm : F.natDegree ≤ m := by
    calc
      F.natDegree ≤ (HexPolyMathlib.toPolynomial f).natDegree :=
        Polynomial.natDegree_map_le
      _ = m := by
        simp [m]
  have hn : G.natDegree ≤ n := by
    calc
      G.natDegree ≤ (HexPolyMathlib.toPolynomial g).natDegree :=
        Polynomial.natDegree_map_le
      _ = n := by
        simp [n]
  have hmn : 0 < m ∨ 0 < n := by
    rcases hpos with hfpos | hgpos
    · left
      dsimp only [m]
      rw [DensePoly.degree?_eq_some_of_pos_size f (by omega), Option.getD_some]
      omega
    · right
      dsimp only [n]
      rw [DensePoly.degree?_eq_some_of_pos_size g (by omega), Option.getD_some]
      omega
  have hresultant : Polynomial.resultant F G m n = 0 := by
    by_cases hboth : F = 0 ∧ G = 0
    · rcases hboth with ⟨hFzero, hGzero⟩
      rw [hFzero, hGzero, Polynomial.resultant_zero_zero]
      exact zero_pow (by omega)
    · have hne : F ≠ 0 ∨ G ≠ 0 := by
        by_cases hFzero : F = 0
        · right
          intro hGzero
          exact hboth ⟨hFzero, hGzero⟩
        · exact Or.inl hFzero
      have hdefault : Polynomial.resultant F G = 0 :=
        DensePoly.resultant_eq_zero_of_common_eval F G y
          (by simpa [F, ε] using hf) (by simpa [G, ε] using hg) hne
      have hmEq : m = F.natDegree + (m - F.natDegree) := by omega
      have hnEq : n = G.natDegree + (n - G.natDegree) := by omega
      rw [hmEq, Polynomial.resultant_add_left_deg F G F.natDegree n
        (m - F.natDegree) le_rfl]
      rw [hnEq, Polynomial.resultant_add_right_deg F G F.natDegree
        G.natDegree (n - G.natDegree) le_rfl]
      rw [hdefault]
      ring
  have hcorrespondence := congrArg ε
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have heval (q : ZPoly) :
      ε q = (HexRootsMathlib.toPolyℂ q).eval t := by
    simp [ε, HexRootsMathlib.toPolyℂ, Polynomial.eval_map]
  rw [← heval]
  rw [hcorrespondence]
  exact hresultant

private theorem ZPoly.addEliminant_ne_zero (a b : AlgebraicRoot) :
    ZPoly.addEliminant a.p b.p ≠ 0 := by
  let P := HexRootsMathlib.toPolyℂ a.p
  let Q := HexRootsMathlib.toPolyℂ b.p
  have haPoly : a.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
  have hbPoly : b.p ≠ 0 :=
    HexRootsMathlib.RefinedIsolation.poly_ne_zero b.rep
  have hPne : P ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero a.p fun hsize =>
      haPoly ((DensePoly.size_eq_zero_iff a.p).mp hsize)
  have hQne : Q ≠ 0 := by
    exact HexRootsMathlib.toPolyℂ_ne_zero b.p fun hsize =>
      hbPoly ((DensePoly.size_eq_zero_iff b.p).mp hsize)
  let sums : Set ℂ :=
    (fun xy : ℂ × ℂ => xy.1 + xy.2) ''
      (P.rootSet ℂ ×ˢ Q.rootSet ℂ)
  have hsums : sums.Finite := by
    exact ((Polynomial.rootSet_finite P ℂ).prod
      (Polynomial.rootSet_finite Q ℂ)).image _
  obtain ⟨t, ht⟩ := hsums.exists_notMem
  let G := Q.comp (Polynomial.C t - Polynomial.X)
  have hcoprime : IsCoprime P G := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℂ) ℂ P G).2
    intro y
    by_contra hboth
    push Not at hboth
    apply ht
    refine ⟨(y, t - y), ⟨?_, ?_⟩, by simp⟩
    · exact (Polynomial.mem_rootSet_of_ne hPne).2 (by
        simpa [Polynomial.aeval_def] using hboth.1)
    · apply (Polynomial.mem_rootSet_of_ne hQne).2
      simpa [G, Polynomial.aeval_def, Polynomial.eval_comp] using hboth.2
  have hresultant : Polynomial.resultant P G ≠ 0 :=
    Polynomial.resultant_ne_zero P G hcoprime
  let y : DensePoly ZPoly := DensePoly.monomial 1 1
  let x : DensePoly ZPoly := DensePoly.C ZPoly.X
  let f : DensePoly ZPoly := a.p.liftOuter
  let g : DensePoly ZPoly := DensePoly.compose b.p.liftOuter (x - y)
  have hfmap :
      (HexPolyMathlib.toPolynomial f).map (evalZPoly t) = P := by
    simpa [f, P] using ZPoly.map_liftOuter a.p t
  have hgmap :
      (HexPolyMathlib.toPolynomial g).map (evalZPoly t) = G := by
    dsimp only [g, G, x, y]
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp,
      ZPoly.map_liftOuter]
    simp [Q, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, evalZPoly_X]
  have hfnat :
      (HexPolyMathlib.toPolynomial f).natDegree = P.natDegree := by
    calc
      (HexPolyMathlib.toPolynomial f).natDegree =
          a.p.degree?.getD 0 := by
        simpa [f] using ZPoly.natDegree_liftOuter a.p
      _ = P.natDegree := by
        simp [P]
  have hinnerNat :
      (HexPolyMathlib.toPolynomial (x - y)).natDegree = 1 := by
    dsimp only [x, y]
    rw [HexPolyMathlib.toPolynomial_sub,
      HexPolyMathlib.toPolynomial_C,
      HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X,
      show Polynomial.C ZPoly.X - Polynomial.X =
          -(Polynomial.X - Polynomial.C ZPoly.X) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hcomplexInnerNat :
      (Polynomial.C t - Polynomial.X).natDegree = 1 := by
    rw [show Polynomial.C t - Polynomial.X =
        -(Polynomial.X - Polynomial.C t) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hgnat :
      (HexPolyMathlib.toPolynomial g).natDegree = G.natDegree := by
    rw [show HexPolyMathlib.toPolynomial g =
        (HexPolyMathlib.toPolynomial b.p.liftOuter).comp
          (HexPolyMathlib.toPolynomial (x - y)) by
        simp [g]]
    rw [Polynomial.natDegree_comp, hinnerNat, mul_one,
      ZPoly.natDegree_liftOuter]
    rw [show G.natDegree = Q.natDegree *
        (Polynomial.C t - Polynomial.X).natDegree by
      exact Polynomial.natDegree_comp]
    rw [hcomplexInnerNat, mul_one]
    simp [Q]
  intro hzero
  have hcorrespondence := congrArg (evalZPoly t)
    (DensePoly.toPolynomial_resultant f g)
  rw [← Polynomial.resultant_map_map] at hcorrespondence
  have hraw : DensePoly.resultant f g = 0 := by
    simpa [ZPoly.addEliminant, f, g, x, y] using hzero
  rw [hraw, map_zero, hfmap, hgmap] at hcorrespondence
  apply hresultant
  simpa [← hfnat, ← hgnat] using hcorrespondence.symm

private theorem ZPoly.addEliminant_isRoot (a b : AlgebraicRoot) :
    (HexRootsMathlib.toPolyℂ (ZPoly.addEliminant a.p b.p)).IsRoot
      (a.toComplex + b.toComplex) := by
  unfold ZPoly.addEliminant
  apply resultant_eval_eq_zero_of_common_root
      (y := a.toComplex)
  · left
    have hsize : 1 < a.p.size := by
      have hpos : 0 < a.p.size := by
        by_contra h
        have hzero : a.p = 0 :=
          (DensePoly.size_eq_zero_iff a.p).mp (by omega)
        have hdegree := a.pos_degree
        rw [hzero] at hdegree
        simp at hdegree
      have hdegree := a.pos_degree
      rw [DensePoly.degree?_eq_some_of_pos_size a.p hpos,
        Option.getD_some] at hdegree
      omega
    have hcoeff :
        a.p.liftOuter.coeff (a.p.size - 1) ≠ 0 := by
      rw [ZPoly.coeff_liftOuter]
      intro hzero
      have hconst := congrArg (fun p : ZPoly => p.coeff 0) hzero
      simp at hconst
      exact DensePoly.coeff_last_ne_zero_of_pos_size a.p (by omega) hconst
    have hlt : a.p.size - 1 < a.p.liftOuter.size := by
      by_contra h
      exact hcoeff (DensePoly.coeff_eq_zero_of_size_le _ (by omega))
    omega
  · change ((HexPolyMathlib.toPolynomial a.p.liftOuter).map
      (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex = 0
    rw [ZPoly.map_liftOuter]
    exact AlgebraicRoot.toComplex_isRoot a
  · change (((HexPolyMathlib.toPolynomial
      (DensePoly.compose b.p.liftOuter
        (DensePoly.C ZPoly.X - DensePoly.monomial 1 1))).map
          (evalZPoly (a.toComplex + b.toComplex))).eval a.toComplex) = 0
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp,
      ZPoly.map_liftOuter]
    simp [HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X, evalZPoly_X,
      Polynomial.eval_comp, AlgebraicRoot.toComplex_isRoot]

end


/-- A successful eliminant search selects the supplied semantic root whenever
the operation ball contains it. -/
private theorem AlgebraicRoot.ofEliminant?_sound
    (raw : ZPoly) (ballAt : Int → Option DyadicComplexBall)
    {c : AlgebraicRoot} {z : ℂ}
    (h : AlgebraicRoot.ofEliminant? raw ballAt = some c)
    (hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot z)
    (hball : ∀ (ball : DyadicComplexBall),
      ballAt (separationDepth (ZPoly.squareFreeCore raw)) = some ball →
        z ∈ ball.set) :
    c.toComplex = z := by
  unfold AlgebraicRoot.ofEliminant? at h
  dsimp only at h
  split at h
  · rename_i hprim
    split at h
    · rename_i hpos
      split at h
      · rename_i hdegree
        split at h
        · rename_i hsimple
          obtain ⟨ball, hballAt, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨isolations, hisolate, h⟩ :=
            Option.bind_eq_some_iff.mp h
          obtain ⟨refined, hrefined, h⟩ :=
            Option.bind_eq_some_iff.mp h
          cases hselected : refined.toList.filter fun r =>
              r.1.square.meetsBall ball with
          | nil => simp [hselected] at h
          | cons matching rest =>
              cases rest with
              | cons second rest => simp [hselected] at h
              | nil =>
                  rw [hselected] at h
                  have hc := Option.some.inj h
                  subst c
                  let p := ZPoly.squareFreeCore raw
                  have hpne : p ≠ 0 := by
                    intro hp
                    have hdegree' := hdegree
                    change ZPoly.squareFreeCore raw = 0 at hp
                    rw [hp] at hdegree'
                    simp at hdegree'
                  have hrawne : raw ≠ 0 := by
                    intro hraw
                    apply hpne
                    subst raw
                    rfl
                  have hpRoot : (HexRootsMathlib.toPolyℂ p).IsRoot z := by
                    simpa [p] using
                      HexPolyZMathlib.isRoot_squareFreeCore hrawne hroot
                  obtain ⟨iso, hiso, hisoRoot⟩ :=
                    HexRootsMathlib.isolate_root_mem_of_pos p hsimple
                      (separationDepth p : Int) .nkThenPellet hdegree
                      hisolate hpRoot
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
                    change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 = z
                    rw [hrawIso, harrIso]
                    exact hisoRoot
                  have hzCandidate :
                      z ∈ refined[i].1.square.toBall.set := by
                    rw [← hrefinedRoot]
                    exact DyadicComplexBall.mem_toBall
                      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc
                        refined[i])
                  have hzBall : z ∈ ball.set := by
                    exact hball ball (by simpa [p] using hballAt)
                  have hmeet :
                      refined[i].1.square.meetsBall ball = true := by
                    simpa [DyadicSquare.meetsBall] using
                      DyadicComplexBall.meets_of_mem hzCandidate hzBall
                  have hmem : refined[i] ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball := by
                    simp [hmeet]
                  rw [hselected] at hmem
                  have heq : refined[i] = matching := by simpa using hmem
                  change matching.root = z
                  rw [← heq]
                  exact hrefinedRoot
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A nonzero eliminant root enclosed by a sufficiently small operation ball
survives normalization, isolation, and the singleton selection filter. -/
private theorem AlgebraicRoot.ofEliminant?_isSome
    (raw : ZPoly) (ballAt : Int → Option DyadicComplexBall)
    {z : ℂ} (hraw : raw ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ raw).IsRoot z)
    (ball : DyadicComplexBall)
    (hballAt : ballAt (separationDepth (ZPoly.squareFreeCore raw)) =
      some ball)
    (hzball : z ∈ ball.set)
    (hballRadius : ball.realRadius ≤
      (2 : ℝ) ^ (-(mahlerPrec (ZPoly.squareFreeCore raw) : ℤ))) :
    (AlgebraicRoot.ofEliminant? raw ballAt).isSome := by
  have hpne : ZPoly.squareFreeCore raw ≠ 0 :=
    ZPoly.squareFreeCore_ne_zero raw hraw
  have hpRoot :
      (HexRootsMathlib.toPolyℂ (ZPoly.squareFreeCore raw)).IsRoot z := by
    exact HexPolyZMathlib.isRoot_squareFreeCore hraw hroot
  have hprim : ZPoly.content (ZPoly.squareFreeCore raw) = 1 := by
    simpa [ZPoly.Primitive] using ZPoly.squareFreeCore_primitive raw hraw
  have hpos : 0 < (ZPoly.squareFreeCore raw).leadingCoeff :=
    ZPoly.leadingCoeff_squareFreeCore_pos raw hraw
  have hsimple : HasOnlySimpleRoots (ZPoly.squareFreeCore raw) := by
    simpa [HasOnlySimpleRoots] using
      ZPoly.squareFreeRat_squareFreeCore raw hraw
  have hdegree : 0 < (ZPoly.squareFreeCore raw).degree?.getD 0 := by
    by_contra hn
    have hsize : (ZPoly.squareFreeCore raw).size ≠ 0 := by
      intro hsize
      exact hpne ((DensePoly.size_eq_zero_iff _).mp hsize)
    exact HexRootsMathlib.not_isRoot_of_degree_not_pos
      (ZPoly.squareFreeCore raw) hsize hn z hpRoot
  unfold AlgebraicRoot.ofEliminant?
  dsimp only
  rw [dif_pos hprim, dif_pos hpos, dif_pos hdegree, dif_pos hsimple]
  rw [hballAt]
  have hisolateSome := HexRootsMathlib.isolate_isSome
    (ZPoly.squareFreeCore raw) hsimple hpne
    (separationDepth (ZPoly.squareFreeCore raw) : Int) .nkThenPellet
  cases hisolate : isolate (ZPoly.squareFreeCore raw) hsimple
      (separationDepth (ZPoly.squareFreeCore raw) : Int) with
  | none => simp [hisolate] at hisolateSome
  | some isolations =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hmapSome := HexRootsMathlib.array_mapM_isSome
        (xs := isolations) (f := DyadicRootIsolation.toRefined?)
        (fun iso hiso => by
          simp [DyadicRootIsolation.toRefined?,
            HexRootsMathlib.isolate_refined (ZPoly.squareFreeCore raw) hsimple
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet hisolate iso hiso])
      cases hrefined : isolations.mapM DyadicRootIsolation.toRefined? with
      | none => simp [hrefined] at hmapSome
      | some refined =>
          simp only [Option.bind_some]
          obtain ⟨hmapSize, hmapGet⟩ :=
            HexRootsMathlib.array_mapM_some_get hrefined
          have hrefinedPairwise : refined.toList.Pairwise fun r s =>
              HexRootsMathlib.RefinedIsolation.root r ≠
                HexRootsMathlib.RefinedIsolation.root s := by
            rw [List.pairwise_iff_getElem]
            intro i j hi hj hij
            have hi' : i < isolations.size := by
              simpa [hmapSize] using hi
            have hj' : j < isolations.size := by
              simpa [hmapSize] using hj
            have htoI := hmapGet i hi' hi
            have htoJ := hmapGet j hj' hj
            have hrawI : refined[i].1 = isolations[i] := by
              rw [DyadicRootIsolation.toRefined?] at htoI
              split at htoI
              · exact (congrArg Subtype.val (Option.some.inj htoI)).symm
              · simp at htoI
            have hrawJ : refined[j].1 = isolations[j] := by
              rw [DyadicRootIsolation.toRefined?] at htoJ
              split at htoJ
              · exact (congrArg Subtype.val (Option.some.inj htoJ)).symm
              · simp at htoJ
            intro hroots
            apply HexRootsMathlib.isolate_roots_ne
              (ZPoly.squareFreeCore raw) hsimple
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet hisolate
              hi' hj' (Nat.ne_of_lt hij)
            change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 =
              HexRootsMathlib.DyadicRootIsolation.root refined[j].1 at hroots
            simpa [hrawI, hrawJ] using hroots
          obtain ⟨iso, hiso, hisoRoot⟩ :=
            HexRootsMathlib.isolate_root_mem_of_pos
              (ZPoly.squareFreeCore raw) hsimple
              (separationDepth (ZPoly.squareFreeCore raw) : Int)
              .nkThenPellet hdegree hisolate hpRoot
          obtain ⟨i, hiList, hidx⟩ := List.getElem_of_mem hiso
          have hi : i < isolations.size := by simpa using hiList
          have hj : i < refined.size := by simpa [← hmapSize] using hi
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
            change HexRootsMathlib.DyadicRootIsolation.root refined[i].1 = z
            rw [hrawIso, harrIso]
            exact hisoRoot
          have hzCandidate : z ∈ refined[i].1.square.toBall.set := by
            rw [← hrefinedRoot]
            exact DyadicComplexBall.mem_toBall
              (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc refined[i])
          have hmeet : refined[i].1.square.meetsBall ball = true := by
            simpa [DyadicSquare.meetsBall] using
              DyadicComplexBall.meets_of_mem hzCandidate hzball
          have hmem : refined[i] ∈ refined.toList.filter fun r =>
              r.1.square.meetsBall ball := by
            simp [hmeet]
          cases hselected : refined.toList.filter fun r =>
              r.1.square.meetsBall ball with
          | nil => simp [hselected] at hmem
          | cons matching rest =>
              cases rest with
              | nil => simp
              | cons second tail =>
                  have hfilteredPairwise := hrefinedPairwise.filter fun r =>
                    r.1.square.meetsBall ball
                  rw [hselected] at hfilteredPairwise
                  have hneRoots : matching.root ≠ second.root :=
                    List.rel_of_pairwise_cons hfilteredPairwise (by simp)
                  have hmatching := List.mem_filter.mp (show matching ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball by simp [hselected])
                  have hsecond := List.mem_filter.mp (show second ∈
                      refined.toList.filter fun r =>
                        r.1.square.meetsBall ball by simp [hselected])
                  have hmatchingRoot : matching.root = z :=
                    QAdjoin.root_eq_of_meetsBall hpne matching hpRoot
                      hzball hballRadius hmatching.2
                  have hsecondRoot : second.root = z :=
                    QAdjoin.root_eq_of_meetsBall hpne second hpRoot
                      hzball hballRadius hsecond.2
                  exact (hneRoots (hmatchingRoot.trans hsecondRoot.symm)).elim

private theorem ZPoly.negRoots_isRoot_of_isRoot {p : ZPoly} {z : ℂ}
    (hp : p ≠ 0) (hz : (HexRootsMathlib.toPolyℂ p).IsRoot z) :
    (HexRootsMathlib.toPolyℂ p.negRoots).IsRoot (-z) := by
  let reflected : ZPoly := DensePoly.compose p (-ZPoly.X)
  have hreflected :
      HexRootsMathlib.toPolyℂ reflected =
        (HexRootsMathlib.toPolyℂ p).comp (-Polynomial.X) := by
    change
      (HexPolyMathlib.toPolynomial reflected).map (Int.castRingHom ℂ) =
        ((HexPolyMathlib.toPolynomial p).map (Int.castRingHom ℂ)).comp
          (-Polynomial.X)
    dsimp only [reflected]
    rw [HexPolyMathlib.toPolynomial_compose, Polynomial.map_comp]
    simp [ZPoly.X, HexPolyMathlib.toPolynomial_monomial,
      Polynomial.monomial_one_one_eq_X]
  have hreflectedRoot :
      (HexRootsMathlib.toPolyℂ reflected).eval (-z) = 0 := by
    rw [hreflected, Polynomial.eval_comp]
    simpa [Polynomial.IsRoot] using hz
  have hpSize : p.size ≠ 0 := by
    intro hsize
    exact hp ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hpComplex : HexRootsMathlib.toPolyℂ p ≠ 0 :=
    HexRootsMathlib.toPolyℂ_ne_zero p hpSize
  have hreflectedComplex : HexRootsMathlib.toPolyℂ reflected ≠ 0 := by
    rw [hreflected]
    intro hzero
    have hdegree := congrArg Polynomial.degree hzero
    rw [Polynomial.degree_comp_neg_X, Polynomial.degree_zero] at hdegree
    exact hpComplex (Polynomial.degree_eq_bot.mp hdegree)
  have hreflectedNe : reflected ≠ 0 := by
    intro hzero
    apply hreflectedComplex
    rw [hzero]
    simp [HexRootsMathlib.toPolyℂ]
  have hcontent : ZPoly.content reflected ≠ 0 :=
    HexPolyZMathlib.content_ne_zero reflected hreflectedNe
  have hdecomp :
      HexRootsMathlib.toPolyℂ reflected =
        Polynomial.C (ZPoly.content reflected : ℂ) *
          HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected) := by
    simpa [HexRootsMathlib.toPolyℂ] using congrArg
      (fun q : Polynomial ℤ => q.map (Int.castRingHom ℂ))
      (HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart reflected)
  have hprimitiveRoot :
      (HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected)).eval (-z) = 0 := by
    have hproduct :
        (ZPoly.content reflected : ℂ) *
          (HexRootsMathlib.toPolyℂ (ZPoly.primitivePart reflected)).eval (-z) = 0 := by
      rw [← Polynomial.eval_C_mul, ← hdecomp]
      exact hreflectedRoot
    exact (mul_eq_zero.mp hproduct).resolve_left (by exact_mod_cast hcontent)
  unfold ZPoly.negRoots ZPoly.normalizePrimitiveSign
  change (HexRootsMathlib.toPolyℂ
    (if (ZPoly.primitivePart reflected).leadingCoeff < 0 then
      DensePoly.scale (-1) (ZPoly.primitivePart reflected)
    else ZPoly.primitivePart reflected)).IsRoot (-z)
  split
  · simpa [Polynomial.IsRoot, HexRootsMathlib.toPolyℂ,
      HexPolyMathlib.toPolynomial_scale] using hprimitiveRoot
  · exact hprimitiveRoot

private theorem DyadicSquare.neg_mem_closedDisc {s : DyadicSquare} {z : ℂ}
    (hz : z ∈ HexRootsMathlib.DyadicSquare.closedDisc s) :
    -z ∈ HexRootsMathlib.DyadicSquare.closedDisc s.neg := by
  have hcenter : HexRootsMathlib.DyadicSquare.center s.neg =
      -HexRootsMathlib.DyadicSquare.center s := by
    apply Complex.ext <;>
      simp [DyadicSquare.neg, HexRootsMathlib.DyadicSquare.center,
        Hex.DyadicSquare.center, HexRootsMathlib.GaussDyadic.toComplex]
  have hradius : HexRootsMathlib.DyadicSquare.radius s.neg =
      HexRootsMathlib.DyadicSquare.radius s := by
    simp [HexRootsMathlib.DyadicSquare.radius_eq, DyadicSquare.neg]
  rw [HexRootsMathlib.DyadicSquare.closedDisc, Metric.mem_closedBall] at hz ⊢
  rw [hcenter, hradius]
  simpa only [dist_neg_neg] using hz

namespace AlgebraicRoot

/-- Reflection computes complex negation. -/
theorem neg_toComplex (a : AlgebraicRoot) :
    a.neg.toComplex = -a.toComplex := by
  have hroot :
      (HexRootsMathlib.toPolyℂ a.p.negRoots).IsRoot (-a.toComplex) :=
    ZPoly.negRoots_isRoot_of_isRoot
      (HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep)
      (AlgebraicRoot.toComplex_isRoot a)
  have hmem :
      -a.toComplex ∈
        HexRootsMathlib.DyadicSquare.closedDisc a.neg.rep.1.square := by
    exact DyadicSquare.neg_mem_closedDisc
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc a.rep)
  exact (HexRootsMathlib.RefinedIsolation.eq_root_of_mem_closedDisc
    a.neg.rep hroot hmem).symm

/-- A certified lazy sum denotes the sum of its inputs. -/
theorem add?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.add? b = some c) :
    c.toComplex = a.toComplex + b.toComplex := by
  unfold AlgebraicRoot.add? at h
  apply AlgebraicRoot.ofEliminant?_sound
    (raw := ZPoly.addEliminant a.p b.p)
    (ballAt := fun prec => do
      let target := prec + 4
      let ar ← a.rep.refineTo? target
      let br ← b.rep.refineTo? target
      some (ar.1.1.square.toBall.add br.1.1.square.toBall))
    h (ZPoly.addEliminant_isRoot a b)
  intro ball hball
  dsimp only at hball
  obtain ⟨ar, har, hball⟩ := Option.bind_eq_some_iff.mp hball
  obtain ⟨br, hbr, hball⟩ := Option.bind_eq_some_iff.mp hball
  have hballEq := Option.some.inj hball
  subst ball
  apply DyadicComplexBall.add_mem
  · have harRoot :
        HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
      exact (HexRootsMathlib.RefinedIsolation.refineTo_root
        a.rep _ .nkThenPellet har).trans rfl
    rw [← harRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
  · have hbrRoot :
        HexRootsMathlib.RefinedIsolation.root br.1 = b.toComplex := by
      exact (HexRootsMathlib.RefinedIsolation.refineTo_root
        b.rep _ .nkThenPellet hbr).trans rfl
    rw [← hbrRoot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)

/-- The bounded lazy addition search always finds its certificate. -/
theorem add?_isSome (a b : AlgebraicRoot) :
    (a.add? b).isSome := by
  unfold AlgebraicRoot.add?
  have harSome := RefinedIsolation.refineTo?_isSome a.rep
    ((separationDepth (ZPoly.squareFreeCore
      (ZPoly.addEliminant a.p b.p)) : Int) + 4)
  cases har : a.rep.refineTo?
      ((separationDepth (ZPoly.squareFreeCore
        (ZPoly.addEliminant a.p b.p)) : Int) + 4) .nkThenPellet with
  | none => simp [har] at harSome
  | some ar =>
      have hbrSome := RefinedIsolation.refineTo?_isSome b.rep
        ((separationDepth (ZPoly.squareFreeCore
          (ZPoly.addEliminant a.p b.p)) : Int) + 4)
      cases hbr : b.rep.refineTo?
          ((separationDepth (ZPoly.squareFreeCore
            (ZPoly.addEliminant a.p b.p)) : Int) + 4) .nkThenPellet with
      | none => simp [hbr] at hbrSome
      | some br =>
          apply AlgebraicRoot.ofEliminant?_isSome
            (raw := ZPoly.addEliminant a.p b.p)
            (ballAt := fun prec => do
              let target := prec + 4
              let ar ← a.rep.refineTo? target
              let br ← b.rep.refineTo? target
              some (ar.1.1.square.toBall.add br.1.1.square.toBall))
            (z := a.toComplex + b.toComplex)
            (ZPoly.addEliminant_ne_zero a b)
            (ZPoly.addEliminant_isRoot a b)
            (ar.1.1.square.toBall.add br.1.1.square.toBall)
          · dsimp only
            rw [har, hbr]
            rfl
          · apply DyadicComplexBall.add_mem
            · have harRoot :
                  HexRootsMathlib.RefinedIsolation.root ar.1 = a.toComplex := by
                exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                  a.rep _ .nkThenPellet har).trans rfl
              rw [← harRoot]
              exact DyadicComplexBall.mem_toBall
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc ar.1)
            · have hbrRoot :
                  HexRootsMathlib.RefinedIsolation.root br.1 = b.toComplex := by
                exact (HexRootsMathlib.RefinedIsolation.refineTo_root
                  b.rep _ .nkThenPellet hbr).trans rfl
              rw [← hbrRoot]
              exact DyadicComplexBall.mem_toBall
                (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc br.1)
          · rw [DyadicComplexBall.realRadius_add]
            have harPrec := RefinedIsolation.refineTo?_precision a.rep
              ((separationDepth (ZPoly.squareFreeCore
                (ZPoly.addEliminant a.p b.p)) : Int) + 4)
              .nkThenPellet har
            have hbrPrec := RefinedIsolation.refineTo?_precision b.rep
              ((separationDepth (ZPoly.squareFreeCore
                (ZPoly.addEliminant a.p b.p)) : Int) + 4)
              .nkThenPellet hbr
            have hsepNat :
                mahlerPrec (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) ≤
                  separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) := by
              rw [separationDepth]
              omega
            have hsepInt :
                (mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) ≤
                  (separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) := by
              exact_mod_cast hsepNat
            have hpow :
                (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) ≤
                  (2 : ℝ) ^ (-(mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
            calc
              ar.1.1.square.toBall.realRadius +
                    br.1.1.square.toBall.realRadius ≤
                  2 * (2 : ℝ) ^ (-((separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4)) +
                    2 * (2 : ℝ) ^ (-((separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4)) :=
                add_le_add
                  (DyadicComplexBall.realRadius_toBall_le harPrec)
                  (DyadicComplexBall.realRadius_toBall_le hbrPrec)
              _ = (1 / 4 : ℝ) * (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                rw [show -((separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) + 4) =
                    -(separationDepth
                      (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int) - 4 by
                  omega]
                rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
                norm_num
                ring
              _ ≤ (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                have hnonneg : 0 ≤ (2 : ℝ) ^ (-(separationDepth
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := by
                  positivity
                nlinarith
              _ ≤ (2 : ℝ) ^ (-(mahlerPrec
                    (ZPoly.squareFreeCore (ZPoly.addEliminant a.p b.p)) : Int)) := hpow

/-- Total lazy addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicRoot) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  cases h : a.add? b with
  | none =>
      have hsome := add?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.add, h] using add?_sound a b h

/-- A certified lazy difference denotes the difference of its inputs. -/
theorem sub?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.sub? b = some c) :
    c.toComplex = a.toComplex - b.toComplex := by
  have hsum : c.toComplex = a.toComplex + b.neg.toComplex :=
    add?_sound a b.neg h
  rw [neg_toComplex] at hsum
  exact hsum

/-- The bounded lazy subtraction search always finds its certificate. -/
theorem sub?_isSome (a b : AlgebraicRoot) :
    (a.sub? b).isSome := by
  exact add?_isSome a b.neg

/-- Total lazy subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicRoot) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  cases h : a.sub? b with
  | none =>
      have hsome := sub?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.sub, h] using sub?_sound a b h

/-- A certified lazy product denotes the product of its inputs. -/
theorem mul?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.mul? b = some c) :
    c.toComplex = a.toComplex * b.toComplex := by
  sorry

/-- The bounded lazy multiplication search always finds its certificate. -/
theorem mul?_isSome (a b : AlgebraicRoot) :
    (a.mul? b).isSome := by
  sorry

/-- Total lazy multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicRoot) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  cases h : a.mul? b with
  | none =>
      have hsome := mul?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.mul, h] using mul?_sound a b h

/-- A certified lazy inverse denotes the reciprocal of its input, including
the executable convention `0⁻¹ = 0`. -/
theorem inv?_sound (a : AlgebraicRoot) {b : AlgebraicRoot}
    (h : a.inv? = some b) :
    b.toComplex = a.toComplex⁻¹ := by
  sorry

/-- The bounded lazy inverse search always finds its certificate. -/
theorem inv?_isSome (a : AlgebraicRoot) :
    a.inv?.isSome := by
  sorry

/-- Total lazy inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicRoot) :
    a.inv.toComplex = a.toComplex⁻¹ := by
  cases h : a.inv? with
  | none =>
      have hsome := inv?_isSome a
      simp [h] at hsome
  | some b =>
      simpa [AlgebraicRoot.inv, h] using inv?_sound a h

/-- A certified lazy quotient denotes the quotient of its inputs. -/
theorem div?_sound (a b : AlgebraicRoot) {c : AlgebraicRoot}
    (h : a.div? b = some c) :
    c.toComplex = a.toComplex / b.toComplex := by
  cases hb : b.inv? with
  | none => simp [AlgebraicRoot.div?, hb] at h
  | some bInv =>
      have hmul : a.mul? bInv = some c := by
        simpa [AlgebraicRoot.div?, hb] using h
      rw [mul?_sound a bInv hmul, inv?_sound b hb]
      rfl

/-- The bounded lazy division search always finds its certificate. -/
theorem div?_isSome (a b : AlgebraicRoot) :
    (a.div? b).isSome := by
  cases hb : b.inv? with
  | none =>
      have hsome := inv?_isSome b
      simp [hb] at hsome
  | some bInv =>
      simpa [AlgebraicRoot.div?, hb] using mul?_isSome a bInv

/-- Total lazy division computes complex division. -/
theorem div_toComplex (a b : AlgebraicRoot) :
    (a.div b).toComplex = a.toComplex / b.toComplex := by
  cases h : a.div? b with
  | none =>
      have hsome := div?_isSome a b
      simp [h] at hsome
  | some c =>
      simpa [AlgebraicRoot.div, h] using div?_sound a b h

end AlgebraicRoot

namespace AlgebraicNumber

/-- Canonical addition computes complex addition. -/
theorem add_toComplex (a b : AlgebraicNumber) :
    (a + b).toComplex = a.toComplex + b.toComplex := by
  change (a.toRoot.add b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.add_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical subtraction computes complex subtraction. -/
theorem sub_toComplex (a b : AlgebraicNumber) :
    (a - b).toComplex = a.toComplex - b.toComplex := by
  change (a.toRoot.sub b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.sub_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical multiplication computes complex multiplication. -/
theorem mul_toComplex (a b : AlgebraicNumber) :
    (a * b).toComplex = a.toComplex * b.toComplex := by
  change (a.toRoot.mul b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.mul_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

/-- Canonical negation computes complex negation. -/
theorem neg_toComplex (a : AlgebraicNumber) :
    (-a).toComplex = -a.toComplex := by
  change a.toRoot.neg.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.neg_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical inversion computes complex inversion. -/
theorem inv_toComplex (a : AlgebraicNumber) :
    a⁻¹.toComplex = a.toComplex⁻¹ := by
  change a.toRoot.inv.exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.inv_toComplex,
    AlgebraicNumber.toRoot_toComplex]

/-- Canonical division computes complex division. -/
theorem div_toComplex (a b : AlgebraicNumber) :
    (a / b).toComplex = a.toComplex / b.toComplex := by
  change (a.toRoot.div b.toRoot).exact.toComplex = _
  rw [AlgebraicRoot.exact_toComplex, AlgebraicRoot.div_toComplex,
    AlgebraicNumber.toRoot_toComplex, AlgebraicNumber.toRoot_toComplex]

end AlgebraicNumber

end

end Hex
