/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Irreducibility
public import HexBerlekampZassenhausMathlib.LocalFactors
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LocalFactors

public section
set_option backward.proofsInPublic true

/-!
The semantic mod-p factorization bundle.

`ModPFactorization f data` collects every fact the Berlekamp-Zassenhaus
certification cone actually consumes about a `PrimeChoiceData`: primality,
the good-prime condition for the lift target `f`, the recorded modular image,
and the semantic invariants of the factor array (monic, irreducible, nodup,
pairwise coprime, nonempty, product congruent to `f` mod `p`).

The bundle is independent of how the prime and factor array were selected, so
recursive direct lifting can certify tracked sublists of a parent
factorization without replaying a Berlekamp run.

`modPFactorization_of_choosePrimeData` recovers the bundle from the
selection witness, so existing entry points discharge it for free.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Semantic validity of `data` as a mod-p factorization package for the
monic lift target `f`: everything the certification cone consumes about a
`PrimeChoiceData`, with no reference to how it was produced. -/
structure ModPFactorization (f : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  /-- The selected modulus is prime. -/
  prime : Hex.Nat.Prime data.p
  /-- The prime satisfies the executable admissibility test for `f`. -/
  good :
    letI := data.bounds
    Hex.isGoodPrime f data.p = true
  /-- The cached modular polynomial is the reduction of `f`. -/
  fModP_eq :
    letI := data.bounds
    data.fModP = Hex.ZPoly.modP data.p f
  /-- Every modular factor is monic. -/
  monic :
    letI := data.bounds
    ∀ g ∈ data.factorsModP, Hex.DensePoly.Monic g
  /-- The modular factor list is nonempty. -/
  ne_nil : data.factorsModP.toList ≠ []
  /-- No modular factor occurs twice. -/
  nodup : data.factorsModP.toList.Nodup
  /-- The splits used for the multifactor lift are pairwise coprime. -/
  coprime :
    letI := data.bounds
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits data.p data.factorsModP.toList
  /-- Every indexed modular factor is irreducible. -/
  irreducible :
    ∀ i : ModPFactorIndex data,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial data.p data.bounds
          (modPFactor data i))
  /-- The product of the lifted factors agrees with the monic modular image. -/
  product :
    letI := data.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
      (Hex.FpPoly.liftToZ
        (Hex.monicModularImage (Hex.ZPoly.modP data.p f)))
      data.p
  /-- Every modular factor has positive degree. -/
  natDegree_pos :
    letI := data.bounds
    ∀ g ∈ data.factorsModP,
      0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree

/-- The `modP`/`liftToZ` roundtrip on an `FpPoly` product: reducing the
integer product of the lifts recovers the `FpPoly` fold product. -/
theorem modP_polyProduct_map_liftToZ {p : Nat} [Hex.ZMod64.Bounds p]
    (arr : Array (Hex.FpPoly p)) :
    Hex.ZPoly.modP p (Array.polyProduct (arr.map Hex.FpPoly.liftToZ)) =
      arr.toList.foldl (· * ·) 1 := by
  cases arr with
  | mk l =>
      suffices h : ∀ acc : Hex.ZPoly,
          Hex.ZPoly.modP p ((l.map Hex.FpPoly.liftToZ).foldl (· * ·) acc) =
            l.foldl (· * ·) (Hex.ZPoly.modP p acc) by
        simpa [Array.polyProduct, Hex.ZPoly.modP_one] using h 1
      intro acc
      induction l generalizing acc with
      | nil => simp
      | cons x xs ih =>
          simp only [List.map_cons, List.foldl_cons]
          rw [ih, modP_mul, Hex.FpPoly.modP_liftToZ]

/-- Assemble the semantic bundle from a proved Berlekamp-form factorization.
The lift target must be primitive with positive leading coefficient and
positive degree. -/
theorem modPFactorization_of_form
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hprime : Hex.Nat.Prime data.p)
    (hgood : @Hex.isGoodPrime f data.p data.bounds = true)
    (hfmod : data.fModP = @Hex.ZPoly.modP data.p data.bounds f)
    (hform : Hex.factorsModPBerlekampForm f data)
    (hprim : Hex.ZPoly.Primitive f)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data := by
  refine
    { prime := hprime
      good := hgood
      fModP_eq := ?_
      monic := factorsModP_monic_of_factorsModPBerlekampForm f data hform
      ne_nil := factorsModP_ne_nil_of_factorsModPBerlekampForm f data hform
      nodup := factorsModP_nodup_of_factorsModPBerlekampForm f data hform hgood
      coprime := factorsModP_coprime_of_factorsModPBerlekampForm f data hform hgood
      irreducible :=
        factors_irreducible_of_factorsModPBerlekampForm f data hform hgood hpos
      product := ?_
      natDegree_pos :=
        factorsModP_natDegree_pos_of_factorsModPBerlekampForm f data hform
          hgood hpos }
  · exact hfmod
  · exact
      factorsModP_polyProduct_congr_of_factorsModPBerlekampForm_of_primitive_pos_lc_core
        f data hprim hlc_pos hform hgood

/-- The selection witness yields the semantic bundle through the
`choosePrimeData?` extraction lemmas. -/
theorem modPFactorization_of_choosePrimeData
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hchoose : Hex.choosePrimeData? f = some data)
    (hprim : Hex.ZPoly.Primitive f)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data := by
  have hprime := Hex.choosePrimeData?_prime f data hchoose
  have hgood := Hex.choosePrimeData?_isGoodPrime f data hchoose
  have hform : Hex.factorsModPBerlekampForm f data := by
    obtain ⟨hzero, heq⟩ :=
      Hex.choosePrimeData?_factorsModP_berlekamp_form f data hchoose
    exact ⟨hprime, hzero, heq⟩
  exact modPFactorization_of_form hprime hgood
    (Hex.choosePrimeData?_fModP_eq f data hchoose) hform hprim hlc_pos hpos

/-- An explicit cached prime trial yields the semantic modular factorization
bundle consumed by direct lifting. -/
theorem modPFactorization_of_probePrimeData
    {f : Hex.ZPoly} {candidate : Hex.SmallPrimeCandidate}
    {data : Hex.PrimeChoiceData}
    (hprobe : Hex.probePrimeData? f candidate = some data)
    (hprim : Hex.ZPoly.Primitive f)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data :=
  modPFactorization_of_form
    (Hex.probePrimeData?_prime f candidate data hprobe)
    (Hex.probePrimeData?_isGoodPrime f candidate data hprobe)
    (Hex.probePrimeData?_fModP_eq f candidate data hprobe)
    (Hex.probePrimeData?_form f candidate data hprobe)
    hprim hlc_pos hpos


/-- A modular factor array of positive-degree monic factors has no more
entries than the degree of any monic integer target to which its product is
congruent. -/
theorem ModPFactorization.factorCount_le_degree_of_product
    {f target : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (h : ModPFactorization f data)
    (hmonic : Hex.DensePoly.Monic target)
    (hcongr :
      letI := data.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
        target data.p) :
    data.factorsModP.size ≤ target.degree?.getD 0 := by
  let := data.bounds
  have hp : 1 < data.p := h.prime.one_lt
  have : Fact (_root_.Nat.Prime data.p) :=
    ⟨natPrime_of_hexNatPrime h.prime⟩
  have : Nontrivial (ZMod data.p) := inferInstance
  let t : Multiset (Polynomial ℤ) :=
    (data.factorsModP.toList : Multiset (Hex.FpPoly data.p)).map
      (fun g => HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g))
  have ht_monic : ∀ q ∈ t, q.Monic := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    apply HexHenselMathlib.toPolynomial_monic_of_dense_monic
    apply Hex.FpPoly.monic_liftToZ_of_monic g hp
    exact h.monic g (by simpa [t] using hg)
  have ht_pos : ∀ q ∈ t, 0 < q.natDegree := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    exact h.natDegree_pos g (by simpa [t] using hg)
  have hcard_le_sum :
      t.card ≤ (t.map Polynomial.natDegree).sum := by
    have aux : ∀ u : Multiset (Polynomial ℤ),
        (∀ q ∈ u, 0 < q.natDegree) →
          u.card ≤ (u.map Polynomial.natDegree).sum := by
      intro u hu
      induction u using Multiset.induction_on with
      | empty => simp
      | @cons q u ih =>
          have hq : 0 < q.natDegree := hu q (by simp)
          have hu' : ∀ z ∈ u, 0 < z.natDegree :=
            fun z hz => hu z (Multiset.mem_cons_of_mem hz)
          have hih := ih hu'
          simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
          omega
    exact aux t ht_pos
  have hprod :
      t.prod =
        HexPolyZMathlib.toPolynomial
          (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ)) := by
    rw [polyProduct_toPolynomial]
    simp only [t, Multiset.map_coe, Multiset.prod_coe, Array.toList_map,
      List.map_map]
    congr 1
  have hmap :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
      target data.p hcongr
  have hprod_monic : t.prod.Monic := by
    have aux : ∀ u : Multiset (Polynomial ℤ),
        (∀ q ∈ u, q.Monic) → u.prod.Monic := by
      intro u hu
      induction u using Multiset.induction_on with
      | empty => simp
      | @cons q u ih =>
          rw [Multiset.prod_cons]
          exact (hu q (by simp)).mul
            (ih (fun z hz => hu z (Multiset.mem_cons_of_mem hz)))
    exact aux t ht_monic
  have hf_monic : (HexPolyZMathlib.toPolynomial target).Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic target hmonic
  have hdegree :
      t.prod.natDegree =
        (HexPolyZMathlib.toPolynomial target).natDegree := by
    have hleft :=
      hprod_monic.natDegree_map (Int.castRingHom (ZMod data.p))
    have hright :=
      hf_monic.natDegree_map (Int.castRingHom (ZMod data.p))
    have hmap' :
      t.prod.map (Int.castRingHom (ZMod data.p)) =
          (HexPolyZMathlib.toPolynomial target).map
            (Int.castRingHom (ZMod data.p)) := by
      rw [hprod]
      simpa using hmap
    rw [← hleft, ← hright, hmap']
  have hsum :
      (t.map Polynomial.natDegree).sum =
        (HexPolyZMathlib.toPolynomial target).natDegree := by
    rw [← Polynomial.natDegree_multiset_prod_of_monic t ht_monic, hdegree]
  have hcard : t.card = data.factorsModP.size := by
    simp [t]
  rw [← hcard, ← HexPolyMathlib.natDegree_toPolynomial target, ← hsum]
  exact hcard_le_sum

end HexBerlekampZassenhausMathlib
