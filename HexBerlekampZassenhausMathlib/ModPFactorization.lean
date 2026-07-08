/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.HenselFactorProps

public section
set_option backward.proofsInPublic true

/-!
The semantic mod-p factorization bundle (#8625).

`ModPFactorization f data` collects every fact the Berlekamp-Zassenhaus
certification cone actually consumes about a `PrimeChoiceData`: primality,
the good-prime condition for the lift target `f`, the recorded modular image,
and the semantic invariants of the factor array (monic, irreducible, nodup,
pairwise coprime, nonempty, product congruent to `f` mod `p`).

Historically the cone was keyed on the SELECTION witness
`ZPoly.toMonicPrimeData? core = some data`, whose `factorsModPBerlekampForm`
component records that `data.factorsModP` is the LITERAL `berlekampFactor`
output. No consumer needs that literal form (nor any selection-walk fact):
they extract exactly the fields below, via the
`…_of_factorsModPBerlekampForm` family. Keying the cone on this bundle
instead lets the recursive per-remainder re-lift certify pieces whose factor
arrays are dilated tracked sublists of the parent's — semantically valid
factorizations that no Berlekamp run ever produced.

`modPFactorization_of_choosePrimeData` recovers the bundle from the
selection witness, so existing entry points discharge it for free.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Semantic validity of `data` as a mod-p factorization package for the
monic lift target `f`: everything the certification cone consumes about a
`PrimeChoiceData`, with no reference to how it was produced. -/
structure ModPFactorization (f : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  prime : Hex.Nat.Prime data.p
  good :
    letI := data.bounds
    Hex.isGoodPrime f data.p = true
  fModP_eq :
    letI := data.bounds
    data.fModP = Hex.ZPoly.modP data.p f
  monic :
    letI := data.bounds
    ∀ g ∈ data.factorsModP, Hex.DensePoly.Monic g
  ne_nil : data.factorsModP.toList ≠ []
  nodup : data.factorsModP.toList.Nodup
  coprime :
    letI := data.bounds
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits data.p data.factorsModP.toList
  irreducible :
    ∀ i : ModPFactorIndex data,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial data.p data.bounds
          (modPFactor data i))
  product :
    letI := data.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ)) f data.p
  natDegree_pos :
    letI := data.bounds
    ∀ g ∈ data.factorsModP,
      0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree

/-- The selection witness yields the semantic bundle: assemble the fields
from the `choosePrimeData?` extraction lemmas and the
`…_of_factorsModPBerlekampForm` family. The lift target must be monic of
positive degree (which `(toMonic core).monic` always is at the use sites). -/
theorem modPFactorization_of_choosePrimeData
    {f : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hchoose : Hex.choosePrimeData? f = some data)
    (hmonic : Hex.DensePoly.Monic f)
    (hpos : 0 < f.degree?.getD 0) :
    ModPFactorization f data := by
  have hprime := Hex.choosePrimeData?_prime f data hchoose
  have hgood := Hex.choosePrimeData?_isGoodPrime f data hchoose
  have hform : Hex.factorsModPBerlekampForm f data := by
    obtain ⟨hzero, heq⟩ :=
      Hex.choosePrimeData?_factorsModP_berlekamp_form f data hchoose
    exact ⟨hprime, hzero, heq⟩
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
      product :=
        factorsModP_polyProduct_congr_of_factorsModPBerlekampForm f data
          hmonic hform hgood
      natDegree_pos :=
        factorsModP_natDegree_pos_of_factorsModPBerlekampForm f data hform
          hgood hpos }
  exact Hex.choosePrimeData?_fModP_eq f data hchoose

/-- The `toMonicPrimeData?` form of the bundle producer. -/
theorem modPFactorization_of_toMonicPrimeData
    {core : Hex.ZPoly} {data : Hex.PrimeChoiceData}
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some data)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ModPFactorization (Hex.ZPoly.toMonic core).monic data := by
  have hmonic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hpos : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  exact modPFactorization_of_choosePrimeData hselected hmonic hpos

end HexBerlekampZassenhausMathlib
