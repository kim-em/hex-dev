/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificatePair
public import HexGroebnerTheory.CertificateLeading
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

public section

namespace HexGroebnerTheory.Certificate
open Hex.Groebner.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

private theorem difference_length {n : Nat} {a b : List Nat}
    (ha : a.length = n) (hb : b.length = n) : (difference a b).length = n := by
  simp [difference, ha, hb]

/-- Serialized pointwise differences transport to truncated exponent subtraction. -/
theorem difference_eq {n : Nat} {a b : List Nat}
    (ha : a.length = n) (hb : b.length = n) :
    HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n (difference a b)) =
      HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n a) -
        HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n b) := by
  ext i
  simp only [HexMvPolyTheory.monoEquiv_apply, Finsupp.tsub_apply,
    Hex.MvPoly.Kernel.get_mono]
  have hia : i.val < a.length := by omega
  have hib : i.val < b.length := by omega
  simp [List.getD_eq_getElem?_getD, hia, hib,
    difference, List.getElem_zipWith]

private theorem singleton_canonical {p n c : Nat} {e : List Nat}
    (he : e.length = n) (hc : c ≠ 0) (hb : c < p) :
    Hex.MvPoly.Kernel.CanonicalMod p n [(e, c)] := by
  simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical, he, hc, hb]

private theorem leading_none {order : Hex.Groebner.TermOrder} {f : Polynomial}
    (h : leading order f = none) : f = [] := by
  cases f <;> simp_all [leading]

/-- Exact S-polynomial construction preserves canonical residue serialization. -/
theorem sPolynomial_canonical {p n : Nat} (order : Hex.Groebner.TermOrder)
    {f g : Polynomial} (hf : Hex.MvPoly.Kernel.CanonicalMod p n f)
    (hg : Hex.MvPoly.Kernel.CanonicalMod p n g) :
    Hex.MvPoly.Kernel.CanonicalMod p n (sPolynomial p order f g) := by
  unfold sPolynomial
  split
  · rename_i a b ha hb
    have af := leading_mem ha
    have bg := leading_mem hb
    exact Hex.MvPoly.Kernel.subMod_canonical p
      (Hex.MvPoly.Kernel.mulMod_canonical p
        (singleton_canonical (difference_length (hg.1.1 _ bg) (hf.1.1 _ af))
          (hg.1.2.2 _ bg) (hg.2 _ bg)) hf)
      (Hex.MvPoly.Kernel.mulMod_canonical p
        (singleton_canonical (difference_length (hf.1.1 _ af) (hg.1.1 _ bg))
          (hf.1.2.2 _ af) (hf.2 _ af)) hg)
  · simp [Hex.MvPoly.Kernel.CanonicalMod, Hex.MvPoly.Kernel.Canonical]

/-- Certificate S-polynomials use the actual leading exponents and coefficients
of the existing residue polynomial interpretation. -/
theorem sPolynomial_eq {p n : Nat} [Hex.ZMod64.Bounds p]
    (order : Hex.Groebner.TermOrder) {f g : Polynomial}
    (hf : Hex.MvPoly.Kernel.CanonicalMod p n f)
    (hg : Hex.MvPoly.Kernel.CanonicalMod p n g) :
    HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) (sPolynomial p order f g) =
      (toMonomialOrder (order.cmp n)).sPolynomial
        (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) f)
        (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) g) := by
  cases ha : leading order f with
  | none =>
    have hz := leading_none ha
    subst f
    simp [sPolynomial, leading, MonomialOrder.sPolynomial_left_zero]
  | some a =>
    cases hb : leading order g with
    | none =>
      have hz := leading_none hb
      subst g
      simp [sPolynomial, leading, MonomialOrder.sPolynomial_right_zero]
    | some b =>
      have af := leading_mem ha
      have bg := leading_mem hb
      have ca := singleton_canonical (difference_length (hg.1.1 _ bg) (hf.1.1 _ af))
        (hg.1.2.2 _ bg) (hg.2 _ bg)
      have cb := singleton_canonical (difference_length (hf.1.1 _ af) (hg.1.1 _ bg))
        (hf.1.2.2 _ af) (hf.2 _ af)
      rw [sPolynomial, ha, hb,
        HexMvPolyTheory.Kernel.denoteMod_subMod p
          (Hex.MvPoly.Kernel.mulMod_canonical p ca hf) (Hex.MvPoly.Kernel.mulMod_canonical p cb hg),
        HexMvPolyTheory.Kernel.denoteMod_mulMod p ca hf,
        HexMvPolyTheory.Kernel.denoteMod_mulMod p cb hg]
      simp only [HexMvPolyTheory.Kernel.denoteMod_cons, HexMvPolyTheory.Kernel.denoteMod_nil,
        add_zero, difference_eq (hg.1.1 _ bg) (hf.1.1 _ af),
        difference_eq (hf.1.1 _ af) (hg.1.1 _ bg)]
      rw [MonomialOrder.sPolynomial, leading_degree order hf ha, leading_degree order hg hb,
        leading_coefficient order hf ha, leading_coefficient order hg hb]

end HexGroebnerTheory.Certificate
