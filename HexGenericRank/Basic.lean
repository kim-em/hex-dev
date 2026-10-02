/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank
public import HexMvGcd.Divide
public import HexMvGcd.Instances

@[expose] public section

namespace Hex.GenericRank

open Hex.Matrix

universe u

variable {k n m : Nat} {C : Type u} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C] [DecidableEq C]
  [BEq C] [LawfulBEq C] [Dvd C] [GcdOps C] [IsMonomialOrder cmp] [LawfulGcdOps C]

/-- Polynomial exact division and a nontrivial coefficient domain supply
hex-rank's Mathlib-free domain laws. -/
instance : DomainLaws (MvPoly k C cmp) := by
  apply DomainLaws.of_exactDivLaws
  intro h
  have hc := congrArg (MvPoly.coeff (Mono.zero : Mono k)) h
  simp only [MvPoly.coeff_one, MvPoly.coeff_zero, ↓reduceIte] at hc
  exact LawfulGcdOps.one_ne_zero hc

/-- The fraction-free rank certificate of a multivariate polynomial matrix. -/
def genericCert (P : Matrix (MvPoly k C cmp) n m) : RankCert (MvPoly k C cmp) n m :=
  rankCertWith Hex.exactDiv P

/-- Rank over the fraction field of the polynomial ring. -/
def genericRank (P : Matrix (MvPoly k C cmp) n m) : Nat :=
  rankWith Hex.exactDiv P

/-- Produce a certificate and return it only after the reference checker accepts it. -/
def genericCert? (P : Matrix (MvPoly k C cmp) n m) :
    Option (RankCert (MvPoly k C cmp) n m) :=
  certifyRankWith Hex.exactDiv P

omit [Dvd C] [LawfulGcdOps C] in
/-- The producer's certificate and rank use the same pivot profile. -/
theorem genericCert_rank (P : Matrix (MvPoly k C cmp) n m) :
    (genericCert P).rank = genericRank P := rfl

omit [Dvd C] [LawfulGcdOps C] in
/-- Every returned certificate has passed the reference check. -/
theorem genericCert?_check {P : Matrix (MvPoly k C cmp) n m}
    {c : RankCert (MvPoly k C cmp) n m} (h : genericCert? P = some c) :
    checkRank P c = true := by
  unfold genericCert? certifyRankWith at h
  dsimp only at h
  split at h
  next hc => cases h; exact hc
  next => contradiction

/-- The selected minor of a returned certificate is nonzero. -/
theorem genericCert?_minor {P : Matrix (MvPoly k C cmp) n m}
    {c : RankCert (MvPoly k C cmp) n m} (h : genericCert? P = some c) :
    det (selectedSubmatrix P c.rows c.cols) ≠ 0 :=
  c.det_ne_zero (genericCert?_check h)

/-- Every next-size minor of a returned certificate vanishes. -/
theorem genericCert?_succ_minor {P : Matrix (MvPoly k C cmp) n m}
    {c : RankCert (MvPoly k C cmp) n m} (h : genericCert? P = some c)
    (rows : Vector (Fin n) (c.rank + 1)) (cols : Vector (Fin m) (c.rank + 1)) :
    det (selectedSubmatrix P rows cols) = 0 :=
  c.det_succ_eq_zero (genericCert?_check h) rows cols

end Hex.GenericRank
