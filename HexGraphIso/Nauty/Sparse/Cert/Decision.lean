/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Sound
public import HexGraphIso.Nauty.Sparse.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Distinguish complete sparse keys using their proved native order. -/
@[expose] def checkDiff (a b : Key n) : Bool := Key.cmp a b != .eq

theorem checkDiff_sound {a b : Key n} (h : checkDiff a b = true) : a ≠ b := by
  simp only [checkDiff, bne_iff_ne] at h
  exact fun he => h (Key.cmp_eq.mpr he)

/-- Two accepted sparse canonical certificates with differing keys prove
non-isomorphism. Certificate failure is never used as a negative verdict. -/
theorem not_isomorphic_of_checkKeys {G H : GraphIso.Sparse.Colored n k}
    {cg ch : CertNode} {bg bh : Key n}
    (hg : checkKey G cg bg = true) (hh : checkKey H ch bh = true)
    (hd : checkDiff bg bh = true) : ¬ GraphIso.Sparse.Isomorphic G H := by
  intro hi
  have he := canonSpecKey_iso hi
  rw [checkKey_sound hg, checkKey_sound hh] at he
  exact checkDiff_sound hd he

end Hex.GraphIso.Nauty.Sparse
