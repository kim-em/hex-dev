/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert

public section

/-!
The `CanonResult`-level certificate wrapper: a checked canonical key
together with the labelling that achieves it, packaged as the
relabelled canonical form. `checkCanon` validates the certificate
replay, the labelling's rows against the claimed key, and builds the
form; its soundness ties the form to `canonSpecKey`.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Validate a certificate together with the claimed canonical
labelling: the replay must accept the key, and the labelling's leaf
rows must be the key's rows. Returns the canonical form and label. -/
@[expose] def checkCanon (G : Colored n k) (cert : CertNode) (B : Key)
    (lab : Array Nat) : Option (CanonResult n k) :=
  if h : lab.size = n ∧ ∀ v ∈ lab, v < n then
    match Label.ofVector? (⟨lab.attach.map fun v =>
        (⟨v.val, h.2 v.val v.property⟩ : Fin n), by simp [h.1]⟩ :
        Vector (Fin n) n) with
    | none => none
    | some l =>
      if checkKey G cert B &&
          (B.rows == leafRows { n := n, g := rowsOf G } lab) then
        some { form := G.relabel l, label := l }
      else
        none
  else
    none

/-- A successful `checkCanon` pins the spec key, exhibits the form as
a relabelling, and keeps the form in the isomorphism class. -/
theorem checkCanon_sound {G : Colored n k} {cert : CertNode} {B : Key}
    {lab : Array Nat} {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    canonSpecKey G = B ∧ res.form = G.relabel res.label ∧
      Isomorphic G res.form ∧
      B.rows = leafRows { n := n, g := rowsOf G } lab := by
  rw [checkCanon] at h
  split at h
  · split at h
    · cases h
    · next l hl =>
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        injection h with h'
        have hform : res.form = G.relabel l := by
          rw [← h']
        have hlabel : res.label = l := by
          rw [← h']
        refine ⟨checkKey_sound hcond.1, ?_, ?_, hcond.2⟩
        · rw [hform, hlabel]
        · rw [hform]
          exact isomorphic_relabel G l
      · cases h
  · cases h

/-- Produce a checked `CanonResult`: run the certified key search and
replay the best leaf to extract its labelling. -/
@[expose] def certifyCanon? (G : Colored n k) :
    Option (CanonResult n k) :=
  match certifyKey? G with
  | none => none
  | some (cert, B) =>
    match bestLab? { n := n, g := rowsOf G } 100 B.rows n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length B.codes with
    | none => none
    | some lab => checkCanon G cert B lab

/-! # The certificate-based negative decision -/

/-- Executable disequality of two canonical keys: the lexicographic
comparison finds the first differing entry. -/
@[expose] def checkDiff (B1 B2 : Key) : Bool :=
  keyCmp B1 B2 != Ordering.eq

theorem checkDiff_sound {B1 B2 : Key} (h : checkDiff B1 B2 = true) :
    B1 ≠ B2 := by
  rw [checkDiff, bne_iff_ne, ne_eq] at h
  intro he
  exact h (keyCmp_eq_iff.mpr he)

/-- Distinct spec keys separate isomorphism classes. -/
theorem not_isomorphic_of_key_ne {G H : Colored n k} {BG BH : Key}
    (hG : canonSpecKey G = BG) (hH : canonSpecKey H = BH)
    (hne : BG ≠ BH) : ¬Isomorphic G H := fun hiso =>
  hne (hG ▸ hH ▸ canonSpecKey_eq_of_isomorphic hiso)

/-- Two checked certificates with differing keys prove
non-isomorphism. -/
theorem not_isomorphic_of_certs {G H : Colored n k}
    {certG certH : CertNode} {BG BH : Key} {labG labH : Array Nat}
    {resG resH : CanonResult n k}
    (hG : checkCanon G certG BG labG = some resG)
    (hH : checkCanon H certH BH labH = some resH)
    (hd : checkDiff BG BH = true) : ¬Isomorphic G H :=
  not_isomorphic_of_key_ne (checkCanon_sound hG).1
    (checkCanon_sound hH).1 (checkDiff_sound hd)

end Hex.GraphIso.Nauty
