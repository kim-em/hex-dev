/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Complete

public section

/-!
Public canonical-form operations, backed by the certificate-checked
nauty-semantic canonicalization: the branch-and-bound producer first,
validated by the trusted replay, with the provably total exhaustive
fallback. Every theorem stated here descends from the Lean-proved
`specCanon` equivalence.

`canonicalize` is total. `findIso` composes the two canonical labels
into a forward transporter when the canonical forms agree. The bounded
surface separates search limits from replay limits and returns `none`
on exhaustion; exhaustion is never evidence of non-isomorphism.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Compute the certificate-checked canonical form of a coloured graph
together with the label producing it: the untrusted search's answer is
accepted only through the trusted replay, and every theorem below is
proved about this surface. Total; worst-case cost is factorial. -/
@[expose] def canonicalizeChecked (G : Colored n k) : CanonResult n k :=
  Nauty.canonicalizeSpec G

/-- The certificate-checked canonical form. -/
@[expose] def canonChecked (G : Colored n k) : Colored n k :=
  (canonicalizeChecked G).form

/-- The label producing the certificate-checked canonical form. -/
@[expose] def labelChecked (G : Colored n k) : Label n :=
  (canonicalizeChecked G).label

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabelChecked_label (G : Colored n k) : G.relabel (labelChecked G) = canonChecked G :=
  Nauty.canonicalizeSpec_relabel G

/-- The canonical form has contiguous colour cells in their original
order. -/
theorem colorSorted_canonChecked (G : Colored n k) : ColorSorted (canonChecked G) := by
  rw [ColorSorted]
  intro i j hij
  rw [show canonChecked G = Nauty.specCanon G from
    Nauty.canonicalizeSpec_form G]
  have hkv : ∀ (x : Fin n),
      ((Nauty.specCanon G).coloring.cells[x]).val =
        (Nauty.sortedColorSeq G)[x.val]! := by
    intro x
    rw [Nauty.specCanon]
    simp only [Nauty.formOfKey, Fin.getElem_fin,
      Hex.Vector.getElem_ofFn']
  rw [Fin.le_def, hkv i, hkv j]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hij) with he | hlt
  · rw [he]
    exact Nat.le_refl _
  · have hp := Nauty.pairwise_sortedColorSeq G
    rw [List.pairwise_iff_getElem] at hp
    have hlen := Nauty.length_sortedColorSeq G
    have := hp i.val j.val (by omega) (by
      have := j.isLt
      omega) hlt
    rw [getElem!_pos _ _ (by
        have := i.isLt
        omega),
      getElem!_pos _ _ (by
        have := j.isLt
        omega)]
    exact this

/-- Every coloured graph is isomorphic to its canonical form. -/
theorem canonChecked_iso (G : Colored n k) : Isomorphic G (canonChecked G) :=
  Nauty.canonicalizeSpec_iso G

/-- Isomorphic coloured graphs have equal canonical forms. -/
theorem canonChecked_invariant {G H : Colored n k} (h : Isomorphic G H) :
    canonChecked G = canonChecked H :=
  Nauty.canonicalizeSpec_invariant h

/-- Two coloured graphs are isomorphic exactly when their canonical forms
are equal. The biconditional compares canonical coloured graphs, not the
labels: label arrays refer to different input vertex names and generally
differ for isomorphic inputs. -/
theorem iso_iff_canonChecked_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ canonChecked G = canonChecked H :=
  Nauty.iso_iff_canonicalizeSpec_eq

/-! # The fast surface

The short names are the certificate-free production surface: the
checked-label transcription of nauty's search, total via fallback to
the checked pipeline on the never-observed malformed-label case. No
canonical-invariance theorem is stated here — that isomorphic graphs
receive equal `canon` forms is pinned by conformance against real
nauty and by the `canonicalize == canonicalizeChecked` agreement
guards, not by a Lean proof; provers use the `Checked` surface. What
is structurally provable is stated: the form is the relabelling by
the label, and a found transporter is a genuine isomorphism. -/

/-- The transcription's canonical result: `none` only if the raw
search output fails the label check, which conformance shows does not
occur. Use this to observe whether `canonicalize` would fall back. -/
@[expose] def canonicalize? (G : Colored n k) :
    Option (CanonResult n k) :=
  Nauty.canonicalize? G

/-- Compute the canonical form of a coloured graph together with the
label producing it, fast: the checked-label transcription, falling
back to `canonicalizeChecked` on the transcription's never-observed
malformed-label case (`canonicalize?` detects it). Agreement with the
checked surface is proven whenever the certificate replay accepts
(`canonicalize_eq_canonicalizeChecked`) and conformance-pinned
unconditionally. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  match Nauty.canonicalize? G with
  | some r => r
  | none => canonicalizeChecked G

/-- The canonical form of a coloured graph. -/
@[expose] def canon (G : Colored n k) : Colored n k :=
  (canonicalize G).form

/-- The label producing the canonical form. -/
@[expose] def label (G : Colored n k) : Label n :=
  (canonicalize G).label

private theorem canonicalize?_relabel {G : Colored n k}
    {r : CanonResult n k} (h : Nauty.canonicalize? G = some r) :
    G.relabel r.label = r.form := by
  rw [Nauty.canonicalize?, Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hr⟩ := h
  rw [← hr]

/-- Relabelling by the label produces the form: structurally for the
transcription, by the checked theorem for the fallback. -/
theorem relabel_label (G : Colored n k) :
    G.relabel (label G) = canon G := by
  rw [label, canon, canonicalize]
  rcases h : Nauty.canonicalize? G with _ | r
  · exact relabelChecked_label G
  · exact canonicalize?_relabel h

/-- The fast and checked tiers agree whenever the certificate replay
accepts, which is every observed run: both construct their result
from the same transcribed search output, so the checked tier's
per-run validation covers the fast answer too. Unconditional
agreement would amount to verifying the pruned search itself; on the
never-observed replay-rejection case the checked tier instead falls
back to the exhaustive spec. -/
theorem canonicalize_eq_canonicalizeChecked {G : Colored n k}
    (h : (Nauty.certifyCanon? G).isSome) :
    canonicalize G = canonicalizeChecked G := by
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp h
  have hfast := Nauty.canonicalize?_eq_of_certifyCanon hres
  have hchecked : canonicalizeChecked G = res := by
    rw [canonicalizeChecked, Nauty.canonicalizeSpec, hres]
  rw [canonicalize, hfast, hchecked]

/-- Find one isomorphism when the fast canonical forms agree: the
forward transporter through the two labels. -/
@[expose] def findIso (G H : Colored n k) : Option (Perm n) :=
  if canon G = canon H then
    some (((label H).toPerm.inv).comp ((label G).toPerm))
  else
    none

/-- The fast Boolean isomorphism decision. `false` is
conformance-pinned, not proven: use `isIsoChecked` where a `false`
answer must carry a proof. -/
@[expose] def isIso (G H : Colored n k) : Bool :=
  (findIso G H).isSome

/-- A found fast transporter is a genuine isomorphism. -/
theorem findIso_sound {G H : Colored n k} {p : Perm n}
    (h : findIso G H = some p) : IsIso G H p := by
  rw [findIso] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canon G) (label G).toPerm := by
      rw [← relabel_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canon G) (label H).toPerm := by
      rw [hc, ← relabel_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

/-- One-way soundness: a positive fast answer proves isomorphism. -/
theorem isomorphic_of_isIso {G H : Colored n k}
    (h : isIso G H = true) : Isomorphic G H := by
  rw [isIso] at h
  rcases hf : findIso G H with _ | p
  · rw [hf] at h
    simp at h
  · exact Isomorphic.intro p (findIso_sound hf)

/-! # Isomorphism search -/

/-- Find one isomorphism from `G` to `H` when one exists: the forward
transporter through the two canonical forms, the canonical label of `H`
composed with the inverse of the canonical label of `G` (in forward
permutation convention). -/
@[expose] def findIsoChecked (G H : Colored n k) : Option (Perm n) :=
  if canonChecked G = canonChecked H then
    some (((labelChecked H).toPerm.inv).comp ((labelChecked G).toPerm))
  else
    none

/-- The certificate-checked Boolean isomorphism decision. -/
@[expose] def isIsoChecked (G H : Colored n k) : Bool :=
  (findIsoChecked G H).isSome

theorem findIsoChecked_sound {G H : Colored n k} {p : Perm n}
    (h : findIsoChecked G H = some p) : IsIso G H p := by
  rw [findIsoChecked] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canonChecked G) (labelChecked G).toPerm := by
      rw [← relabelChecked_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canonChecked G) (labelChecked H).toPerm := by
      rw [hc, ← relabelChecked_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

theorem findIsoChecked_isSome_iff (G H : Colored n k) :
    (findIsoChecked G H).isSome = true ↔ Isomorphic G H := by
  rw [findIsoChecked]
  split
  · simpa using (iso_iff_canonChecked_eq G H).mpr (by assumption)
  · rename_i hc
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun h => hc ((iso_iff_canonChecked_eq G H).mp h)

theorem isIsoChecked_eq_true_iff (G H : Colored n k) :
    isIsoChecked G H = true ↔ Isomorphic G H :=
  findIsoChecked_isSome_iff G H

theorem isIsoChecked_eq_false_iff (G H : Colored n k) :
    isIsoChecked G H = false ↔ ¬Isomorphic G H := by
  rw [← isIsoChecked_eq_true_iff]
  rcases h : isIsoChecked G H <;> simp

/-! # Bounded operations -/

/-- Bounded isomorphism search. Outer `none` is exhaustion; `some none` is
a completed non-isomorphism result; `some (some p)` is a found
transporter. Exhaustion is not evidence of non-isomorphism. The
conservative pre-check charges the worst case for each of the two
canonicalizations. -/
@[expose] def findIso? (search : SearchLimits) (G H : Colored n k) :
    Option (Option (Perm n)) :=
  if 2 * searchCost n ≤ search.maxNodes then some (findIsoChecked G H) else none

namespace FindIso

theorem some_sound (search : SearchLimits) (G H : Colored n k) (p : Perm n)
    (h : findIso? search G H = some (some p)) : IsIso G H p := by
  rw [findIso?] at h
  split at h
  · exact findIsoChecked_sound (Option.some.inj h)
  · simp at h

theorem none_sound (search : SearchLimits) (G H : Colored n k)
    (h : findIso? search G H = some none) : ¬Isomorphic G H := by
  rw [findIso?] at h
  split at h
  · intro hiso
    have := (findIsoChecked_isSome_iff G H).mpr hiso
    rw [Option.some.inj h] at this
    simp at this
  · simp at h

end FindIso

/-! # Canonical certificates -/

/-- A canonical certificate: the replayed tree shape, the claimed best
key, and the achieving labelling. Plain data; the checker recomputes
partitions, codes, and comparisons from the graph. -/
structure CanonCert (n k : Nat) where
  /-- The pruned tree the producer visited. -/
  tree : Nauty.CertNode
  /-- The claimed canonical key. -/
  key : Nauty.Key
  /-- The labelling achieving the key. -/
  lab : Array Nat

/-- Produce a canonical certificate from the branch-and-bound search.
`none` on exhaustion. The certificate is UNVALIDATED here — the
producer/checker split puts the sole trusted replay in `checkCanon`,
so a candidate a buggy producer would emit is rejected there rather
than replayed twice. The conservative pre-check charges `maxNodes`
the worst case; `maxCertNodes` is checked against the record count of
the certificate actually produced. -/
@[expose] def certify? (limits : SearchLimits) (G : Colored n k) :
    Option (CanonCert n k) :=
  if searchCost n ≤ limits.maxNodes then
    match
      (if n == 0 then some ((.leaf : Nauty.CertNode), (⟨[], []⟩ : Nauty.Key))
       else Nauty.produceCand G none) with
    | none => none
    | some (cert, B) =>
      if cert.size ≤ limits.maxCertNodes then
        some ⟨cert, B, (Nauty.runColored G).canonlab⟩
      else
        none
  else
    none

/-- Replay a canonical certificate against the graph. The replay is
charged one `checkCost n` per certificate record, plus one for the
achieving-labelling validation. -/
@[expose] def checkCanon (limits : ReplayLimits) (G : Colored n k)
    (cert : CanonCert n k) : Option (CanonResult n k) :=
  if (cert.tree.size + 1) * checkCost n ≤ limits.maxCheckerSteps then
    Nauty.checkCanon G cert.tree cert.key cert.lab
  else
    none

theorem checkCanon_sound {limits : ReplayLimits} {G : Colored n k}
    {cert : CanonCert n k} {result : CanonResult n k}
    (h : checkCanon limits G cert = some result) :
    result.form = canonChecked G ∧ G.relabel result.label = result.form := by
  rw [checkCanon] at h
  split at h
  · refine ⟨?_, (Nauty.checkCanon_sound h).2.1.symm⟩
    rw [Nauty.checkCanon_form h,
      show canonChecked G = Nauty.specCanon G from
        Nauty.canonicalizeSpec_form G]
  · simp at h

/-- A checked certificate's key is the spec key. -/
theorem checkCanon_key {limits : ReplayLimits} {G : Colored n k}
    {cert : CanonCert n k} {result : CanonResult n k}
    (h : checkCanon limits G cert = some result) :
    Nauty.canonSpecKey G = cert.key := by
  rw [checkCanon] at h
  split at h
  · exact (Nauty.checkCanon_sound h).1
  · simp at h

/-- Bounded canonicalization: certificate production under the search
limits followed by replay under the replay limits, so every limit is
consulted. `none` is exhaustion (or an untrusted-search failure); the
unbounded `canonicalize` remains the total operation. -/
@[expose] def canon? (search : SearchLimits) (replay : ReplayLimits)
    (G : Colored n k) : Option (CanonResult n k) :=
  match certify? search G with
  | some cert => checkCanon replay G cert
  | none => none

theorem canon?_eq_some {search : SearchLimits} {replay : ReplayLimits}
    {G : Colored n k} {result : CanonResult n k}
    (h : canon? search replay G = some result) :
    result.form = canonChecked G ∧ G.relabel result.label = result.form := by
  rw [canon?] at h
  split at h
  · exact checkCanon_sound h
  · simp at h

/-! # Difference certificates -/

/-- A difference certificate: two canonical certificates whose keys
differ at some position. -/
structure DiffCert (n k : Nat) where
  /-- The certificate for the left graph. -/
  left : CanonCert n k
  /-- The certificate for the right graph. -/
  right : CanonCert n k

/-- Verify the two canonical keys differ: the lexicographic comparison
finds the first differing entry. -/
@[expose] def checkDiff (d : DiffCert n k) : Bool :=
  Nauty.checkDiff d.left.key d.right.key

/-- Two checked certificates and a verified difference prove
non-isomorphism. -/
theorem checkDiff_not_isomorphic {l1 l2 : ReplayLimits}
    {G H : Colored n k} {d : DiffCert n k} {r1 r2 : CanonResult n k}
    (h1 : checkCanon l1 G d.left = some r1)
    (h2 : checkCanon l2 H d.right = some r2)
    (hd : checkDiff d = true) : ¬Isomorphic G H :=
  Nauty.not_isomorphic_of_key_ne (checkCanon_key h1)
    (checkCanon_key h2) (Nauty.checkDiff_sound hd)

end Hex.GraphIso
