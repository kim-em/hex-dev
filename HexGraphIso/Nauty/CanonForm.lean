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

/-- The colour value at position `i` of a labelling. -/
@[expose] def labColor (G : Colored n k) (lab : Array Nat) (i : Nat) :
    Nat :=
  if h : i < lab.size ∧ lab[i]! < n then
    (G.coloring.cells[(⟨lab[i]!, h.2⟩ : Fin n)]).val
  else
    0

/-- Positions list colours in nondecreasing order. -/
@[expose] def colorSortedCheck (G : Colored n k) (lab : Array Nat) :
    Bool :=
  (List.range n).all fun i =>
    decide (i + 1 = n) ||
      decide (labColor G lab i ≤ labColor G lab (i + 1))

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
          (B.rows == leafRows { n := n, g := rowsOf G } lab) &&
          colorSortedCheck G lab then
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
        refine ⟨checkKey_sound hcond.1.1, ?_, ?_, hcond.1.2⟩
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

/-! # Correctness of the inverse labelling -/

theorem invPerm_go_size (lab : Array Nat) :
    ∀ (l : List Nat) (inv : Array Nat),
      (invPerm.go lab l inv).size = inv.size
  | [], _ => rfl
  | i :: rest, inv => by
    rw [invPerm.go, invPerm_go_size lab rest, Array.size_set!]

theorem invPerm_go_untouched (lab : Array Nat) :
    ∀ (l : List Nat) (inv : Array Nat) (w : Nat),
      (∀ j ∈ l, lab[j]! ≠ w) →
      (invPerm.go lab l inv)[w]! = inv[w]!
  | [], _, _, _ => rfl
  | j :: rest, inv, w, hl => by
    rw [invPerm.go,
      invPerm_go_untouched lab rest _ w
        (fun j' hj' => hl j' (List.mem_cons.mpr (Or.inr hj'))),
      Array.getElem!_set!_ne _ _ _ _
        (hl j (List.mem_cons.mpr (Or.inl rfl)))]

theorem invPerm_go_get (lab : Array Nat) :
    ∀ (l : List Nat) (inv : Array Nat) (i : Nat), i ∈ l →
      (∀ j ∈ l, lab[j]! = lab[i]! → j = i) →
      lab[i]! < inv.size →
      (invPerm.go lab l inv)[lab[i]!]! = i
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | j :: rest, inv, i, hi, hinj, hsz => by
    rw [invPerm.go]
    rcases Decidable.em (i ∈ rest) with hir | hir
    · exact invPerm_go_get lab rest _ i hir
        (fun j' hj' => hinj j' (List.mem_cons.mpr (Or.inr hj')))
        (by rw [Array.size_set!]; exact hsz)
    · have hij : j = i := by
        rcases List.mem_cons.mp hi with rfl | h
        · rfl
        · exact absurd h hir
      subst hij
      rw [invPerm_go_untouched lab rest _ _ (fun j' hj' he => by
        have := hinj j' (List.mem_cons.mpr (Or.inr hj')) he
        subst this
        exact hir hj')]
      exact Array.getElem!_set!_self _ _ _ hsz

theorem invPerm_size (lab : Array Nat) :
    (invPerm lab).size = lab.size := by
  rw [invPerm, invPerm_go_size, Array.size_replicate]

theorem getElem!_invPerm (lab : Array Nat)
    (hinj : ∀ a b, a < lab.size → b < lab.size →
      lab[a]! = lab[b]! → a = b)
    {i : Nat} (hi : i < lab.size) (hv : lab[i]! < lab.size) :
    (invPerm lab)[lab[i]!]! = i := by
  rw [invPerm]
  refine invPerm_go_get lab _ _ i (List.mem_range.mpr hi)
    (fun j hj he => hinj j i (List.mem_range.mp hj) hi he) ?_
  rw [Array.size_replicate]
  exact hv

theorem getElem!_invPerm_lt {lab : Array Nat} (hn0 : 0 < lab.size)
    (v : Nat) : (invPerm lab)[v]! < lab.size := by
  rw [invPerm]
  have hgen : ∀ (l : List Nat) (inv : Array Nat),
      (∀ j ∈ l, j < lab.size) →
      (∀ w : Nat, inv[w]! < lab.size) →
      ∀ w : Nat, (invPerm.go lab l inv)[w]! < lab.size := by
    intro l
    induction l with
    | nil => intro inv _ hinv w; exact hinv w
    | cons j rest ih =>
      intro inv hl hinv w
      rw [invPerm.go]
      refine ih _ (fun j' hj' => hl j' (List.mem_cons.mpr
        (Or.inr hj'))) (fun w' => ?_) w
      rcases getElem!_set!_cases inv lab[j]! j w' with he | he
      · rw [he]
        exact hinv w'
      · rw [he]
        exact hl j (List.mem_cons.mpr (Or.inl rfl))
  refine hgen _ _ (fun j hj => List.mem_range.mp hj) (fun w => ?_) v
  rcases Nat.lt_or_ge w lab.size with hw | hw
  · rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_replicate]
    exact hn0
  · rw [getElem!_neg _ _ (by simpa using hw)]
    exact hn0

/-! # Leaf rows are the relabelled graph's rows -/

theorem rowOf_relabel {G : Colored n k} {l : Label n}
    {lab : Array Nat} (hsz : lab.size = n)
    (hl : ∀ (i : Nat) (h : i < n), (l.get ⟨i, h⟩).val = lab[i]!)
    {i : Nat} (hi : i < n) :
    rowOf (G.relabel l) i =
      permset (rowsOf G)[lab[i]!]! (invPerm lab) n := by
  have hn0 : 0 < n := by omega
  have hlabl : ∀ j, j < n → lab[j]! < n := fun j hj => by
    rw [← hl j hj]
    exact (l.get ⟨j, hj⟩).isLt
  have hinj : ∀ a b, a < lab.size → b < lab.size →
      lab[a]! = lab[b]! → a = b := by
    intro a b ha hb he
    rw [hsz] at ha hb
    have hab : l.get ⟨a, ha⟩ = l.get ⟨b, hb⟩ :=
      Fin.eq_of_val_eq (by rw [hl a ha, hl b hb, he])
    exact congrArg Fin.val (l.perm.get_inj hab)
  have hsurj : ∀ v, v < n → ∃ j, j < n ∧ lab[j]! = v := by
    intro v hv
    obtain ⟨w, hw⟩ := l.perm.get_surj ⟨v, hv⟩
    refine ⟨w.val, w.isLt, ?_⟩
    rw [← hl w.val w.isLt]
    have hwe : (⟨w.val, w.isLt⟩ : Fin n) = w := Fin.eta w w.isLt
    rw [hwe]
    show (l.perm.get w).val = v
    rw [hw]
  have hps : permset (rowsOf G)[lab[i]!]! (invPerm lab) n =
      image (fun v => (invPerm lab)[v]!) n (rowsOf G)[lab[i]!]! := rfl
  rw [hps]
  refine Nat.eq_of_testBit_eq fun t => ?_
  rcases Nat.lt_or_ge t n with ht | ht
  · rw [testBit_rowOf_lt (G.relabel l) hi ht, testBit_image]
    rw [Colored.adj_relabel]
    have hgi : l.get ⟨i, hi⟩ = ⟨lab[i]!, hlabl i hi⟩ :=
      Fin.eq_of_val_eq (hl i hi)
    have hgt : l.get ⟨t, ht⟩ = ⟨lab[t]!, hlabl t ht⟩ :=
      Fin.eq_of_val_eq (hl t ht)
    rw [hgi, hgt]
    rcases hadj : G.graph.adj ⟨lab[i]!, hlabl i hi⟩
        ⟨lab[t]!, hlabl t ht⟩ with _ | _
    · -- no edge: no witness can fire
      symm
      rw [List.any_eq_false]
      intro v hv
      have hvn := List.mem_range.mp hv
      simp only [Bool.and_eq_true, beq_iff_eq, not_and]
      intro hbit hinv
      -- v = lab[t]! since invPerm is injective on the range
      obtain ⟨j, hj, hje⟩ := hsurj v hvn
      have hjt : j = t := by
        rw [← hje] at hinv
        rw [getElem!_invPerm lab hinj (by omega)
          (by rw [hje, hsz]; exact hvn)] at hinv
        exact hinv
      subst hjt
      subst hje
      rw [getElem!_rowsOf G (hlabl i hi),
        testBit_rowOf_lt G (hlabl i hi) (hlabl j hj)] at hbit
      rw [hadj] at hbit
      cases hbit
    · -- edge: the witness is lab[t]!
      symm
      rw [List.any_eq_true]
      refine ⟨lab[t]!, List.mem_range.mpr (hlabl t ht), ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rw [getElem!_rowsOf G (hlabl i hi),
          testBit_rowOf_lt G (hlabl i hi) (hlabl t ht)]
        exact hadj
      · exact getElem!_invPerm lab hinj (by omega)
          (by rw [hsz]; exact hlabl t ht)
  · -- above the vertex range both sides are clear
    rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (rowOf_lt (G.relabel l) i)
        (Nat.pow_le_pow_right (by omega) ht))]
    symm
    rw [testBit_image, List.any_eq_false]
    intro v hv
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro _ hinv
    have := getElem!_invPerm_lt (lab := lab) (by omega) v
    omega

/-- The claimed labelling's leaf rows are exactly the rows of the
relabelled graph. -/
theorem rowsOf_relabel_eq_leafRows {G : Colored n k} {l : Label n}
    {lab : Array Nat} (hsz : lab.size = n)
    (hl : ∀ (i : Nat) (h : i < n), (l.get ⟨i, h⟩).val = lab[i]!) :
    rowsOf (G.relabel l) =
      (leafRows { n := n, g := rowsOf G } lab).toArray := by
  rw [rowsOf, leafRows]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  exact rowOf_relabel hsz hl (List.mem_range.mp hi)

/-! # Determinism facts for checked forms -/

theorem ofVector?_perm_vec {v : Vector (Fin n) n} {l : Label n}
    (h : Label.ofVector? v = some l) : l.perm.vec = v := by
  rw [Label.ofVector?, Perm.ofVector?] at h
  split at h
  · simp only [Option.map_some] at h
    injection h with h'
    rw [← h']
  · simp at h

/-- Everything a successful `checkCanon` establishes, with the label's
entries pinned to the claimed array. -/
theorem checkCanon_inv {G : Colored n k} {cert : CertNode} {B : Key}
    {lab : Array Nat} {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    lab.size = n ∧
    res.form = G.relabel res.label ∧
    (∀ (i : Nat) (hi : i < n), (res.label.get ⟨i, hi⟩).val =
      lab[i]!) ∧
    checkKey G cert B = true ∧
    B.rows = leafRows { n := n, g := rowsOf G } lab ∧
    colorSortedCheck G lab = true := by
  rw [checkCanon] at h
  split at h
  · next hwf =>
    split at h
    · cases h
    · next l hl =>
      split at h
      · next hcond =>
        injection h with h'
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        have hvec := ofVector?_perm_vec hl
        have hlabel : res.label = l := by rw [← h']
        have hform : res.form = G.relabel l := by rw [← h']
        refine ⟨hwf.1, by rw [hform, hlabel], ?_, hcond.1.1,
          hcond.1.2, hcond.2⟩
        intro i hi
        rw [hlabel]
        have hlen : i < l.perm.vec.toList.length := by
          simpa using hi
        show (l.perm.get ⟨i, hi⟩).val = lab[i]!
        have h2 : l.perm.get ⟨i, hi⟩ = l.perm.vec.toList[i]'hlen :=
          (Perm.get_toList l.perm ⟨i, hi⟩).symm
        have h1 : l.perm.vec.toList =
            (⟨lab.attach.map fun v =>
              (⟨v.val, hwf.2 v.val v.property⟩ : Fin n), by
                simp [hwf.1]⟩ : Vector (Fin n) n).toList :=
          congrArg Vector.toList hvec
        rw [h2, List.getElem_of_eq h1 hlen]
        have hasz : i < (lab.attach.map fun v =>
            (⟨v.val, hwf.2 v.val v.property⟩ : Fin n)).size := by
          rw [Array.size_map, Array.size_attach]
          omega
        show (((lab.attach.map fun v =>
          (⟨v.val, hwf.2 v.val v.property⟩ : Fin n))[i]'hasz)).val =
          lab[i]!
        rw [Array.getElem_map]
        show (lab.attach[i]'(by rw [Array.size_attach]; omega)).val =
          lab[i]!
        rw [Array.getElem_attach]
        exact (getElem!_pos lab i (by omega)).symm
      · cases h
  · cases h

/-- The rows of a checked canonical form are the key's rows. -/
theorem checkCanon_rows {G : Colored n k} {cert : CertNode} {B : Key}
    {lab : Array Nat} {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    rowsOf res.form = B.rows.toArray := by
  obtain ⟨hsz, hform, hag, _, hrows, _⟩ := checkCanon_inv h
  rw [hform, rowsOf_relabel_eq_leafRows hsz hag, hrows]

/-- The colours of a checked canonical form are nondecreasing along
the vertex order. -/
theorem checkCanon_sorted {G : Colored n k} {cert : CertNode}
    {B : Key} {lab : Array Nat} {res : CanonResult n k}
    (h : checkCanon G cert B lab = some res) :
    ∀ (i : Nat) (hi1 : i + 1 < n),
      (res.form.coloring.cells[i]'(by omega)).val ≤
        (res.form.coloring.cells[i + 1]'(by omega)).val := by
  obtain ⟨hsz, hform, hag, _, _, hsort⟩ := checkCanon_inv h
  intro i hi1
  have hi : i < n := by omega
  have hs := List.all_eq_true.mp hsort i (List.mem_range.mpr hi)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
  rcases hs with hs | hs
  · omega
  · have hcell : ∀ (j : Nat) (hj : j < n),
        (res.form.coloring.cells[j]'(by omega)).val =
          labColor G lab j := by
      intro j hj
      rw [hform]
      rw [Colored.cells_relabel G res.label j hj]
      have hbound : lab[j]! < n := by
        rw [← hag j hj]
        exact (res.label.get ⟨j, hj⟩).isLt
      rw [labColor, dif_pos ⟨by omega, hbound⟩]
      congr 2
      exact Fin.eq_of_val_eq (hag j hj)
    rw [hcell i hi, hcell (i + 1) hi1]
    exact hs

/-! # Checked forms with equal keys are equal -/

theorem pairwise_le_of_adjacent {f : Nat → Nat} {m : Nat}
    (h : ∀ i, i + 1 < m → f i ≤ f (i + 1)) :
    ((List.range m).map f).Pairwise (· ≤ ·) := by
  have mono : ∀ d i, i + d < m → f i ≤ f (i + d) := by
    intro d
    induction d with
    | zero => intro i _; exact Nat.le_refl _
    | succ d ih =>
      intro i hi
      refine Nat.le_trans (ih i (by omega)) ?_
      have h2 := h (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 from by omega]
      exact h2
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_map, List.length_range] at hi hj
  rw [List.getElem_map, List.getElem_map, List.getElem_range,
    List.getElem_range]
  have := mono (j - i) i (by omega)
  rw [show i + (j - i) = j from by omega] at this
  exact this

/-- The colour value at each vertex, as a plain list. -/
@[expose] def colorList (K : Colored n k) : List Nat :=
  (List.range n).map (keyOf K)

theorem count_colorList (K : Colored n k) {c : Nat} (hc : c < k) :
    (colorList K).count c = (colorClass K c).length := by
  rw [colorList, List.count_eq_countP, List.countP_map,
    colorClass_eq_key hc, List.countP_eq_length_filter]
  congr 1

theorem count_colorList_ge (K : Colored n k) {c : Nat} (hc : k ≤ c) :
    (colorList K).count c = 0 := by
  rw [colorList, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter, List.length_eq_zero_iff,
    List.filter_eq_nil_iff]
  intro v hv
  have hvn := List.mem_range.mp hv
  show ¬((keyOf K v == c) = true)
  intro hb
  have hbe : keyOf K v = c := by simpa using hb
  rw [keyOf, dif_pos hvn] at hbe
  have := (K.coloring.cells[(⟨v, hvn⟩ : Fin n)]).isLt
  omega

theorem colorList_perm_of_lengths {G' H' G H : Colored n k}
    (hG : Isomorphic G G') (hH : Isomorphic H H')
    (hGH : ∀ c, c < k →
      (colorClass G c).length = (colorClass H c).length) :
    (colorList G').Perm (colorList H') := by
  rw [List.perm_iff_count]
  intro c
  rcases Nat.lt_or_ge c k with hc | hc
  · rw [count_colorList G' hc, count_colorList H' hc]
    obtain ⟨p1, hp1⟩ := hG.elim
    obtain ⟨p2, hp2⟩ := hH.elim
    rw [length_colorClass_eq hp1 c, length_colorClass_eq hp2 c]
    exact hGH c hc
  · rw [count_colorList_ge G' hc, count_colorList_ge H' hc]

/-- Two checked canonical forms with the same key and the same colour
class sizes are equal. -/
theorem checkCanon_form_eq {G H : Colored n k}
    {certG certH : CertNode} {B : Key} {labG labH : Array Nat}
    {resG resH : CanonResult n k}
    (hG : checkCanon G certG B labG = some resG)
    (hH : checkCanon H certH B labH = some resH)
    (hlen : ∀ c, c < k →
      (colorClass G c).length = (colorClass H c).length) :
    resG.form = resH.form := by
  have hrG := checkCanon_rows hG
  have hrH := checkCanon_rows hH
  have hadj : ∀ (K : Colored n k) (i j : Fin n),
      K.graph.adj i j = ((rowsOf K)[i.val]!).testBit j.val := by
    intro K i j
    rw [getElem!_rowsOf K i.isLt, testBit_rowOf_lt K i.isLt j.isLt]
  have hclG : colorList resG.form = colorList resH.form := by
    refine List.Perm.eq_of_pairwise
      (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) ?_ ?_ ?_
    · refine pairwise_le_of_adjacent fun i hi => ?_
      have hs := checkCanon_sorted hG i hi
      have hkv : ∀ (K : Colored n k) (j : Nat) (hj : j < n),
          keyOf K j = (K.coloring.cells[j]'(by omega)).val := by
        intro K j hj
        rw [keyOf, dif_pos hj]
        rfl
      rw [hkv _ i (by omega), hkv _ (i + 1) (by omega)]
      exact hs
    · refine pairwise_le_of_adjacent fun i hi => ?_
      have hs := checkCanon_sorted hH i hi
      have hkv : ∀ (K : Colored n k) (j : Nat) (hj : j < n),
          keyOf K j = (K.coloring.cells[j]'(by omega)).val := by
        intro K j hj
        rw [keyOf, dif_pos hj]
        rfl
      rw [hkv _ i (by omega), hkv _ (i + 1) (by omega)]
      exact hs
    · exact colorList_perm_of_lengths (checkCanon_sound hG).2.2.1
        (checkCanon_sound hH).2.2.1 hlen
  refine Colored.ext ?_ ?_
  · intro i j
    rw [hadj resG.form i j, hadj resH.form i j, hrG, hrH]
  · intro i
    have h1 := congrArg (fun l : List Nat => l[i.val]!) hclG
    simp only [colorList] at h1
    have hget : ∀ (K : Colored n k),
        ((List.range n).map (keyOf K))[i.val]! = keyOf K i.val := by
      intro K
      rw [getElem!_pos _ _ (by simp [i.isLt]), List.getElem_map,
        List.getElem_range]
    rw [hget, hget] at h1
    have hkv : ∀ (K : Colored n k),
        keyOf K i.val = (K.coloring.cells[i.val]'(by
          have := i.isLt
          omega)).val := by
      intro K
      rw [keyOf, dif_pos i.isLt]
      rfl
    rw [hkv, hkv] at h1
    -- from value equality to Fin equality
    exact Fin.eq_of_val_eq h1

/-! # The certificate-based positive decision -/

/-- Executable equality of colour class sizes. -/
@[expose] def cellSizesCheck (G H : Colored n k) : Bool :=
  (List.range k).all fun c =>
    (colorClass G c).length == (colorClass H c).length

theorem cellSizesCheck_sound {G H : Colored n k}
    (h : cellSizesCheck G H = true) :
    ∀ c, c < k → (colorClass G c).length = (colorClass H c).length :=
  fun c hc => by
    simpa using List.all_eq_true.mp h c (List.mem_range.mpr hc)

/-- Two checked certificates with the same key and matching colour
class sizes prove isomorphism. -/
theorem isomorphic_of_certs {G H : Colored n k}
    {certG certH : CertNode} {B : Key} {labG labH : Array Nat}
    {resG resH : CanonResult n k}
    (hG : checkCanon G certG B labG = some resG)
    (hH : checkCanon H certH B labH = some resH)
    (hcs : cellSizesCheck G H = true) : Isomorphic G H := by
  have hfe := checkCanon_form_eq hG hH (cellSizesCheck_sound hcs)
  exact ((checkCanon_sound hG).2.2.1).trans
    (hfe ▸ ((checkCanon_sound hH).2.2.1).symm)

end Hex.GraphIso.Nauty
