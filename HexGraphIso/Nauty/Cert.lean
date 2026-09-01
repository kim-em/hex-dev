/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SpecIso

public section

/-!
Canonical certificates for the nauty-semantic search, after Banković,
Drecun, and Marić. A certificate records the shape of the pruned tree
the producer visited; the checker replays each recorded node against
the specification (`specNode`), justifying every pruned sibling either
by code dominance or by a checked automorphism, and concludes that the
claimed leaf key is `canonSpecKey`.

This file provides the order and structural lemmas the checker's
soundness argument composes: bounds for `keysMax`, first-difference
comparisons of code lists, the head code of every spec key, and the
automorphism transport between sibling subtrees.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # The key order: `≤` and bounds -/

/-- `k1 ≤ k2` in the leaf-key order. -/
@[expose] def keyLe (k1 k2 : Key) : Prop := keyCmp k1 k2 ≠ .gt

theorem keyLe_iff {a b : Key} : keyLe a b ↔ keyCmp b a ≠ .lt := by
  rw [keyLe]
  constructor
  · intro h hlt
    exact h (keyCmp_gt_iff_lt.mpr hlt)
  · intro h hgt
    exact h (keyCmp_gt_iff_lt.mp hgt)

theorem keyLe_refl (x : Key) : keyLe x x := by
  rw [keyLe, keyCmp_self]
  intro h
  cases h

theorem keyLe_of_eq {a b : Key} (h : a = b) : keyLe a b := by
  rw [h]
  exact keyLe_refl b

theorem keyLe_trans {a b c : Key} (h1 : keyLe a b) (h2 : keyLe b c) :
    keyLe a c :=
  keyLe_iff.mpr (keyCmp_ge_trans (keyLe_iff.mp h2) (keyLe_iff.mp h1))

theorem keyLe_antisym {a b : Key} (h1 : keyLe a b) (h2 : keyLe b a) :
    a = b :=
  keyCmp_antisym (keyLe_iff.mp h2) (keyLe_iff.mp h1)

theorem keysMax_le {b k : Key} {l : List Key} (hk : keyLe k b)
    (hl : ∀ y ∈ l, keyLe y b) : keyLe (keysMax k l) b := by
  rcases keysMax_mem l k with h | h
  · rw [h]
    exact hk
  · exact hl _ h

theorem keyLe_keysMax {y k : Key} {l : List Key}
    (hy : y = k ∨ y ∈ l) : keyLe y (keysMax k l) :=
  keyLe_iff.mpr (keysMax_ge l k y hy)

theorem keysMax_eq_of_le {b k : Key} {l : List Key}
    (hk : keyLe k b) (hl : ∀ y ∈ l, keyLe y b)
    (hb : b = k ∨ b ∈ l) : keysMax k l = b :=
  keyLe_antisym (keysMax_le hk hl) (keyLe_keysMax hb)

/-! # First-difference comparisons of code lists -/

theorem keyCmp_cons_lt {c c' : Nat} (h : c < c') (cs cs' : List Nat)
    (r r' : List Nat) :
    keyCmp ⟨c :: cs, r⟩ ⟨c' :: cs', r'⟩ = .lt := by
  rw [keyCmp]
  have hcc : compare c c' = .lt := Nat.compare_eq_lt.mpr h
  simp only [listCmp, hcc]

theorem keyCmp_cons_gt {c c' : Nat} (h : c' < c) (cs cs' : List Nat)
    (r r' : List Nat) :
    keyCmp ⟨c :: cs, r⟩ ⟨c' :: cs', r'⟩ = .gt := by
  rw [keyCmp]
  have hcc : compare c c' = .gt := Nat.compare_eq_gt.mpr h
  simp only [listCmp, hcc]

theorem keyCmp_cons_eq (c : Nat) (cs cs' : List Nat)
    (r r' : List Nat) :
    keyCmp ⟨c :: cs, r⟩ ⟨c :: cs', r'⟩ =
      keyCmp ⟨cs, r⟩ ⟨cs', r'⟩ := by
  rw [keyCmp, keyCmp]
  have hcc : compare c c = Ordering.eq := by
    simp [Nat.compare_eq_eq]
  simp only [listCmp, hcc]

/-! # Every spec key starts with the node's refinement code -/

theorem specNode_codes_head (ctx : Ctx) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active numcells : Nat) :
    ∃ rest, (specNode ctx tcLevel (fuel + 1) level lab ptn active
      numcells).codes =
      (refine ctx level lab ptn active numcells).longcode :: rest := by
  rw [specNode]
  rcases hdisc : discreteAt (refine ctx level lab ptn active
      numcells).ptn level ctx.n with _ | _
  · simp only [Bool.false_eq_true, if_false]
    obtain ⟨m, hm⟩ : ∃ m, (specMaketargetcell ctx
        (refine ctx level lab ptn active numcells).lab
        (refine ctx level lab ptn active numcells).ptn level
          tcLevel).2.2 = m + 1 :=
      ⟨cellEnd (refine ctx level lab ptn active numcells).ptn level
        (specTargetcell ctx
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn level
            tcLevel + 1) -
        specTargetcell ctx
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn level
            tcLevel, rfl⟩
    rw [hm, List.range_succ_eq_map, List.map_cons]
    exact ⟨_, rfl⟩
  · simp only [if_true]
    exact ⟨[codeSentinel], rfl⟩

/-! # Automorphism transport between sibling subtrees -/

/-- If `γ` fixes the adjacency rows and carries the cells of `lab₂` to
the cells of `lab₁`, the two subtrees produce the same key. -/
theorem specNode_autom {ctx : Ctx} (hn : ctx.n = n) {γ : Renaming n}
    (hg : RowsMap γ ctx.g ctx.g) (tcLevel fuel level : Nat)
    {lab₁ lab₂ ptn : Array Nat} {active numcells : Nat}
    (hcp : cellsPerm ptn level lab₁ (lab₂.map γ.toFun))
    (hs1 : lab₁.size = n) (hs2 : lab₂.size = n)
    (hok1 : LabOk lab₁ n) (hok2 : LabOk lab₂ n)
    (hsp : ptn.size = n) (hact : active < 2 ^ n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, elem active v = true →
      v = 0 ∨ ptn[v - 1]! ≤ level)
    (hvals : ∀ q : Nat, ptn[q]! ≤ level ∨ ptn[q]! = n + 2)
    (hlf : level + fuel ≤ n + 1) :
    specNode ctx tcLevel fuel level lab₂ ptn active numcells =
      specNode ctx tcLevel fuel level lab₁ ptn active numcells := by
  have h1 := specNode_map γ (ctx := ctx) (ctx' := ctx) hn hn hg
    tcLevel fuel level lab₂ ptn active numcells hs2 hok2 hsp hact hend
  have hokm : LabOk (lab₂.map γ.toFun) n := by
    intro i hi
    rw [Array.size_map] at hi
    rw [getElem!_map_of_lt _ _ hi]
    exact (γ.maps _).mp (hok2 i hi)
  have h2 := specNode_perm hn tcLevel fuel level lab₁
    (lab₂.map γ.toFun) ptn active numcells hcp
    (by rw [Array.size_map]; omega) hs1 hok1 hokm hsp hact hend
    hstarts hvals hlf
  exact h1.symm.trans h2.symm

/-! # Recognizing cell equivalence from the enumerated cells -/

theorem isCell_mem_cells {ptn : Array Nat} {level a len nn : Nat}
    (h : IsCell ptn level a len) (hnn : nn ≤ ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (ha : a < nn) :
    (a, a + len - 1) ∈ cells ptn level nn := by
  obtain ⟨p, hpm, hp1, hp2⟩ := cells_cover a ha
  have hpc := cells_isCell hnn hend p hpm
  have hple := cells_le p hpm
  have hlen0 := h.1
  rcases isCell_disjoint_or_eq h hpc with hd | hd | hd
  · omega
  · omega
  · have hpe : (a, a + len - 1) = p := by
      rcases p with ⟨p1, p2⟩
      simp only [Prod.mk.injEq]
      simp only at hd hp1 hp2 hple
      omega
    rw [hpe]
    exact hpm

theorem cellsPerm_of_forall_cells {ptn lab₁ lab₂' : Array Nat}
    {level : Nat} (hsp : ptn.size = n) (hs1 : lab₁.size = n)
    (hs2 : lab₂'.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hcells : ∀ p ∈ cells ptn level n,
      (segN lab₁ p.1 (p.2 + 1 - p.1)).Perm
        (segN lab₂' p.1 (p.2 + 1 - p.1))) :
    cellsPerm ptn level lab₁ lab₂' := by
  intro a len hcell
  have hlen0 := hcell.1
  have hendn : ptn[n - 1]! ≤ level := by
    rw [← hsp] at *
    exact hend
  rcases Nat.lt_or_ge a n with han | han
  · have hain : a + len ≤ n := by
      rcases Nat.lt_or_ge (a + len) (n + 1) with h1 | h1
      · omega
      · exfalso
        have hi := hcell.2.2.1 (n - 1) (by omega) (by omega)
        omega
    have hmem := isCell_mem_cells hcell (by omega) hend han
    have hp := hcells _ hmem
    have hp2 : (segN lab₁ a (a + len - 1 + 1 - a)).Perm
        (segN lab₂' a (a + len - 1 + 1 - a)) := hp
    rw [show a + len - 1 + 1 - a = len from by omega] at hp2
    exact hp2
  · have hlen1 : len = 1 := by
      rcases Nat.lt_or_ge len 2 with h2 | h2
      · omega
      · exfalso
        have hi := hcell.2.2.1 a (Nat.le_refl a) (by omega)
        rw [getElem!_neg _ _ (by omega)] at hi
        have hd : (default : Nat) = 0 := rfl
        omega
    subst hlen1
    rw [show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_cons,
      segN_zero, segN_zero, getElem!_neg _ _ (by omega),
      getElem!_neg _ _ (by omega)]

/-! # Checked automorphisms -/

theorem image_congr {f f' : Nat → Nat} (s : Nat)
    (h : ∀ v, v < n → f v = f' v) :
    image f n s = image f' n s := by
  rw [image, image]
  have hgen : ∀ (l : List Nat) (t : Nat), (∀ v ∈ l, f v = f' v) →
      l.foldl (fun t v => if s.testBit v then insert t (f v) else t)
        t =
      l.foldl (fun t v => if s.testBit v then insert t (f' v) else t)
        t := by
    intro l
    induction l with
    | nil => intro t _; rfl
    | cons v rest ih =>
      intro t hl
      rw [List.foldl_cons, List.foldl_cons,
        hl v (List.mem_cons.mpr (Or.inl rfl))]
      exact ih _ fun w hw => hl w (List.mem_cons.mpr (Or.inr hw))
  exact hgen _ 0 fun v hv => h v (List.mem_range.mp hv)

/-- Executable check that `γ` names an automorphism of the rows `g`:
a permutation of `[0, n)` whose induced row transport fixes `g`. -/
@[expose] def checkAutom (g γ : Array Nat) (n : Nat) : Bool :=
  γ.size == n &&
  ((List.range n).all fun v => γ[v]! < n) &&
  (((List.range n).map fun v => γ[v]!).isPerm (List.range n)) &&
  ((List.range n).all fun v =>
    g[γ[v]!]! == image (fun w => γ[w]!) n g[v]!)

/-- The renaming named by a checked automorphism array. -/
@[expose] def renamingOfArray (γ : Array Nat) (n : Nat)
    (hbound : ∀ v, v < n → γ[v]! < n)
    (hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b) :
    Renaming n where
  toFun v := if v < n then γ[v]! else v
  inj a b hab := by
    rcases Decidable.em (a < n) with ha | ha <;>
      rcases Decidable.em (b < n) with hb | hb
    · rw [if_pos ha, if_pos hb] at hab
      exact hinj a b ha hb hab
    · rw [if_pos ha, if_neg hb] at hab
      exact absurd (hbound a ha) (by omega)
    · rw [if_neg ha, if_pos hb] at hab
      exact absurd (hbound b hb) (by omega)
    · rw [if_neg ha, if_neg hb] at hab
      exact hab
  maps v := by
    rcases Decidable.em (v < n) with h | h
    · rw [if_pos h]
      exact ⟨fun _ => hbound v h, fun _ => h⟩
    · rw [if_neg h]

theorem checkAutom_sound {g γ : Array Nat} (hg : g.size = n)
    (h : checkAutom g γ n = true) :
    ∃ σ : Renaming n, (∀ v, v < n → σ v = γ[v]!) ∧ RowsMap σ g g := by
  rw [checkAutom] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsize, hbound⟩, hperm⟩, hrows⟩ := h
  have hbound' : ∀ v, v < n → γ[v]! < n := by
    intro v hv
    have := List.all_eq_true.mp hbound v (List.mem_range.mpr hv)
    simpa using this
  have hnodup : (((List.range n).map fun v => γ[v]!)).Nodup :=
    ((List.isPerm_iff.mp hperm).symm.nodup List.nodup_range)
  have hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
    intro a b ha hb hab
    have hga : ((List.range n).map fun v => γ[v]!)[a]! = γ[a]! := by
      rw [getElem!_pos _ _ (by simpa using ha), List.getElem_map,
        List.getElem_range]
    have hgb : ((List.range n).map fun v => γ[v]!)[b]! = γ[b]! := by
      rw [getElem!_pos _ _ (by simpa using hb), List.getElem_map,
        List.getElem_range]
    exact (List.Nodup.getElem!_inj (by simpa using ha)
      (by simpa using hb) hnodup).mp (by rw [hga, hgb]; exact hab)
  refine ⟨renamingOfArray γ n hbound' hinj, fun v hv => ?_, hg, hg,
    fun v hv => ?_⟩
  · show (if v < n then γ[v]! else v) = γ[v]!
    rw [if_pos hv]
  · have hrv := List.all_eq_true.mp hrows v (List.mem_range.mpr hv)
    have hrv' : g[γ[v]!]! = image (fun w => γ[w]!) n g[v]! := by
      simpa using hrv
    have hσv : renamingOfArray γ n hbound' hinj v = γ[v]! := by
      show (if v < n then γ[v]! else v) = γ[v]!
      rw [if_pos hv]
    rw [hσv, hrv']
    exact (image_congr _ fun w hw => by
      show (if w < n then γ[w]! else w) = γ[w]!
      rw [if_pos hw]).symm

/-- Executable check that two labellings fill each cell of `ptn` with
the same vertices. -/
@[expose] def checkCellsPerm (ptn lab₁ lab₂' : Array Nat)
    (level nn : Nat) : Bool :=
  (cells ptn level nn).all fun p =>
    (segN lab₁ p.1 (p.2 + 1 - p.1)).isPerm
      (segN lab₂' p.1 (p.2 + 1 - p.1))

theorem checkCellsPerm_sound {ptn lab₁ lab₂' : Array Nat}
    {level : Nat} (hsp : ptn.size = n) (hs1 : lab₁.size = n)
    (hs2 : lab₂'.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (h : checkCellsPerm ptn lab₁ lab₂' level n = true) :
    cellsPerm ptn level lab₁ lab₂' := by
  refine cellsPerm_of_forall_cells hsp hs1 hs2 hend fun p hp => ?_
  have := List.all_eq_true.mp h p hp
  exact List.isPerm_iff.mp (by simpa using this)

/-! # The certificate and its checker -/

/-- One node of a canonical certificate: the shape of the pruned
search tree the producer visited. Prune variants justify discarding a
subtree; `node` lists one entry per position of the target cell. -/
inductive CertNode where
  /-- The replayed state is discrete; compare its leaf key with the
  claimed best. -/
  | leaf : CertNode
  /-- The subtree's refinement code falls below the best code at this
  depth. -/
  | codePrune : CertNode
  /-- `γ` maps this subtree onto the earlier sibling at offset `o`. -/
  | autom (o : Nat) (γ : Array Nat) : CertNode
  /-- Recurse into every position of the target cell. -/
  | node (children : List CertNode) : CertNode

mutual

/-- Replay one node of the certificate. `⟨bcodes, brows⟩` is the
claimed best key's suffix at this depth. Returns `none` if the replay
fails, otherwise `some achieved` where `achieved` records whether this
subtree attains the claimed best. Success certifies that every leaf
key of the subtree is `≤` the claimed suffix. -/
def checkNode (ctx : Ctx) (tcLevel : Nat) (brows : List Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → CertNode →
      List Nat → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes =>
    match bcodes with
    | [] => none
    | bc :: brest =>
      match cert with
      | .autom _ _ => none
      | .codePrune =>
        if compare (refine ctx level lab ptn active
            numcells).longcode bc = .lt then
          some false
        else
          none
      | .leaf =>
        match compare (refine ctx level lab ptn active
            numcells).longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAt (refine ctx level lab ptn active
              numcells).ptn level ctx.n then
            match keyCmp
              ⟨[(refine ctx level lab ptn active numcells).longcode,
                codeSentinel],
                leafRows ctx (refine ctx level lab ptn active
                  numcells).lab⟩
              ⟨bc :: brest, brows⟩ with
            | .gt => none
            | .eq => some true
            | .lt => some false
          else
            none
      | .node children =>
        match compare (refine ctx level lab ptn active
            numcells).longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAt (refine ctx level lab ptn active
              numcells).ptn level ctx.n then
            none
          else
            if children.length = (specMaketargetcell ctx
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn level
                  tcLevel).2.2 then
              checkChildren ctx tcLevel brows fuel level
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                (specMaketargetcell ctx
                  (refine ctx level lab ptn active numcells).lab
                  (refine ctx level lab ptn active numcells).ptn
                  level tcLevel).1
                numcells brest children 0
            else
              none

/-- Replay the children of a node from offset `o` on. -/
def checkChildren (ctx : Ctx) (tcLevel : Nat) (brows : List Nat)
    (fuel level : Nat) (rsLab rsPtn : Array Nat) (tc numcells : Nat)
    (brest : List Nat) : List CertNode → Nat → Option Bool
  | [], _ => some false
  | c :: rest, o =>
    let sub : Option Bool :=
      match c with
      | .autom o' γ =>
        if o' < o &&
            checkAutom ctx.g γ ctx.n &&
            checkCellsPerm
              (breakout rsLab rsPtn (level + 1) tc
                rsLab[tc + o]!).2.1
              (breakout rsLab rsPtn (level + 1) tc
                rsLab[tc + o']!).1
              ((breakout rsLab rsPtn (level + 1) tc
                rsLab[tc + o]!).1.map fun w => γ[w]!)
              (level + 1) ctx.n then
          some false
        else
          none
      | _ =>
        checkNode ctx tcLevel brows fuel (level + 1)
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
          (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
          (numcells + 1) c brest
    match sub with
    | none => none
    | some a =>
      match checkChildren ctx tcLevel brows fuel level rsLab rsPtn tc
          numcells brest rest (o + 1) with
      | none => none
      | some a' => some (a || a')

end

/-- Replay a whole certificate against the claimed best key `B`. -/
@[expose] def checkKey (G : Colored n k) (cert : CertNode) (B : Key) :
    Bool :=
  if n == 0 then
    B.codes == [] && B.rows == []
  else
    checkNode { n := n, g := rowsOf G } 100 B.rows n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length cert B.codes = some true

end Hex.GraphIso.Nauty
