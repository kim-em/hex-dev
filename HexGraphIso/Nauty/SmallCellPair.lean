/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellTriple
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix

public section

/-!
The pair-closure involution (SPEC § Verified search refinement, the
code-1 arm of the store-validity obligation).

The pair deviation swaps every pair cell in the `PairMatch`-reachability
closure of the target pair at once. This file constructs that involution
(`pairFlip`: a member of a closure pair maps to its partner, every other
vertex is fixed — a `Classical.choose` over the closure, made
well-defined by the position toolkit's uniqueness facts), proves its
evaluation laws, bounds, and involutivity, and discharges the
`S`-hypotheses of `flip_rows` for it: closure pairs swap
(`pairFlip_first`/`pairFlip_second`), members of non-closure cells are
fixed (`pairFlip_fix_cell`), and the closure is `PairMatch`-closed by
construction (`PairReach.step`). The self-equivalence
(`cellsPerm_self_flip`, stated for any renaming swapping `S`-pairs and
fixing the other cells pointwise, so future flips reuse it) and the
packaged pair deviation (`pair_deviation_leafRows`, through
`deviation_leafRows_self` exactly as the triple instance) complete the
pair analogue of the triple theory.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The involution -/

section PairFlip

open Classical

variable {lab ptn : Array Nat} {level t : Nat}

/-- The involution swapping every pair in the `PairReach` closure of
`t`: a vertex that is a member of a closure pair maps to its partner,
and every other vertex is fixed. -/
noncomputable def pairFlip (ctx : Ctx n) (lab ptn : Array Nat)
    (level t : Nat) : Nat → Nat := fun v =>
  if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! then
    lab[h.choose + 1]!
  else if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! then
    lab[h.choose]!
  else v

/-- Two closure pairs sharing a first member coincide. -/
private theorem first_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c']!) : c = c' := by
  have h1 := cells_bound (by omega) hend _ hcell
  have h2 := cells_bound (by omega) hend _ hcell'
  have h1' : c + 1 < ptn.size := h1
  have h2' : c' + 1 < ptn.size := h2
  exact hinj c c' (by omega) (by omega) hv

/-- Two closure pairs sharing a second member coincide. -/
private theorem second_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c + 1]! = lab[c' + 1]!) : c = c' := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have := hinj (c + 1) (c' + 1) (by omega) (by omega) hv
  omega

/-- A first member of one pair cell is never the second member of
another. -/
private theorem first_ne_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c' + 1]!) : False := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have heq := hinj c (c' + 1) (by omega) (by omega) hv
  exact pair_start_ne_second (by omega) hend hcell hcell' heq

/-- The flip carries a closure pair's first member to its second. -/
theorem pairFlip_first (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c]! = lab[c + 1]! := by
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (first_eq hpsz hend hinj hcell hcell' hv).symm
  show (if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! then
      lab[h.choose + 1]!
    else _) = _
  rw [dite_eq_left hex]
  show lab[hex.choose + 1]! = lab[c + 1]!
  rw [hcc]

/-- The flip carries a closure pair's second member to its first. -/
theorem pairFlip_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c + 1]! = lab[c]! := by
  have hno : ¬ ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! := by
    rintro ⟨c', -, hcell', hv⟩
    exact first_ne_second hpsz hend hinj hcell' hcell hv.symm
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (second_eq hpsz hend hinj hcell hcell' hv).symm
  show (if _ : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! then _
    else if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! then lab[h.choose]!
    else _) = _
  rw [dite_eq_right hno, dite_eq_left hex]
  show lab[hex.choose]! = lab[c]!
  rw [hcc]

/-- The flip fixes every vertex that is not a closure-pair member. -/
theorem pairFlip_fix {v : Nat}
    (hnone : ∀ c, PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level n →
        v ≠ lab[c]! ∧ v ≠ lab[c + 1]!) :
    pairFlip ctx lab ptn level t v = v := by
  have h1 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).1 hv
  have h2 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).2 hv
  show (if _ : _ then _ else if _ : _ then _ else v) = v
  rw [dite_eq_right h1, dite_eq_right h2]

/-- The flip is bounded on the vertex range. -/
theorem pairFlip_lt (hpsz : ptn.size = n)
    (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hlb : LabOk lab n)
    {v : Nat} (hv : v < n) :
    pairFlip ctx lab ptn level t v < n := by
  show (if _ : _ then _ else if _ : _ then _ else v) < n
  split
  · next h =>
    obtain ⟨-, hcell, -⟩ := h.choose_spec
    have hb : (h.choose, h.choose + 1).2 < ptn.size :=
      cells_bound (by omega) hend _ hcell
    exact hlb _ (by rw [hlsz]; omega)
  · split
    · next h =>
      obtain ⟨-, hcell, -⟩ := h.choose_spec
      have hb : (h.choose, h.choose + 1).2 < ptn.size :=
        cells_bound (by omega) hend _ hcell
      exact hlb _ (by rw [hlsz]; omega)
    · exact hv

/-- The flip is an involution on the vertex range. -/
theorem pairFlip_invol (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {v : Nat} :
    pairFlip ctx lab ptn level t
      (pairFlip ctx lab ptn level t v) = v := by
  rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]!) with h1 | h1
  · obtain ⟨c, hr, hcell, rfl⟩ := h1
    rw [pairFlip_first hpsz hend hinj hr hcell,
      pairFlip_second hpsz hend hinj hr hcell]
  · rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
        (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]!) with
      h2 | h2
    · obtain ⟨c, hr, hcell, rfl⟩ := h2
      rw [pairFlip_second hpsz hend hinj hr hcell,
        pairFlip_first hpsz hend hinj hr hcell]
    · have hfix : pairFlip ctx lab ptn level t v = v := by
        refine pairFlip_fix fun c hr hcell => ⟨?_, ?_⟩
        · intro hcon
          exact h1 ⟨c, hr, hcell, hcon⟩
        · intro hcon
          exact h2 ⟨c, hr, hcell, hcon⟩
      rw [hfix, hfix]

/-- A member of a cell outside the closure is fixed by the flip: its
position would otherwise sit inside a closure pair's window. -/
theorem pairFlip_fix_cell (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {q : Nat × Nat} (hq : q ∈ cells ptn level n)
    (hnotS : ¬ PairReach ctx lab ptn level t q.1)
    {o : Nat} (ho : o < q.2 + 1 - q.1) :
    pairFlip ctx lab ptn level t lab[q.1 + o]! = lab[q.1 + o]! := by
  have hqbd : q.2 < ptn.size := cells_bound (by omega) hend _ hq
  have hqle := cells_le _ hq
  have hqIs := cells_isCell (by omega) hend _ hq
  refine pairFlip_fix fun c hr hcell => ?_
  have hcbd : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have hcIs := cells_isCell (by omega) hend _ hcell
  rw [show c + 1 + 1 - c = 2 by omega] at hcIs
  constructor
  · intro hcon
    have hpos : q.1 + o = c :=
      hinj (q.1 + o) c (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega
  · intro hcon
    have hpos : q.1 + o = c + 1 :=
      hinj (q.1 + o) (c + 1) (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega

end PairFlip

/-! # The self-equivalence of a cell flip

A renaming that swaps the labelling window of every `S`-cell (each a
pair) and fixes every other cell pointwise is a cell-contents
permutation of the labelling against itself. Stated for any renaming so
the pair closure and any future flip shapes share it. -/

section FlipSelf

variable {lab ptn : Array Nat} {level : Nat}

/-- The mapped labelling is cell-contents equivalent to the original
when the map swaps `S`-pair windows and fixes every other cell
pointwise. -/
theorem cellsPerm_self_flip {σ : Renaming n} {S : Nat → Prop}
    (hps : ptn.size = n) (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hSpair : ∀ p ∈ cells ptn level n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level n, S p.1 →
      σ.toFun lab[p.1]! = lab[p.1 + 1]! ∧
        σ.toFun lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 →
        σ.toFun lab[p.1 + o]! = lab[p.1 + o]!) :
    cellsPerm ptn level lab (lab.map σ.toFun) := by
  intro α len hIs
  rcases Decidable.em (α < n) with han | han
  · have hcross : α + len ≤ n := by
      have := isCell_no_cross hend hIs (by omega)
      omega
    have hlen0 : 0 < len := hIs.1
    have hmem : (α, α + len - 1) ∈ cells ptn level n :=
      mem_cells_of_isCell (by omega) hend hIs han (by omega)
    have hmapAt : ∀ o, o < len →
        (lab.map σ.toFun)[α + o]! = σ.toFun lab[α + o]! := by
      intro o ho
      exact getElem!_map_of_lt _ _ (by rw [hlsz]; omega)
    rcases Classical.em (S α) with hS | hS
    · -- a closure pair: the window swaps in place
      have hp2 : α + len - 1 = α + 1 := hSpair _ hmem hS
      have hlen2 : len = 2 := by omega
      subst hlen2
      have hsw := hSswap _ hmem hS
      have hs1 : σ.toFun lab[α]! = lab[α + 1]! := hsw.1
      have hs2 : σ.toFun lab[α + 1]! = lab[α]! := hsw.2
      have hseg : segN lab α 2 = lab[α]! :: lab[α + 1]! :: [] := by
        rw [show (2 : Nat) = 1 + 1 from rfl, segN_cons,
          show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_zero]
      have hsegm : segN (lab.map σ.toFun) α 2 =
          σ.toFun lab[α]! :: σ.toFun lab[α + 1]! :: [] := by
        rw [show (2 : Nat) = 1 + 1 from rfl, segN_cons,
          show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_zero,
          getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega),
          getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega)]
      rw [hseg, hsegm, hs1, hs2, Nat.add_zero]
      exact List.Perm.swap _ _ _
    · -- a fixed cell
      have hfix := hSfix _ hmem hS
      have hfixseg : segN (lab.map σ.toFun) α len =
          segN lab α len := by
        refine segN_congr fun o ho => ?_
        rw [hmapAt o ho]
        exact hfix o (by omega)
      rw [hfixseg]
  · -- beyond the bound: phantom singleton
    have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
    rw [getElem!_oob (by omega : lab.size ≤ α),
      getElem!_oob (by rw [Array.size_map]; omega :
        (lab.map σ.toFun).size ≤ α)]

end FlipSelf

/-- The flip packaged as a state self-equivalence, for a raw involution
`f`: the `S`-hypotheses are stated on `f` and converted through
`renamingOfFlip` internally. -/
theorem stPerm_self_flip {f : Nat → Nat} {S : Nat → Prop}
    {st : RefineSt n} {level : Nat}
    (hok : StOk n level st)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hSpair : ∀ p ∈ cells st.ptn level n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells st.ptn level n, S p.1 →
      f st.lab[p.1]! = st.lab[p.1 + 1]! ∧
        f st.lab[p.1 + 1]! = st.lab[p.1]!)
    (hSfix : ∀ p ∈ cells st.ptn level n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 →
        f st.lab[p.1 + o]! = st.lab[p.1 + o]!) :
    StPerm level st (mapSt (renamingOfFlip f n hfb hinvol) st) := by
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hok.labOk i (by rw [hok.labSize]; omega)
  have hat : ∀ i, i < n →
      (renamingOfFlip f n hfb hinvol).toFun st.lab[i]! =
        f st.lab[i]! := fun i hi =>
    renamingOfFlip_at hfb hinvol (hlb i hi)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (st.lab.map _).size = st.lab.size
    rw [Array.size_map]
  · show cellsPerm st.ptn level st.lab
      (st.lab.map (renamingOfFlip f n hfb hinvol).toFun)
    refine cellsPerm_self_flip hok.ptnSize hok.labSize hok.ptnEnd
      hSpair ?_ ?_
    · intro p hp hS
      have hpsz := hok.ptnSize
      have hbd : p.2 < st.ptn.size :=
        cells_bound (by omega) hok.ptnEnd _ hp
      have hp2 : p.2 = p.1 + 1 := hSpair _ hp hS
      obtain ⟨h1, h2⟩ := hSswap _ hp hS
      rw [hok.ptnSize] at hbd
      constructor
      · rw [hat p.1 (by omega)]
        exact h1
      · rw [hat (p.1 + 1) (by omega)]
        exact h2
    · intro p hp hS o ho
      have hpsz := hok.ptnSize
      have hbd : p.2 < st.ptn.size :=
        cells_bound (by omega) hok.ptnEnd _ hp
      have hle := cells_le _ hp
      rw [hok.ptnSize] at hbd
      rw [hat (p.1 + o) (by omega)]
      exact hSfix _ hp hS o ho

/-! # The pair deviation -/

/-- The flip data at a pair target: a row-preserving self-symmetry of
the node carrying one child's individualized vertex to the other's. -/
theorem pair_flip_data {st : RefineSt n} {level tc : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hP : (tc, tc + 1) ∈ cells st.ptn level n)
    (hOdd : ∀ q ∈ cells st.ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {a b : Nat} (ha : a < 2) (hb : b < 2) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + b]! = σ.toFun st.lab[tc + a]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinjr : ∀ i j, i < n → j < n →
      st.lab[i]! = st.lab[j]! → i = j := hIt.inj
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfb : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc v < n := fun v hv =>
    pairFlip_lt hpsz hlsz hend hIt.ok.labOk hv
  have hinvol : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc
        (pairFlip ctx st.lab st.ptn level tc v) = v := fun v _ =>
    pairFlip_invol hpsz hend hIt.inj
  have hSpair : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → p.2 = p.1 + 1 := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    have hpm : (p.1, p.2) ∈ cells st.ptn level n := hp
    exact cells_eq_of_start (by omega) hend hpm hcell
  have hSswap : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 →
      pairFlip ctx st.lab st.ptn level tc st.lab[p.1]! =
          st.lab[p.1 + 1]! ∧
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + 1]! =
          st.lab[p.1]! := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    exact ⟨pairFlip_first hpsz hend hIt.inj hS hcell,
      pairFlip_second hpsz hend hIt.inj hS hcell⟩
  have hSfix : ∀ p ∈ cells st.ptn level n,
      ¬ PairReach ctx st.lab st.ptn level tc p.1 →
      ∀ o, o < p.2 + 1 - p.1 →
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + o]! =
          st.lab[p.1 + o]! := by
    intro p hp hS o ho
    exact pairFlip_fix_cell hpsz hend hIt.inj hp hS ho
  have hSclosed : ∀ p ∈ cells st.ptn level n,
      ∀ q ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → q.2 = q.1 + 1 →
      PairMatch ctx.g st.lab[p.1]! st.lab[p.1 + 1]!
        st.lab[q.1]! st.lab[q.1 + 1]! →
      PairReach ctx st.lab st.ptn level tc q.1 := by
    intro p hp q hq hS hq2 hm
    have hqm : (q.1, q.1 + 1) ∈ cells st.ptn level n := by
      have hqm' : (q.1, q.2) ∈ cells st.ptn level n := hq
      rw [hq2] at hqm'
      exact hqm'
    exact PairReach.step hS (pairReach_pair hP hS) hqm hm
  have hsurj := labInj_surj
    (by rw [hlsz]; exact Nat.le_refl _ : n ≤ st.lab.size)
    hIt.ok.labOk hIt.inj
  have hrows := flip_rows hE hpsz hend hinjr hlb hsurj hsymm
    hloop hfb hinvol hSpair hSswap hSfix hSclosed hOdd
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  have hsp := stPerm_self_flip hIt.ok hfb hinvol hSpair hSswap hSfix
  have hbd : (tc, tc + 1).2 < st.ptn.size :=
    cells_bound (by omega) hend _ hP
  have hbase : PairReach ctx st.lab st.ptn level tc tc :=
    PairReach.base
  have hvv : st.lab[tc + b]! =
      (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
        hfb hinvol).toFun st.lab[tc + a]! := by
    have hat : ∀ i, i < n →
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[i]! =
          pairFlip ctx st.lab st.ptn level tc st.lab[i]! := fun i hi =>
      renamingOfFlip_at hfb hinvol (hlb i hi)
    rcases Decidable.em (a = 0) with rfl | ha0
    · have hb1 : b = 1 := by omega
      subst hb1
      show st.lab[tc + 1]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc]!
      rw [hat tc (by rw [hpsz] at hbd; omega),
        pairFlip_first hpsz hend hIt.inj hbase hP]
    · have ha1 : a = 1 := by omega
      have hb0 : b = 0 := by omega
      subst ha1; subst hb0
      show st.lab[tc]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc + 1]!
      rw [hat (tc + 1) (by rw [hpsz] at hbd; omega),
        pairFlip_second hpsz hend hIt.inj hbase hP]
  exact ⟨renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
    hfb hinvol, hgmap, hsp, hvv⟩

/-- A deviation at a pair target under the first-branch shape: descents
below its two children reach leaves with the same rows. -/
theorem pair_deviation_leafRows {st : RefineSt n}
    {level tc level' : Nat} {U' : RefineSt n}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hP : (tc, tc + 1) ∈ cells st.ptn level n)
    (hOdd : ∀ q ∈ cells st.ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {a b : Nat} (ha : a < 2) (hb : b < 2) (hab : a ≠ b)
    (hdesc : Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + a]!) level' U')
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V', Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + b]!) level' V' ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab := by
  obtain ⟨σ, hgmap, hsp, hvv⟩ := pair_flip_data hIt hgsz hsymm
    hloop hE hP hOdd ha hb hab
  exact deviation_leafRows_self hIt hlvl hgmap hsp hP (by omega)
    (show a ≤ tc + 1 - tc by omega) (show b ≤ tc + 1 - tc by omega)
    hvv hdesc hdisc

end Hex.GraphIso.Nauty
