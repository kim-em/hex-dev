/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.NodeLit
public import HexGraphIso.Nauty.Packed
public import HexGraphIso.Nauty.PopCount

public section

/-!
The certificate replay over packed kernel state.

`HexGraphIso.NodeLit` replays certificates over `List Nat` labelling
and partition state, which the kernel reads and writes by walking the
spine, one step per position: a refinement pass that touches every
position is quadratic in the kernel, and the measured cost per
certificate record grows as `n ^ 1.8` (see
`scripts/bench/graphiso_kernel_cost.py`). This file clones the same
call tree over `lab` and `ptn` packed into fixed-width fields of one
`Nat` (`HexGraphIso.Nauty.Packed`), the adjacency rows packed the same
way with width `n`, and every arithmetic step spelled with the raw
kernel-accelerated functions, so a read is a shift and a mask, a
write a handful of arithmetic steps, and a pass linear in the kernel.

Each clone is proven equal to its list original under the
correspondence `Rep` between the packed number and the list, threaded
through the state by `RepSt`. The equalities compose to
`checkKeyP_eq`, so `checkKeyP` closes the negative route through the
existing `checkKeyLit`/`checkKey` soundness; the compiled search and
the `Array` definitions the soundness proofs mention are untouched.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-! # Packed context and state -/

/-- The replay context over packed rows: `w`/`m` are the field width
and mask for positions and vertices, `g` the rows packed with width
`n`, and `rm` the row mask. -/
structure CtxP where
  /-- The number of vertices. -/
  n : Nat
  /-- The field width of packed position and vertex vectors. -/
  w : Nat
  /-- `2 ^ w - 1`. -/
  m : Nat
  /-- The adjacency rows, row `v` in bits `[n * v, n * (v + 1))`. -/
  g : Nat
  /-- `2 ^ n - 1`. -/
  rm : Nat

/-- The correspondence between a packed context and a list context. -/
structure CtxRep (ctx : CtxP) (ctxL : CtxL) : Prop where
  n : ctx.n = ctxL.n
  m : ctx.m = 2 ^ ctx.w - 1
  rm : ctx.rm = 2 ^ ctx.n - 1
  g : Rep ctx.n ctx.n ctx.g ctxL.g
  /-- Positions, vertices, the initial partition's infinity `n + 2`, and
  every level the replay's fuel of `n` reaches fit a field. -/
  nlt : ctx.n + 2 < 2 ^ ctx.w

/-- Read a packed position or vertex vector. -/
@[expose] def lget (ctx : CtxP) (a i : Nat) : Nat := pget ctx.w ctx.m a i

/-- Write a packed position or vertex vector. -/
@[expose] def lset (ctx : CtxP) (a i v : Nat) : Nat :=
  pset ctx.w ctx.m ctx.n a i v

/-- The row of vertex `v`. -/
@[expose] def rowP (ctx : CtxP) (v : Nat) : Nat := pget ctx.n ctx.rm ctx.g v

theorem lget_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) {a : Nat}
    {l : List Nat} (hr : Rep ctx.w ctx.n a l) (i : Nat) :
    lget ctx a i = atD l i 0 := by
  rw [lget, h.m, hr.get]

theorem lget_lt {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (a i : Nat) :
    lget ctx a i < 2 ^ ctx.w := by
  rw [lget, h.m]
  exact pget_lt ..

theorem lset_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) {a : Nat}
    {l : List Nat} (hr : Rep ctx.w ctx.n a l) (i : Nat) {v : Nat}
    (hv : v < 2 ^ ctx.w) : Rep ctx.w ctx.n (lset ctx a i v) (l.set i v) := by
  rw [lset, h.m]
  exact hr.set i hv

theorem rowP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (v : Nat) :
    rowP ctx v = atD ctxL.g v 0 := by
  rw [rowP, h.rm, h.g.get]

/-- `RefineSt` with packed labelling and partition. -/
structure RefineStP where
  lab : Nat
  ptn : Nat
  active : Nat
  numcells : Nat
  hint : Nat
  maxpos : Nat
  longcode : Nat

/-- The correspondence between packed and list refine states. -/
structure RepSt (w n : Nat) (st : RefineStP) (stL : RefineStL) : Prop where
  lab : Rep w n st.lab stL.lab
  ptn : Rep w n st.ptn stL.ptn
  active : st.active = stL.active
  numcells : st.numcells = stL.numcells
  hint : st.hint = stL.hint
  maxpos : st.maxpos = stL.maxpos
  longcode : st.longcode = stL.longcode

/-- `RepSt` from the two packed correspondences and the scalar field
equalities in one conjunction. -/
theorem RepSt.mk' {w n : Nat} {st : RefineStP} {stL : RefineStL}
    (hlab : Rep w n st.lab stL.lab) (hptn : Rep w n st.ptn stL.ptn)
    (hrest : st.active = stL.active ∧ st.numcells = stL.numcells ∧
      st.hint = stL.hint ∧ st.maxpos = stL.maxpos ∧ st.longcode = stL.longcode) :
    RepSt w n st stL :=
  ⟨hlab, hptn, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2⟩

/-! # Raw helpers -/

theorem cond_and {α : Type} (a b : Bool) (x y : α) :
    cond (a && b) x y = if a = true ∧ b = true then x else y := by
  cases a <;> cases b <;> simp

theorem cond_or {α : Type} (a b : Bool) (x y : α) :
    cond (a || b) x y = if a = true ∨ b = true then x else y := by
  cases a <;> cases b <;> simp

/-- `Nat.max`, raw. -/
@[expose] def maxK (a b : Nat) : Nat := cond (Nat.ble a b) b a

theorem maxK_eq (a b : Nat) : maxK a b = Nat.max a b := by
  rw [maxK, cond_ble]
  rfl

/-- `Nat.min`, raw. -/
@[expose] def minK (a b : Nat) : Nat := cond (Nat.ble a b) a b

theorem minK_eq (a b : Nat) : minK a b = Nat.min a b := by
  rw [minK, cond_ble]
  rfl

/-- `multOf`, raw. -/
@[expose] def multOfK (counts : List Nat) (v : Nat) : Nat :=
  go counts 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | c :: rest, acc => go rest (cond (Nat.beq c v) (Nat.add acc 1) acc)

theorem multOfK_go_eq (v : Nat) : ∀ (counts : List Nat) (acc : Nat),
    multOfK.go v counts acc = List.countP.go (· == v) counts acc
  | [], _ => rfl
  | c :: rest, acc => by
    rw [multOfK.go, List.countP.go, multOfK_go_eq v rest, cond_beq, add_eq]
    rcases Decidable.em (c = v) with h | h
    · simp [h]
    · simp [h]

theorem multOfK_eq (counts : List Nat) (v : Nat) :
    multOfK counts v = multOf counts v := by
  rw [multOfK, multOf, List.countP, multOfK_go_eq]

/-- `countValues`, raw. -/
@[expose] def countValuesK (counts : List Nat) : List Nat :=
  let lo := counts.foldl minK (counts.headD 0)
  (List.range (Nat.sub (Nat.add (counts.foldl maxK (counts.headD 0)) 1) lo)).map
    (Nat.add lo ·)

theorem countValuesK_eq (counts : List Nat) :
    countValuesK counts = countValues counts := by
  rw [countValuesK, countValues]
  simp only [add_eq, sub_eq]
  have hmax : maxK = Nat.max := funext fun a => funext fun b => maxK_eq a b
  have hmin : minK = Nat.min := funext fun a => funext fun b => minK_eq a b
  rw [hmax, hmin]

/-- `pickSplit`, raw. -/
@[expose] def pickSplitK (active hint : Nat) : Option Nat :=
  cond (elemK active hint) (some hint)
    (match nextElemK active (some hint) with
    | some v => some v
    | none => nextElemK active none)

theorem pickSplitK_eq (active hint : Nat) :
    pickSplitK active hint = pickSplit active hint := by
  cases hn : nextElem active (some hint) <;>
    simp [pickSplitK, pickSplit, elemK_eq, nextElemK_eq, hn]

/-- The bound on a bit set's population. -/
theorem popCount_le_of_lt {nn s : Nat} (hs : s < 2 ^ nn) :
    popCount s ≤ nn := by
  rw [popCount_eq_bitCount nn s hs, bitCount]
  exact Nat.le_trans List.countP_le_length
    (Nat.le_of_eq (List.length_range ..))

/-! # The refine tower over packed state -/

@[expose] def cellEndGoP (ctx : CtxP) (ptn level : Nat) : Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
    cond (Nat.blt level (lget ctx ptn j))
      (cellEndGoP ctx ptn level fuel (Nat.add j 1)) j

@[expose] def cellEndP (ctx : CtxP) (ptn level i : Nat) : Nat :=
  cellEndGoP ctx ptn level (Nat.sub ctx.n i) i

theorem cellEndGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : ∀ (fuel j : Nat),
      cellEndGoP ctx ptnP level fuel j = cellEndGoL ptn level fuel j
  | 0, _ => rfl
  | fuel + 1, j => by
    rw [cellEndGoP, cellEndGoL, cond_blt, lget_eq h hp, add_eq]
    rcases Decidable.em (level < atD ptn j 0) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl, cellEndGoP_eq h hp level fuel]
    · rw [ite_eq_right hl, ite_eq_right hl]

theorem cellEndP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level i : Nat) : cellEndP ctx ptnP level i = cellEndL ptn level i := by
  rw [cellEndP, cellEndL, hp.len, sub_eq, cellEndGoP_eq h hp]

@[expose] def cellsGoP (ctx : CtxP) (ptn level : Nat) :
    Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, c1 =>
    cond (Nat.blt c1 ctx.n)
      (let c2 := cellEndP ctx ptn level c1
      (c1, c2) :: cellsGoP ctx ptn level fuel (Nat.add c2 1))
      []

@[expose] def cellsP (ctx : CtxP) (ptn level : Nat) : List (Nat × Nat) :=
  cellsGoP ctx ptn level ctx.n 0

theorem cellsGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : ∀ (fuel c1 : Nat),
      cellsGoP ctx ptnP level fuel c1 = cellsGoL ptn level ctxL.n fuel c1
  | 0, _ => rfl
  | fuel + 1, c1 => by
    rw [cellsGoP, cellsGoL, cond_blt, h.n]
    rcases Decidable.em (c1 < ctxL.n) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl]
      simp only [cellEndP_eq h hp, add_eq, cellsGoP_eq h hp level fuel]
    · rw [ite_eq_right hl, ite_eq_right hl]

theorem cellsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) : cellsP ctx ptnP level = cellsL ptn level ctxL.n := by
  rw [cellsP, cellsL, cellsGoP_eq h hp, h.n]

/-- The two-pointer partition with `d = c2 + 1`, so the right pointer
stays a natural (`d = 0` is nauty's `c2 = -1`). -/
@[expose] def splitCellLoopP (ctx : CtxP) (gRow : Nat) :
    Nat → Nat → Nat → Nat → (Nat × Nat × Nat)
  | 0, lab, c1, d => (lab, c1, d)
  | fuel + 1, lab, c1, d =>
    cond (Nat.blt c1 d)
      (cond (elemK gRow (lget ctx lab c1))
        (splitCellLoopP ctx gRow fuel lab (Nat.add c1 1) d)
        (splitCellLoopP ctx gRow fuel
          (lset ctx (lset ctx lab c1 (lget ctx lab (Nat.sub d 1)))
            (Nat.sub d 1) (lget ctx lab c1))
          c1 (Nat.sub d 1)))
      (lab, c1, d)

theorem splitCellLoopP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (gRow : Nat) : ∀ (fuel : Nat) {labP : Nat} {lab : List Nat},
      Rep ctx.w ctx.n labP lab → ∀ (c1 d : Nat),
      Rep ctx.w ctx.n (splitCellLoopP ctx gRow fuel labP c1 d).1
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).1 ∧
      ((splitCellLoopP ctx gRow fuel labP c1 d).2.1 : Int) =
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).2.1 ∧
      ((splitCellLoopP ctx gRow fuel labP c1 d).2.2 : Int) =
        (splitCellLoopL gRow fuel lab (c1 : Int) ((d : Int) - 1)).2.2 + 1
  | 0, _, _, hl, c1, d => by
    rw [splitCellLoopP, splitCellLoopL]
    exact ⟨hl, rfl, by simp⟩
  | fuel + 1, labP, lab, hl, c1, d => by
    rw [splitCellLoopP, splitCellLoopL, cond_blt]
    simp only [add_eq, sub_eq]
    rcases Decidable.em (c1 < d) with hlt | hlt
    · have he' : elemK gRow (lget ctx labP c1) = elem gRow (atD lab c1 0) := by
        rw [elemK_eq, lget_eq h hl]
      rw [ite_eq_left hlt, ite_eq_left (show (c1 : Int) ≤ (d : Int) - 1 by omega),
        he', cond_beq_true, Int.toNat_natCast]
      rcases Decidable.em (elem gRow (atD lab c1 0) = true) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        have := splitCellLoopP_eq h gRow fuel hl (c1 + 1) d
        simpa using this
      · rw [ite_eq_right he, ite_eq_right he]
        have hsub : ((d : Int) - 1).toNat = d - 1 := by omega
        have hl' : Rep ctx.w ctx.n
            (lset ctx (lset ctx labP c1 (lget ctx labP (d - 1))) (d - 1)
              (lget ctx labP c1))
            ((lab.set c1 (atD lab (d - 1) 0)).set (d - 1) (atD lab c1 0)) := by
          rw [← lget_eq h hl, ← lget_eq h hl]
          exact lset_rep h (lset_rep h hl c1 (lget_lt h _ _)) _ (lget_lt h _ _)
        have := splitCellLoopP_eq h gRow fuel hl' c1 (d - 1)
        rw [hsub]
        have hd : (((d - 1 : Nat) : Int) - 1 : Int) = (d : Int) - 1 - 1 := by omega
        rw [hd] at this
        exact this
    · rw [ite_eq_right hlt, ite_eq_right (show ¬ (c1 : Int) ≤ (d : Int) - 1 by omega)]
      exact ⟨hl, rfl, by simp⟩

@[expose] def trivialSplitP (ctx : CtxP) (level cell1 cell2 c1 d : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.ble (Nat.add cell1 1) d && Nat.ble c1 cell2)
    (cond (elemK st.active cell1 ||
        Nat.ble (Nat.sub cell2 c1) (Nat.sub (Nat.sub d 1) cell1))
      (cond (Nat.beq c1 cell2)
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK st.active c1
          hint := c1 }
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK st.active c1 })
      (cond (Nat.beq (Nat.sub d 1) cell1)
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK st.active cell1
          hint := cell1 }
        { st with
          ptn := lset ctx st.ptn (Nat.sub d 1) level
          longcode := mashK st.longcode (Nat.sub d 1)
          numcells := Nat.add st.numcells 1
          active := insertK st.active cell1 }))
    st

theorem trivialSplitP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 c1 d : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (trivialSplitP ctx level cell1 cell2 c1 d st)
      (trivialSplitL level cell1 cell2 (c1 : Int) ((d : Int) - 1) stL) := by
  have hsub : ((d : Int) - 1).toNat = d - 1 := by omega
  rw [trivialSplitP, trivialSplitL, cond_and, cond_or, cond_beq, cond_beq,
    hst.active, elemK_eq]
  simp only [Nat.ble_eq, add_eq, sub_eq, Int.ofNat_eq_natCast, Int.toNat_natCast, hsub,
    beq_iff_eq]
  have hlem : ∀ (i : Nat), RepSt ctx.w ctx.n
      ⟨st.lab, lset ctx st.ptn (d - 1) level, insertK stL.active i,
        st.numcells + 1, i, st.maxpos, mashK st.longcode (d - 1)⟩
      ⟨stL.lab, stL.ptn.set (d - 1) level, insert stL.active i,
        stL.numcells + 1, i, stL.maxpos, mash stL.longcode (d - 1)⟩ := fun i =>
    RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev)
      (by simp [hst.numcells, hst.maxpos, hst.longcode, mashK_eq, insertK_eq])
  have hlem' : ∀ (i : Nat), RepSt ctx.w ctx.n
      ⟨st.lab, lset ctx st.ptn (d - 1) level, insertK stL.active i,
        st.numcells + 1, st.hint, st.maxpos, mashK st.longcode (d - 1)⟩
      ⟨stL.lab, stL.ptn.set (d - 1) level, insert stL.active i,
        stL.numcells + 1, stL.hint, stL.maxpos, mash stL.longcode (d - 1)⟩ := fun i =>
    RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev)
      (by simp [hst.numcells, hst.hint, hst.maxpos, hst.longcode, mashK_eq,
        insertK_eq])
  rcases Decidable.em (cell1 + 1 ≤ d ∧ c1 ≤ cell2) with hc | hc
  · rw [ite_eq_left hc,
      ite_eq_left (show (d : Int) - 1 ≥ (cell1 : Int) ∧ (c1 : Int) ≤ (cell2 : Int) by omega)]
    rcases Decidable.em (elem stL.active cell1 = true ∨
        cell2 - c1 ≤ d - 1 - cell1) with ho | ho
    · rw [ite_eq_left ho,
        ite_eq_left (show elem stL.active cell1 = true ∨ d - 1 - cell1 ≥ cell2 - c1 by
          simpa using ho)]
      rcases Decidable.em (c1 = cell2) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        exact hlem c1
      · rw [ite_eq_right he, ite_eq_right he]
        exact hlem' c1
    · rw [ite_eq_right ho,
        ite_eq_right (show ¬ (elem stL.active cell1 = true ∨ d - 1 - cell1 ≥ cell2 - c1) by
          simpa using ho)]
      rcases Decidable.em (d - 1 = cell1) with he | he
      · rw [ite_eq_left he, ite_eq_left he]
        exact hlem cell1
      · rw [ite_eq_right he, ite_eq_right he]
        exact hlem' cell1
  · rw [ite_eq_right hc,
      ite_eq_right (show ¬ ((d : Int) - 1 ≥ (cell1 : Int) ∧ (c1 : Int) ≤ (cell2 : Int)) by
        omega)]
    exact hst

@[expose] def trivialCellP (ctx : CtxP) (level gRow cell1 cell2 : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.beq cell1 cell2) st
    (let r := splitCellLoopP ctx gRow (Nat.add (Nat.sub cell2 cell1) 2) st.lab
      cell1 (Nat.add cell2 1)
    trivialSplitP ctx level cell1 cell2 r.2.1 r.2.2 { st with lab := r.1 })

theorem trivialCellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (gRow cell1 cell2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (trivialCellP ctx level gRow cell1 cell2 st)
      (trivialCellL level gRow cell1 cell2 stL) := by
  rw [trivialCellP, trivialCellL, cond_beq]
  rcases Decidable.em (cell1 = cell2) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    simp only [add_eq, sub_eq, Int.ofNat_eq_natCast]
    have hloop := splitCellLoopP_eq h gRow (cell2 - cell1 + 2) hst.lab cell1
      (cell2 + 1)
    have hd : (((cell2 + 1 : Nat) : Int) - 1 : Int) = (cell2 : Int) := by omega
    rw [hd] at hloop
    obtain ⟨hlab, hc1, hc2⟩ := hloop
    have hst' : RepSt ctx.w ctx.n
        { st with lab := (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab
          cell1 (cell2 + 1)).1 }
        { stL with lab := (splitCellLoopL gRow (cell2 - cell1 + 2) stL.lab
          (cell1 : Int) (cell2 : Int)).1 } :=
      ⟨hlab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
        hst.longcode⟩
    have := trivialSplitP_eq h hlev cell1 cell2
      (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab cell1 (cell2 + 1)).2.1
      (splitCellLoopP ctx gRow (cell2 - cell1 + 2) st.lab cell1 (cell2 + 1)).2.2
      hst'
    rw [hc1, hc2, Int.add_sub_cancel] at this
    exact this

@[expose] def refineTrivialGoP (ctx : CtxP) (level gRow : Nat) :
    List (Nat × Nat) → RefineStP → RefineStP
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineTrivialGoP ctx level gRow rest
      (trivialCellP ctx level gRow cell1 cell2 st)

@[expose] def refineTrivialP (ctx : CtxP) (level split1 : Nat)
    (st : RefineStP) : RefineStP :=
  refineTrivialGoP ctx level (rowP ctx (lget ctx st.lab split1))
    (cellsP ctx st.ptn level) st

theorem refineTrivialGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (gRow : Nat) :
    ∀ (cs : List (Nat × Nat)) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineTrivialGoP ctx level gRow cs st)
        (refineTrivialGoL level gRow cs stL)
  | [], _, _, hst => hst
  | (cell1, cell2) :: rest, _, _, hst => by
    rw [refineTrivialGoP, refineTrivialGoL]
    exact refineTrivialGoP_eq h hlev gRow rest
      (trivialCellP_eq h hlev gRow cell1 cell2 hst)

theorem refineTrivialP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineTrivialP ctx level split1 st)
      (refineTrivialL ctxL level split1 stL) := by
  rw [refineTrivialP, refineTrivialL, rowP_eq h, lget_eq h hst.lab,
    cellsP_eq h hst.ptn]
  exact refineTrivialGoP_eq h hlev _ _ hst

@[expose] def worksetOfP (ctx : CtxP) (lab lo hi : Nat) : Nat :=
  (List.range (Nat.sub (Nat.add hi 1) lo)).foldl
    (fun w o => insertK w (lget ctx lab (Nat.add lo o))) 0

theorem worksetOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (lo hi : Nat) :
    worksetOfP ctx labP lo hi = worksetOfL lab lo hi := by
  rw [worksetOfP, worksetOfL]
  simp only [insertK_eq, lget_eq h hl, add_eq, sub_eq]

@[expose] def countsOfP (ctx : CtxP) (lab workset cell1 cell2 : Nat) :
    List Nat :=
  (List.range (Nat.sub (Nat.add cell2 1) cell1)).map fun o =>
    popCountK (Nat.land workset (rowP ctx (lget ctx lab (Nat.add cell1 o))))

theorem countsOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    (workset cell1 cell2 : Nat) :
    countsOfP ctx labP workset cell1 cell2 =
      countsOfL ctxL lab workset cell1 cell2 := by
  rw [countsOfP, countsOfL]
  simp only [popCountK_eq, land_eq, rowP_eq h, lget_eq h hl, add_eq, sub_eq]

/-- `windowStep` with `maxcell1 = maxcell + 1`, so nauty's `-1` seed
is `0`. -/
@[expose] def windowStepP (ctx : CtxP) (level cell1 cell2 v c1 c2 maxcell1 : Nat)
    (st : RefineStP) : RefineStP :=
  let st := { st with longcode := mashK st.longcode (Nat.add v c1) }
  let st :=
    cond (Nat.blt maxcell1 (Nat.add (Nat.sub c2 c1) 1))
      { st with maxpos := c1 } st
  let st :=
    cond (Nat.beq c1 cell1) st
      (let st := { st with
        active := insertK st.active c1
        numcells := Nat.add st.numcells 1 }
      cond (Nat.beq (Nat.sub c2 c1) 1) { st with hint := c1 } st)
  cond (Nat.ble c2 cell2)
    { st with ptn := lset ctx st.ptn (Nat.sub c2 1) level } st

theorem windowStepP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 v c1 c2 maxcell1 : Nat)
    (maxcell : Int) (hmax : (maxcell1 : Int) = maxcell + 1)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (windowStepP ctx level cell1 cell2 v c1 c2 maxcell1 st)
      (windowStepL level cell1 cell2 v c1 c2 maxcell stL) := by
  rw [windowStepP, windowStepL]
  simp only [cond_blt, cond_beq, cond_ble, add_eq, sub_eq, mashK_eq,
    insertK_eq, hst.active, hst.numcells, hst.longcode, hst.maxpos, hst.hint,
    Int.ofNat_eq_natCast, bne_iff_ne, beq_iff_eq, ne_eq]
  have h1 : (((c2 - c1 : Nat) : Int) > maxcell) ↔ (maxcell1 < c2 - c1 + 1) := by
    omega
  simp only [h1]
  repeat' split
  all_goals first
    | exact RepSt.mk' hst.lab (lset_rep h hst.ptn _ hlev) (by simp)
    | exact RepSt.mk' hst.lab hst.ptn (by simp)
    | (exfalso; omega)

@[expose] def windowScanP (ctx : CtxP) (level cell1 cell2 : Nat)
    (counts : List Nat) : List Nat → Nat → Nat → RefineStP → RefineStP
  | [], _, _, st => st
  | v :: vs, c1, maxcell1, st =>
    let mult := multOfK counts v
    cond (Nat.blt 0 mult)
      (windowScanP ctx level cell1 cell2 counts vs (Nat.add c1 mult)
        (cond (Nat.blt maxcell1 (Nat.add mult 1)) (Nat.add mult 1) maxcell1)
        (windowStepP ctx level cell1 cell2 v c1 (Nat.add c1 mult) maxcell1 st))
      (windowScanP ctx level cell1 cell2 counts vs c1 maxcell1 st)

theorem windowScanP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (cell1 cell2 : Nat)
    (counts : List Nat) : ∀ (vs : List Nat) (c1 maxcell1 : Nat)
      (maxcell : Int), (maxcell1 : Int) = maxcell + 1 →
      ∀ {st : RefineStP} {stL : RefineStL}, RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (windowScanP ctx level cell1 cell2 counts vs c1 maxcell1 st)
        (windowScanL level cell1 cell2 counts vs c1 maxcell stL)
  | [], _, _, _, _, _, _, hst => hst
  | v :: vs, c1, maxcell1, maxcell, hmax, st, stL, hst => by
    rw [windowScanP, windowScanL]
    simp only [multOfK_eq, cond_blt, add_eq]
    rcases Decidable.em (0 < multOf counts v) with hm | hm
    · rw [ite_eq_left hm, ite_eq_left hm]
      refine windowScanP_eq h hlev cell1 cell2 counts vs _ _ _ ?_
        (windowStepP_eq h hlev cell1 cell2 v c1 _ maxcell1 maxcell hmax hst)
      simp only [Int.ofNat_eq_natCast]
      rcases Decidable.em (maxcell1 < multOf counts v + 1) with hl | hl
      · rw [ite_eq_left hl,
          ite_eq_left (show ((multOf counts v : Nat) : Int) > maxcell by omega)]
        simp
      · rw [ite_eq_right hl,
          ite_eq_right (show ¬ ((multOf counts v : Nat) : Int) > maxcell by omega)]
        exact hmax
    · rw [ite_eq_right hm, ite_eq_right hm]
      exact windowScanP_eq h hlev cell1 cell2 counts vs c1 maxcell1 maxcell hmax hst

@[expose] def segmentOfP (ctx : CtxP) (lab cell1 : Nat) (counts values : List Nat) :
    List Nat :=
  values.flatMap fun v =>
    (counts.zipIdx.filter fun p => Nat.beq p.1 v).map fun p =>
      lget ctx lab (Nat.add cell1 p.2)

theorem segmentOfP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (cell1 : Nat)
    (counts values : List Nat) :
    segmentOfP ctx labP cell1 counts values = segmentOfL lab cell1 counts values := by
  rw [segmentOfP, segmentOfL]
  congr 1
  funext v
  rw [List.filter_congr (fun p _ => ?_)]
  · refine List.map_congr_left fun p _ => ?_
    rcases p with ⟨c, j⟩
    simp [lget_eq h hl]
  · rcases p with ⟨c, j⟩
    exact beq_eq_beq c v

theorem segmentOfP_small {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (labP cell1 : Nat) (counts values : List Nat) :
    Small ctx.w (segmentOfP ctx labP cell1 counts values) := by
  unfold Small
  intro x hx
  rw [segmentOfP, List.mem_flatMap] at hx
  obtain ⟨v, _, hx⟩ := hx
  rw [List.mem_map] at hx
  obtain ⟨⟨c, j⟩, _, rfl⟩ := hx
  exact lget_lt h _ _

@[expose] def writeSegmentP (ctx : CtxP) (lab cell1 : Nat) : List Nat → Nat
  | [] => lab
  | x :: rest => writeSegmentP ctx (lset ctx lab cell1 x) (Nat.add cell1 1) rest

theorem writeSegmentP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) :
    ∀ (seg : List Nat), Small ctx.w seg → ∀ {labP : Nat} {lab : List Nat},
      Rep ctx.w ctx.n labP lab → ∀ (cell1 : Nat),
      Rep ctx.w ctx.n (writeSegmentP ctx labP cell1 seg)
        (writeSegmentL lab cell1 seg)
  | [], _, _, _, hl, _ => hl
  | x :: rest, hs, _, _, hl, cell1 => by
    rw [writeSegmentP, writeSegmentL, add_eq]
    exact writeSegmentP_rep h rest (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      (lset_rep h hl cell1 (hs x (List.mem_cons_self ..))) (cell1 + 1)

@[expose] def nontrivialFixP (cell1 : Nat) (st : RefineStP) : RefineStP :=
  cond (elemK st.active cell1) st
    { st with active := eraseK (insertK st.active cell1) st.maxpos }

theorem nontrivialFixP_eq (cell1 : Nat) {w n : Nat} {st : RefineStP}
    {stL : RefineStL} (hst : RepSt w n st stL) :
    RepSt w n (nontrivialFixP cell1 st) (nontrivialFixL cell1 stL) := by
  rw [nontrivialFixP, nontrivialFixL, elemK_eq, cond_beq_true, hst.active,
    hst.maxpos, eraseK_eq, insertK_eq]
  rcases Decidable.em (elem stL.active cell1 = true) with he | he
  · rw [ite_eq_left he, ite_eq_right (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_left (by simpa using he)]
    exact RepSt.mk' hst.lab hst.ptn
      (by simp [hst.numcells, hst.hint, hst.longcode])

@[expose] def nontrivialCellP (ctx : CtxP) (level workset cell1 cell2 : Nat)
    (st : RefineStP) : RefineStP :=
  cond (Nat.beq cell1 cell2) st
    (let counts := countsOfP ctx st.lab workset cell1 cell2
    let lo := counts.foldl minK (counts.headD 0)
    let hi := counts.foldl maxK (counts.headD 0)
    cond (Nat.beq lo hi)
      { st with longcode := mashK st.longcode (Nat.add lo cell1) }
      (let values := countValuesK counts
      let st' := windowScanP ctx level cell1 cell2 counts values cell1 0 st
      nontrivialFixP cell1
        { st' with
          lab := writeSegmentP ctx st'.lab cell1
            (segmentOfP ctx st'.lab cell1 counts values) }))

theorem nontrivialCellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (workset cell1 cell2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (nontrivialCellP ctx level workset cell1 cell2 st)
      (nontrivialCellL ctxL level workset cell1 cell2 stL) := by
  rw [nontrivialCellP, nontrivialCellL, cond_beq]
  rcases Decidable.em (cell1 = cell2) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact hst
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    simp only [countsOfP_eq h hst.lab, cond_beq, add_eq]
    have hmax : maxK = Nat.max := funext fun a => funext fun b => maxK_eq a b
    have hmin : minK = Nat.min := funext fun a => funext fun b => minK_eq a b
    rw [hmax, hmin]
    rcases Decidable.em ((countsOfL ctxL stL.lab workset cell1 cell2).foldl
        Nat.min ((countsOfL ctxL stL.lab workset cell1 cell2).headD 0) =
        (countsOfL ctxL stL.lab workset cell1 cell2).foldl Nat.max
          ((countsOfL ctxL stL.lab workset cell1 cell2).headD 0)) with hlo | hlo
    · rw [ite_eq_left hlo, ite_eq_left (by simpa using hlo)]
      exact ⟨hst.lab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
        by simp [hst.longcode, mashK_eq]⟩
    · rw [ite_eq_right hlo, ite_eq_right (by simpa using hlo), countValuesK_eq]
      have hscan := windowScanP_eq h hlev cell1 cell2
        (countsOfL ctxL stL.lab workset cell1 cell2)
        (countValues (countsOfL ctxL stL.lab workset cell1 cell2)) cell1 0 (-1)
        (by simp) hst
      refine nontrivialFixP_eq cell1 ⟨?_, hscan.ptn, hscan.active, hscan.numcells,
        hscan.hint, hscan.maxpos, hscan.longcode⟩
      rw [segmentOfP_eq h hscan.lab]
      exact writeSegmentP_rep h _
        (by rw [← segmentOfP_eq h hscan.lab]; exact segmentOfP_small h _ _ _ _)
        hscan.lab cell1

@[expose] def refineNontrivialGoP (ctx : CtxP) (level workset : Nat) :
    List (Nat × Nat) → RefineStP → RefineStP
  | [], st => st
  | (cell1, cell2) :: rest, st =>
    refineNontrivialGoP ctx level workset rest
      (nontrivialCellP ctx level workset cell1 cell2 st)

@[expose] def refineNontrivialP (ctx : CtxP) (level split1 split2 : Nat)
    (st : RefineStP) : RefineStP :=
  let workset := worksetOfP ctx st.lab split1 split2
  let st := { st with
    longcode := mashK st.longcode (Nat.add (Nat.sub split2 split1) 1) }
  refineNontrivialGoP ctx level workset (cellsP ctx st.ptn level) st

theorem refineNontrivialGoP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (workset : Nat) :
    ∀ (cs : List (Nat × Nat)) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineNontrivialGoP ctx level workset cs st)
        (refineNontrivialGoL ctxL level workset cs stL)
  | [], _, _, hst => hst
  | (cell1, cell2) :: rest, _, _, hst => by
    rw [refineNontrivialGoP, refineNontrivialGoL]
    exact refineNontrivialGoP_eq h hlev workset rest
      (nontrivialCellP_eq h hlev workset cell1 cell2 hst)

theorem refineNontrivialP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 split2 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineNontrivialP ctx level split1 split2 st)
      (refineNontrivialL ctxL level split1 split2 stL) := by
  rw [refineNontrivialP, refineNontrivialL, worksetOfP_eq h hst.lab]
  simp only [cellsP_eq h hst.ptn, add_eq, sub_eq, mashK_eq]
  exact refineNontrivialGoP_eq h hlev _ _
    ⟨hst.lab, hst.ptn, hst.active, hst.numcells, hst.hint, hst.maxpos,
      by simp [hst.longcode]⟩

@[expose] def refineStepP (ctx : CtxP) (level split1 : Nat) (st : RefineStP) :
    RefineStP :=
  let st := { st with active := eraseK st.active split1 }
  let split2 := cellEndP ctx st.ptn level split1
  let st := { st with longcode := mashK st.longcode (Nat.add split1 split2) }
  cond (Nat.beq split1 split2)
    (refineTrivialP ctx level split1 st)
    (refineNontrivialP ctx level split1 split2 st)

theorem refineStepP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (split1 : Nat)
    {st : RefineStP} {stL : RefineStL} (hst : RepSt ctx.w ctx.n st stL) :
    RepSt ctx.w ctx.n (refineStepP ctx level split1 st)
      (refineStepL ctxL level split1 stL) := by
  rw [refineStepP, refineStepL]
  simp only [cellEndP_eq h hst.ptn, cond_beq, eraseK_eq, mashK_eq, add_eq,
    hst.active, hst.longcode]
  have hst' : RepSt ctx.w ctx.n
      { st with
        active := erase stL.active split1
        longcode := mash stL.longcode (split1 + cellEndL stL.ptn level split1) }
      { stL with
        active := erase stL.active split1
        longcode := mash stL.longcode (split1 + cellEndL stL.ptn level split1) } :=
    ⟨hst.lab, hst.ptn, rfl, hst.numcells, hst.hint, hst.maxpos, rfl⟩
  rcases Decidable.em (split1 = cellEndL stL.ptn level split1) with he | he
  · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
    exact refineTrivialP_eq h hlev split1 hst'
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    exact refineNontrivialP_eq h hlev split1 _ hst'

@[expose] def refineLoopP (ctx : CtxP) (level : Nat) :
    Nat → RefineStP → RefineStP
  | 0, st => st
  | fuel + 1, st =>
    cond (Nat.blt st.numcells ctx.n)
      (match pickSplitK st.active st.hint with
      | some split1 => refineLoopP ctx level fuel (refineStepP ctx level split1 st)
      | none => st)
      st

theorem refineLoopP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) :
    ∀ (fuel : Nat) {st : RefineStP} {stL : RefineStL},
      RepSt ctx.w ctx.n st stL →
      RepSt ctx.w ctx.n (refineLoopP ctx level fuel st)
        (refineLoopL ctxL level fuel stL)
  | 0, _, _, hst => hst
  | fuel + 1, st, stL, hst => by
    have hc : (st.numcells < ctx.n) = (stL.numcells < ctxL.n) := by
      rw [hst.numcells, h.n]
    rw [refineLoopP, refineLoopL, cond_blt, pickSplitK_eq, hst.active,
      hst.hint]
    rcases Decidable.em (st.numcells < ctx.n) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left (Eq.mp hc hl)]
      rcases hps : pickSplit stL.active stL.hint with _ | split1
      · exact hst
      · exact refineLoopP_eq h hlev fuel (refineStepP_eq h hlev split1 hst)
    · rw [ite_eq_right hl, ite_eq_right (fun h' => hl (Eq.mpr hc h'))]
      exact hst

@[expose] def refineP (ctx : CtxP) (level lab ptn active numcells : Nat) :
    RefineStP :=
  let st : RefineStP :=
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }
  let st := refineLoopP ctx level (Nat.add (Nat.mul 4 ctx.n) 8) st
  { st with longcode := cleanupK (mashK st.longcode st.numcells) }

theorem refineP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level < 2 ^ ctx.w) {labP : Nat} {lab : List Nat}
    (hl : Rep ctx.w ctx.n labP lab) {ptnP : Nat} {ptn : List Nat}
    (hp : Rep ctx.w ctx.n ptnP ptn) (active numcells : Nat) :
    RepSt ctx.w ctx.n (refineP ctx level labP ptnP active numcells)
      (refineL ctxL level lab ptn active numcells) := by
  rw [refineP, refineL]
  simp only [add_eq, mul_eq, cleanupK_eq, mashK_eq]
  rw [show 4 * ctxL.n + 8 = 4 * ctx.n + 8 by rw [h.n]]
  have hloop := refineLoopP_eq h hlev (4 * ctx.n + 8)
    (st := ⟨labP, ptnP, active, numcells, 0, 0, numcells⟩)
    (stL := ⟨lab, ptn, active, numcells, 0, 0, numcells⟩)
    ⟨hl, hp, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨hloop.lab, hloop.ptn, hloop.active, hloop.numcells, hloop.hint,
    hloop.maxpos, by simp [hloop.longcode, hloop.numcells]⟩


/-! # Raw list helpers -/

@[expose] def listContainsK : List Nat → Nat → Bool
  | [], _ => false
  | b :: bs, a => cond (Nat.beq a b) true (listContainsK bs a)

theorem listContainsK_eq : ∀ (l : List Nat) (a : Nat),
    listContainsK l a = l.contains a
  | [], _ => rfl
  | b :: bs, a => by
    rw [listContainsK, List.contains_cons, listContainsK_eq bs a, cond_beq]
    rcases Decidable.em (a = b) with h | h <;> simp [h]

@[expose] def listEraseK : List Nat → Nat → List Nat
  | [], _ => []
  | a :: as, b => cond (Nat.beq a b) as (a :: listEraseK as b)

theorem listEraseK_eq : ∀ (l : List Nat) (b : Nat), listEraseK l b = l.erase b
  | [], _ => rfl
  | a :: as, b => by
    rw [listEraseK, List.erase_cons, listEraseK_eq as b, cond_beq]
    rcases Decidable.em (a = b) with h | h <;> simp [h]

/-- `List.isPerm`, raw. -/
@[expose] def isPermK : List Nat → List Nat → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ => listContainsK l₂ a && isPermK l₁ (listEraseK l₂ a)

theorem isPermK_eq : ∀ (l₁ l₂ : List Nat), isPermK l₁ l₂ = l₁.isPerm l₂
  | [], _ => rfl
  | a :: l₁, l₂ => by
    rw [isPermK, List.isPerm, listContainsK_eq, listEraseK_eq, isPermK_eq l₁]

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ x, x ∈ l → p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a (List.mem_cons_self ..),
      find?_congr l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem map_atD_range {α : Type} (l : List Nat) (f : Nat → α) :
    (List.range l.length).map (fun i => f (atD l i 0)) = l.map f := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [atD_eq_getElem l i (by simpa using h2)]

theorem map_getBang_range {γ : Array Nat} {nn : Nat} (h : γ.size = nn) :
    (List.range nn).map (fun v => γ[v]!) = γ.toList := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, getBang_eq_atD]
  rw [atD_eq_getElem _ i (by simpa using h2)]

/-! # Target cell, breakout, and leaf machinery over packed state -/

@[expose] def discreteAtP (ctx : CtxP) (ptn level : Nat) : Bool :=
  (cellsP ctx ptn level).all fun p => Nat.beq p.1 p.2

theorem discreteAtP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn) (level : Nat) :
    discreteAtP ctx ptnP level = discreteAtL ptn level ctxL.n := by
  rw [discreteAtP, discreteAtL, cellsP_eq h hp]
  simp only [beq_eq_beq]

@[expose] def joinTestP (ctx : CtxP) (lab wset c1 c2 : Nat) : Bool :=
  let counts := countsOfP ctx lab wset c1 c2
  counts.any (fun c => Nat.blt 0 c) &&
    counts.any (fun c => Nat.blt c (popCountK wset))

theorem joinTestP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    (wset c1 c2 : Nat) :
    joinTestP ctx labP wset c1 c2 = joinTestL ctxL lab wset c1 c2 := by
  rw [joinTestP, joinTestL, countsOfP_eq h hl, popCountK_eq]
  simp only [blt_eq_decide]

@[expose] def specBestcellRowP (ctx : CtxP) (lab ptn level : Nat)
    (startArr : List Nat) (workset v2 : Nat) : List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v1 :: rest, bucket =>
    cond (joinTestP ctx lab workset (atD startArr v1 0)
        (cellEndP ctx ptn level (atD startArr v1 0)))
      (specBestcellRowP ctx lab ptn level startArr workset v2 rest
        ((bucket.set v1 (Nat.add (atD bucket v1 0) 1)).set v2
          (Nat.add (atD bucket v2 0) 1)))
      (specBestcellRowP ctx lab ptn level startArr workset v2 rest bucket)

theorem specBestcellRowP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) (startArr : List Nat) (workset v2 : Nat) :
    ∀ (vs bucket : List Nat),
      specBestcellRowP ctx labP ptnP level startArr workset v2 vs bucket =
        specBestcellRowL ctxL lab ptn level startArr workset v2 vs bucket
  | [], _ => rfl
  | v1 :: rest, bucket => by
    rw [specBestcellRowP, specBestcellRowL, joinTestP_eq h hl, cellEndP_eq h hp,
      cond_beq_true]
    simp only [add_eq]
    rcases Decidable.em (joinTestL ctxL lab workset (atD startArr v1 0)
        (cellEndL ptn level (atD startArr v1 0)) = true) with hj | hj
    · rw [ite_eq_left hj, ite_eq_left hj,
        specBestcellRowP_eq h hl hp level startArr workset v2 rest]
    · rw [ite_eq_right hj, ite_eq_right hj,
        specBestcellRowP_eq h hl hp level startArr workset v2 rest]

@[expose] def specBestcellRowsP (ctx : CtxP) (lab ptn level : Nat)
    (startArr : List Nat) : List Nat → List Nat → List Nat
  | [], bucket => bucket
  | v2 :: rest, bucket =>
    specBestcellRowsP ctx lab ptn level startArr rest
      (specBestcellRowP ctx lab ptn level startArr
        (worksetOfP ctx lab (atD startArr v2 0)
          (cellEndP ctx ptn level (atD startArr v2 0)))
        v2 (List.range v2) bucket)

theorem specBestcellRowsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level : Nat) (startArr : List Nat) : ∀ (vs bucket : List Nat),
      specBestcellRowsP ctx labP ptnP level startArr vs bucket =
        specBestcellRowsL ctxL lab ptn level startArr vs bucket
  | [], _ => rfl
  | v2 :: rest, bucket => by
    rw [specBestcellRowsP, specBestcellRowsL, worksetOfP_eq h hl, cellEndP_eq h hp,
      specBestcellRowP_eq h hl hp, specBestcellRowsP_eq h hl hp level startArr rest]

@[expose] def argmaxLoopK (bucket : List Nat) : List Nat → Nat → Nat → Nat
  | [], v1, _ => v1
  | i :: rest, v1, v2 =>
    cond (Nat.blt v2 (atD bucket i 0))
      (argmaxLoopK bucket rest i (atD bucket i 0))
      (argmaxLoopK bucket rest v1 v2)

theorem argmaxLoopK_eq (bucket : List Nat) : ∀ (vs : List Nat) (v1 v2 : Nat),
    argmaxLoopK bucket vs v1 v2 = argmaxLoopL bucket vs v1 v2
  | [], _, _ => rfl
  | i :: rest, v1, v2 => by
    rw [argmaxLoopK, argmaxLoopL, cond_blt]
    rcases Decidable.em (v2 < atD bucket i 0) with hl | hl
    · rw [ite_eq_left hl, ite_eq_left hl, argmaxLoopK_eq bucket rest]
    · rw [ite_eq_right hl, ite_eq_right hl, argmaxLoopK_eq bucket rest]

@[expose] def specBestcellP (ctx : CtxP) (lab ptn level : Nat) : Nat :=
  let starts := ((cellsP ctx ptn level).filter fun p => !Nat.beq p.1 p.2).map (·.1)
  let nnt := starts.length
  cond (Nat.beq nnt 0) ctx.n
    (let bucket := specBestcellRowsP ctx lab ptn level starts
      (List.range' 1 (Nat.sub nnt 1)) (List.replicate nnt 0)
    atD starts (argmaxLoopK bucket (List.range' 1 (Nat.sub nnt 1)) 0 (atD bucket 0 0)) 0)

theorem specBestcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn) (level : Nat) :
    specBestcellP ctx labP ptnP level = specBestcellL ctxL lab ptn level := by
  rw [specBestcellP, specBestcellL, cellsP_eq h hp]
  have hf : (fun p : Nat × Nat => !Nat.beq p.1 p.2) = fun x => decide (x.1 ≠ x.2) :=
    funext fun p => by rw [beq_eq_decide, decide_not]
  simp only [cond_beq, sub_eq, specBestcellRowsP_eq h hl hp, argmaxLoopK_eq, h.n,
    beq_iff_eq, hf]

/-- The start of the first nontrivial cell, `0` if every cell is a
singleton: the target-cell rule below the `tcLevel` cutoff. -/
@[expose] def firstNontrivialP : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => cond (Nat.beq p.1 p.2) (firstNontrivialP rest) p.1

@[expose] def specTargetcellP (ctx : CtxP) (lab ptn level tcLevel : Nat) : Nat :=
  cond (Nat.ble level tcLevel) (specBestcellP ctx lab ptn level)
    (firstNontrivialP (cellsP ctx ptn level))

theorem specTargetcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level tcLevel : Nat) :
    specTargetcellP ctx labP ptnP level tcLevel =
      specTargetcellL ctxL lab ptn level tcLevel := by
  rw [specTargetcellP, specTargetcellL, cellsP_eq h hp, cond_ble]
  rcases Decidable.em (level ≤ tcLevel) with hle | hle
  · rw [ite_eq_left hle, ite_eq_left hle, specBestcellP_eq h hl hp]
  · rw [ite_eq_right hle, ite_eq_right hle]
    generalize cellsL ptn level ctxL.n = cs
    induction cs with
    | nil => rfl
    | cons p rest ih =>
      rcases p with ⟨c1, c2⟩
      rw [firstNontrivialP, List.find?_cons, cond_beq]
      rcases Decidable.em (c1 = c2) with he | he
      · rw [ite_eq_left he, ih]
        simp [he]
      · rw [ite_eq_right he]
        simp [he]

@[expose] def specMaketargetcellP (ctx : CtxP) (lab ptn level tcLevel : Nat) :
    Nat × Nat × Nat :=
  let i := specTargetcellP ctx lab ptn level tcLevel
  let j := cellEndP ctx ptn level (Nat.add i 1)
  (i, worksetOfP ctx lab i j, Nat.add (Nat.sub j i) 1)

theorem specMaketargetcellP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    (level tcLevel : Nat) :
    specMaketargetcellP ctx labP ptnP level tcLevel =
      specMaketargetcellL ctxL lab ptn level tcLevel := by
  rw [specMaketargetcellP, specMaketargetcellL]
  simp only [specTargetcellP_eq h hl hp, cellEndP_eq h hp, worksetOfP_eq h hl,
    add_eq, sub_eq]

@[expose] def breakoutGoP (ctx : CtxP) (tv : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, lab, _, _ => lab
  | fuel + 1, lab, i, prev =>
    let next := lget ctx lab i
    let lab := lset ctx lab i prev
    cond (Nat.beq next tv) lab (breakoutGoP ctx tv fuel lab (Nat.add i 1) next)

theorem breakoutGoP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL) (tv : Nat) :
    ∀ (fuel : Nat) {labP : Nat} {lab : List Nat}, Rep ctx.w ctx.n labP lab →
      ∀ (i prev : Nat), prev < 2 ^ ctx.w →
      Rep ctx.w ctx.n (breakoutGoP ctx tv fuel labP i prev)
        (breakoutGoL tv fuel lab i prev)
  | 0, _, _, hl, _, _, _ => hl
  | fuel + 1, labP, lab, hl, i, prev, hprev => by
    rw [breakoutGoP, breakoutGoL]
    simp only [add_eq]
    have hn : lget ctx labP i = atD lab i 0 := lget_eq h hl i
    rw [hn, cond_beq]
    rcases Decidable.em (atD lab i 0 = tv) with he | he
    · rw [ite_eq_left he, ite_eq_left (by simpa using he)]
      exact lset_rep h hl i hprev
    · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
      exact breakoutGoP_rep h tv fuel (lset_rep h hl i hprev) (i + 1) _ (hl.small.atD i)

@[expose] def breakoutP (ctx : CtxP) (lab ptn level tc tv : Nat) : Nat × Nat × Nat :=
  (breakoutGoP ctx tv (Nat.add ctx.n 1) lab tc tv, lset ctx ptn tc level,
    insertK 0 tc)

theorem breakoutP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    {level : Nat} (hlev : level < 2 ^ ctx.w) (tc : Nat) {tv : Nat}
    (htv : tv < 2 ^ ctx.w) :
    Rep ctx.w ctx.n (breakoutP ctx labP ptnP level tc tv).1
        (breakoutL lab ptn level tc tv).1 ∧
      Rep ctx.w ctx.n (breakoutP ctx labP ptnP level tc tv).2.1
        (breakoutL lab ptn level tc tv).2.1 ∧
      (breakoutP ctx labP ptnP level tc tv).2.2 =
        (breakoutL lab ptn level tc tv).2.2 := by
  rw [breakoutP, breakoutL]
  refine ⟨?_, lset_rep h hp tc hlev, insertK_eq 0 tc⟩
  rw [hl.len, add_eq]
  exact breakoutGoP_rep h tv _ hl tc tv htv

@[expose] def segNP (ctx : CtxP) (lab lo len : Nat) : List Nat :=
  (List.range len).map fun o => lget ctx lab (Nat.add lo o)

theorem segNP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) (lo len : Nat) :
    segNP ctx labP lo len = segNL lab lo len := by
  rw [segNP, segNL]
  simp only [lget_eq h hl, add_eq]

/-- The packed image of a packed labelling under a packed permutation. -/
@[expose] def mapGammaP (ctx : CtxP) (γP lab : Nat) : Nat :=
  pack ctx.w ((List.range ctx.n).map fun i => lget ctx γP (lget ctx lab i))

theorem mapGammaP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {γP : Nat} {γl : List Nat} (hg : Rep ctx.w ctx.n γP γl)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    Rep ctx.w ctx.n (mapGammaP ctx γP labP) (lab.map fun v => atD γl v 0) := by
  rw [mapGammaP]
  have hs : Small ctx.w ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)) := by
    unfold Small
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact lget_lt h _ _
  have hlen : ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)).length =
      ctx.n := by simp
  have heq : ((List.range ctx.n).map fun i => lget ctx γP (lget ctx labP i)) =
      lab.map fun v => atD γl v 0 := by
    simp only [lget_eq h hg, lget_eq h hl]
    rw [← hl.len]
    exact map_atD_range lab fun v => atD γl v 0
  exact ⟨by rw [← heq]; exact hlen, by rw [← heq]; exact hs, by rw [heq]⟩

@[expose] def checkCellsPermP (ctx : CtxP) (ptn lab₁ lab₂' level : Nat) : Bool :=
  (cellsP ctx ptn level).all fun p =>
    isPermK (segNP ctx lab₁ p.1 (Nat.sub (Nat.add p.2 1) p.1))
      (segNP ctx lab₂' p.1 (Nat.sub (Nat.add p.2 1) p.1))

theorem checkCellsPermP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {ptnP : Nat} {ptn : List Nat} (hp : Rep ctx.w ctx.n ptnP ptn)
    {lab₁P : Nat} {lab₁ : List Nat} (h1 : Rep ctx.w ctx.n lab₁P lab₁)
    {lab₂P : Nat} {lab₂ : List Nat} (h2 : Rep ctx.w ctx.n lab₂P lab₂) (level : Nat) :
    checkCellsPermP ctx ptnP lab₁P lab₂P level =
      checkCellsPermL ptn lab₁ lab₂ level ctxL.n := by
  rw [checkCellsPermP, checkCellsPermL, cellsP_eq h hp]
  simp only [isPermK_eq, segNP_eq h h1, segNP_eq h h2, add_eq, sub_eq]

@[expose] def invPermGoP (ctx : CtxP) (lab : Nat) : List Nat → Nat → Nat
  | [], inv => inv
  | i :: rest, inv => invPermGoP ctx lab rest (lset ctx inv (lget ctx lab i) i)

theorem invPermGoP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    ∀ (idx : List Nat), (∀ i, i ∈ idx → i < 2 ^ ctx.w) →
      ∀ {invP : Nat} {inv : List Nat}, Rep ctx.w ctx.n invP inv →
      Rep ctx.w ctx.n (invPermGoP ctx labP idx invP) (invPermGoL lab idx inv)
  | [], _, _, _, hi => hi
  | i :: rest, hidx, _, _, hi => by
    rw [invPermGoP, invPermGoL, lget_eq h hl]
    exact invPermGoP_rep h hl rest (fun j hj => hidx j (List.mem_cons_of_mem _ hj))
      (lset_rep h hi _ (hidx i (List.mem_cons_self ..)))

@[expose] def invPermP (ctx : CtxP) (lab : Nat) : Nat :=
  invPermGoP ctx lab (List.range ctx.n) 0

theorem invPermP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    Rep ctx.w ctx.n (invPermP ctx labP) (invPermL lab) := by
  rw [invPermP, invPermL, hl.len]
  refine invPermGoP_rep h hl _ (fun i hi => ?_) (Rep.replicate ctx.w ctx.n)
  have := List.mem_range.mp hi
  have := h.nlt
  omega

@[expose] def permsetP (ctx : CtxP) (s perm : Nat) : Nat :=
  (List.range ctx.n).foldl
    (fun acc v => cond (elemK s v) (insertK acc (lget ctx perm v)) acc) 0

theorem permsetP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {permP : Nat} {perm : List Nat} (hp : Rep ctx.w ctx.n permP perm) (s : Nat) :
    permsetP ctx s permP = permsetL s perm ctxL.n := by
  rw [permsetP, permsetL, h.n]
  congr 1
  funext acc v
  rw [elemK_eq, cond_beq_true, insertK_eq, lget_eq h hp]
  rfl

@[expose] def leafRowsP (ctx : CtxP) (lab : Nat) : List Nat :=
  let inv := invPermP ctx lab
  (List.range ctx.n).map fun i => permsetP ctx (rowP ctx (lget ctx lab i)) inv

theorem leafRowsP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {labP : Nat} {lab : List Nat} (hl : Rep ctx.w ctx.n labP lab) :
    leafRowsP ctx labP = leafRowsL ctxL lab := by
  rw [leafRowsP, leafRowsL]
  simp only [permsetP_eq h (invPermP_rep h hl), rowP_eq h, lget_eq h hl, h.n]

/-! # Automorphism validation over packed state -/

@[expose] def imageP (σ : Nat → Nat) (n s : Nat) : Nat :=
  (List.range n).foldl (fun t v => cond (elemK s v) (insertK t (σ v)) t) 0

theorem imageP_eq (σ : Nat → Nat) (n s : Nat) : imageP σ n s = image σ n s := by
  rw [imageP, image]
  congr 1
  funext t v
  rw [elemK_eq, cond_beq_true, insertK_eq]
  rfl

/-- A candidate permutation array has `n` entries, all vertices. -/
@[expose] def gammaOkP (ctx : CtxP) (γl : List Nat) : Bool :=
  Nat.beq γl.length ctx.n && γl.all fun v => Nat.blt v ctx.n

theorem gammaOkP_rep {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {γl : List Nat} (hok : gammaOkP ctx γl = true) :
    Rep ctx.w ctx.n (pack ctx.w γl) γl := by
  rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hok
  refine ⟨hok.1, fun x hx => ?_, rfl⟩
  have := Nat.blt_eq.mp (hok.2 x hx)
  have := h.nlt
  omega

@[expose] def checkAutomP (ctx : CtxP) (γ : Array Nat) : Bool :=
  let γl := γ.toList
  gammaOkP ctx γl &&
    (let γP := pack ctx.w γl
    isPermK γl (List.range ctx.n) &&
      (List.range ctx.n).all fun v =>
        Nat.beq (rowP ctx (lget ctx γP v))
          (imageP (fun w => lget ctx γP w) ctx.n (rowP ctx v)))

theorem gammaOkP_of_checkAutom {ctx : CtxP} {nn : Nat} {g : Array Nat}
    (h : CtxRep ctx (Ctx.toL ⟨nn, g⟩)) {γ : Array Nat}
    (hc : checkAutom g γ nn = true) : gammaOkP ctx γ.toList = true := by
  rw [checkAutom, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hsize, hsmall⟩, _⟩, _⟩ := hc
  rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Array.length_toList,
    hsize, h.n]
  refine ⟨rfl, fun x hx => ?_⟩
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Array.length_toList, hsize] at hi
  have := of_decide_eq_true (hsmall i (List.mem_range.mpr hi))
  rw [getBang_eq_atD, atD_eq_getElem _ i (by simpa [hsize] using hi)] at this
  exact Nat.blt_eq.mpr this

theorem checkAutomP_eq {ctx : CtxP} {nn : Nat} {g : Array Nat}
    (h : CtxRep ctx (Ctx.toL ⟨nn, g⟩)) (γ : Array Nat) :
    checkAutomP ctx γ = checkAutom g γ nn := by
  have hrow : ∀ v, rowP ctx v = g[v]! := fun v => by
    rw [rowP_eq h, getBang_eq_atD]
    rfl
  rcases hok : gammaOkP ctx γ.toList with _ | _
  · rw [checkAutomP]
    simp only [hok, Bool.false_and]
    rcases hc : checkAutom g γ nn with _ | _
    · rfl
    · rw [gammaOkP_of_checkAutom h hc] at hok
      cases hok
  · have hrep := gammaOkP_rep h hok
    have hok' := hok
    rw [gammaOkP, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true,
      Array.length_toList] at hok'
    have hsize : γ.size = nn := by rw [hok'.1, h.n]; rfl
    have hget : ∀ v, lget ctx (pack ctx.w γ.toList) v = γ[v]! := fun v => by
      rw [lget_eq h hrep, getBang_eq_atD]
    have hbound : ∀ v, v ∈ List.range nn → (γ[v]! : Nat) < nn := fun v hv => by
      have hmem : (γ[v]! : Nat) ∈ γ.toList := by
        rw [getBang_eq_atD, atD_eq_getElem _ v (by
          rw [Array.length_toList, hsize]; exact List.mem_range.mp hv)]
        exact List.getElem_mem _
      have := Nat.blt_eq.mp (hok'.2 _ hmem)
      rw [h.n] at this
      exact this
    rw [checkAutomP, checkAutom, Bool.eq_iff_iff]
    simp only [hok, Bool.true_and, Bool.and_eq_true, hget, hrow, isPermK_eq,
      imageP_eq, h.n, Ctx.toL, map_getBang_range hsize, beq_iff_eq, Nat.beq_eq,
      List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hperm, himgs⟩
      exact ⟨⟨⟨hsize, hbound⟩, hperm⟩, himgs⟩
    · rintro ⟨⟨_, hperm⟩, himgs⟩
      exact ⟨hperm, himgs⟩

@[expose] def validGammasP (ctx : CtxP) (cert : CertNode) : List Nat :=
  ((certGammas (Nat.add ctx.n 2) cert []).filter (checkAutomP ctx)).map
    fun γ => pack ctx.w γ.toList

theorem validGammasP_eq {ctx : CtxP} {nn : Nat} {g : Array Nat}
    (h : CtxRep ctx (Ctx.toL ⟨nn, g⟩)) (cert : CertNode) :
    validGammasP ctx cert = (validGammas g nn cert).map fun γ => pack ctx.w γ.toList := by
  rw [validGammasP, validGammas, add_eq, h.n]
  congr 1
  exact List.filter_congr fun γ _ => checkAutomP_eq h γ

/-- Membership of a certificate's permutation among the validated
generators, on packed numbers: the array must have `n` vertex entries
(so the packing is faithful) and its packing must appear. -/
@[expose] def containsGammaP (ctx : CtxP) (vgens : List Nat) (γ : Array Nat) : Bool :=
  gammaOkP ctx γ.toList && vgens.any (Nat.beq (pack ctx.w γ.toList))

theorem containsGamma_of_mem : ∀ {vgens : List (Array Nat)} {γ : Array Nat},
    γ ∈ vgens → containsGamma vgens γ = true
  | g :: rest, γ, hmem => by
    rw [containsGamma, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl (by rw [gammaEq]; exact beq_self_eq_true _)
    · exact Or.inr (containsGamma_of_mem hmem)

theorem containsGammaP_eq {ctx : CtxP} {nn : Nat} {g : Array Nat}
    (h : CtxRep ctx (Ctx.toL ⟨nn, g⟩)) (cert : CertNode) (γ : Array Nat) :
    containsGammaP ctx (validGammasP ctx cert) γ =
      containsGamma (validGammas g nn cert) γ := by
  rw [Bool.eq_iff_iff, containsGammaP, validGammasP_eq h, Bool.and_eq_true,
    List.any_eq_true]
  constructor
  · rintro ⟨hok, x, hx, hbeq⟩
    rw [List.mem_map] at hx
    obtain ⟨g', hg', rfl⟩ := hx
    have hc := validGammas_sound hg'
    have hrep := gammaOkP_rep h hok
    have hrep' := gammaOkP_rep h (gammaOkP_of_checkAutom h hc)
    have heq : γ.toList = g'.toList :=
      pack_injective ctx.w _ _ hrep.small hrep'.small (by rw [hrep.len, hrep'.len])
        (Nat.eq_of_beq_eq_true hbeq)
    rw [Array.toList_inj] at heq
    rw [heq]
    exact containsGamma_of_mem hg'
  · intro hc
    have hmem := containsGamma_mem hc
    refine ⟨gammaOkP_of_checkAutom h (validGammas_sound hmem), pack ctx.w γ.toList,
      List.mem_map.mpr ⟨γ, hmem, rfl⟩, Nat.beq_refl _⟩

/-! # The certificate replay over packed state -/

@[expose] def checkNodeP (ctx : CtxP) (tcLevel : Nat) (brows : List Nat)
    (vgens : List Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → CertNode → List Nat → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes =>
    match bcodes with
    | [] => none
    | bc :: brest =>
      let rs := refineP ctx level lab ptn active numcells
      match cert with
      | .autom _ _ => none
      | .codePrune => cond (Nat.blt rs.longcode bc) (some false) none
      | .leaf =>
        cond (Nat.blt rs.longcode bc) (some false)
          (cond (Nat.beq rs.longcode bc)
            (cond (discreteAtP ctx rs.ptn level)
              (match keyCmp
                ⟨[rs.longcode, codeSentinel], leafRowsP ctx rs.lab⟩
                ⟨bc :: brest, brows⟩ with
              | .gt => none
              | .eq => some true
              | .lt => some false)
              none)
            none)
      | .node children =>
        cond (Nat.blt rs.longcode bc) (some false)
          (cond (Nat.beq rs.longcode bc)
            (cond (discreteAtP ctx rs.ptn level) none
              (let tcr := specMaketargetcellP ctx rs.lab rs.ptn level tcLevel
              cond (Nat.beq children.length tcr.2.2)
                ((children.zipIdx 0).foldl
                  (fun acc (co : CertNode × Nat) =>
                    match acc with
                    | none => none
                    | some a =>
                      let br := breakoutP ctx rs.lab rs.ptn (Nat.add level 1) tcr.1
                        (lget ctx rs.lab (Nat.add tcr.1 co.2))
                      match
                        match co.1 with
                        | .autom o' γ =>
                          cond (Nat.blt o' co.2 &&
                              containsGammaP ctx vgens γ &&
                              checkCellsPermP ctx br.2.1
                                (breakoutP ctx rs.lab rs.ptn (Nat.add level 1)
                                  tcr.1 (lget ctx rs.lab (Nat.add tcr.1 o'))).1
                                (mapGammaP ctx (pack ctx.w γ.toList) br.1)
                                (Nat.add level 1))
                            (some false) none
                        | _ =>
                          checkNodeP ctx tcLevel brows vgens fuel (Nat.add level 1)
                            br.1 br.2.1 br.2.2 (Nat.add rs.numcells 1) co.1 brest
                      with
                      | none => none
                      | some a' => some (a || a'))
                  (some false))
                none))
            none)
  termination_by structural fuel => fuel

theorem checkNodeP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    (tcLevel : Nat) (brows : List Nat) {vgensP : List Nat}
    {vgens : List (Array Nat)}
    (hcont : ∀ γ, containsGammaP ctx vgensP γ = containsGamma vgens γ) :
    ∀ (fuel level : Nat), level + fuel ≤ ctx.n + 1 →
      ∀ {labP : Nat} {lab : List Nat}, Rep ctx.w ctx.n labP lab →
      ∀ {ptnP : Nat} {ptn : List Nat}, Rep ctx.w ctx.n ptnP ptn →
      ∀ (active numcells : Nat) (cert : CertNode) (bcodes : List Nat),
      checkNodeP ctx tcLevel brows vgensP fuel level labP ptnP active numcells
        cert bcodes =
      checkNodeL ctxL tcLevel brows vgens fuel level lab ptn active numcells
        cert bcodes
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, level, hlev, labP, lab, hl, ptnP, ptn, hp, active, numcells, cert,
      bcodes => by
    have hlev1 : level < 2 ^ ctx.w := by have := h.nlt; omega
    have hlev2 : level + 1 < 2 ^ ctx.w := by have := h.nlt; omega
    have hrs := refineP_eq h hlev1 hl hp active numcells
    cases bcodes with
    | nil => rfl
    | cons bc brest =>
      have hcode : (refineP ctx level labP ptnP active numcells).longcode =
          (refineL ctxL level lab ptn active numcells).longcode := hrs.longcode
      have hdisc := discreteAtP_eq h hrs.ptn level
      rcases hcmp : compare (refineL ctxL level lab ptn active numcells).longcode bc
        with _ | _ | _
      · -- lt
        have hlt := Nat.compare_eq_lt.mp hcmp
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            true := by rw [blt_eq_decide, decide_eq_true hlt]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp, ite_true]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp]
        | node children =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_true, hcmp]
      · -- eq
        have heq := Nat.compare_eq_eq.mp hcmp
        have hnlt : ¬ (refineL ctxL level lab ptn active numcells).longcode < bc := by
          omega
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [blt_eq_decide, decide_eq_false hnlt]
        have hbeq : Nat.beq (refineL ctxL level lab ptn active numcells).longcode bc =
            true := by rw [beq_eq_decide, decide_eq_true heq]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_false, hcmp, reduceCtorEq, ite_false]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, Bool.cond_true, hcmp, hdisc,
            leafRowsP_eq h hrs.lab]
          rw [cond_beq_true]
          congr 1
        | node children =>
          have hfold : ∀ (rsLabP rsPtnP : Nat) (rsLab rsPtn : List Nat),
              Rep ctx.w ctx.n rsLabP rsLab → Rep ctx.w ctx.n rsPtnP rsPtn →
              ∀ (tc m : Nat) (cs : List (CertNode × Nat)) (acc : Option Bool),
              cs.foldl
                (fun acc (co : CertNode × Nat) =>
                  match acc with
                  | none => none
                  | some a =>
                    match
                      match co.1 with
                      | .autom o' γ =>
                        cond (Nat.blt o' co.2 &&
                            containsGammaP ctx vgensP γ &&
                            checkCellsPermP ctx
                              (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                                (lget ctx rsLabP (Nat.add tc co.2))).2.1
                              (breakoutP ctx rsLabP rsPtnP (Nat.add level 1)
                                tc (lget ctx rsLabP (Nat.add tc o'))).1
                              (mapGammaP ctx (pack ctx.w γ.toList)
                                (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                                  (lget ctx rsLabP (Nat.add tc co.2))).1)
                              (Nat.add level 1))
                          (some false) none
                      | _ =>
                        checkNodeP ctx tcLevel brows vgensP fuel (Nat.add level 1)
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).1
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).2.1
                          (breakoutP ctx rsLabP rsPtnP (Nat.add level 1) tc
                            (lget ctx rsLabP (Nat.add tc co.2))).2.2
                          (Nat.add m 1) co.1 brest
                    with
                    | none => none
                    | some a' => some (a || a')) acc =
              cs.foldl
                (fun acc (co : CertNode × Nat) =>
                  match acc with
                  | none => none
                  | some a =>
                    match
                      match co.1 with
                      | .autom o' γ =>
                        if o' < co.2 &&
                            containsGamma vgens γ &&
                            checkCellsPermL
                              (breakoutL rsLab rsPtn (level + 1) tc
                                (atD rsLab (tc + co.2) 0)).2.1
                              (breakoutL rsLab rsPtn (level + 1)
                                tc (atD rsLab (tc + o') 0)).1
                              ((breakoutL rsLab rsPtn (level + 1) tc
                                (atD rsLab (tc + co.2) 0)).1.map
                                fun w => atD γ.toList w 0)
                              (level + 1) ctxL.n then
                          some false
                        else
                          none
                      | _ =>
                        checkNodeL ctxL tcLevel brows vgens fuel (level + 1)
                          (breakoutL rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).1
                          (breakoutL rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).2.1
                          (breakoutL rsLab rsPtn (level + 1) tc
                            (atD rsLab (tc + co.2) 0)).2.2
                          (m + 1) co.1 brest
                    with
                    | none => none
                    | some a' => some (a || a')) acc := by
            intro rsLabP rsPtnP rsLab rsPtn hrl hrp tc m cs
            induction cs with
            | nil => intro acc; rfl
            | cons co rest ih =>
              intro acc
              rw [List.foldl_cons, List.foldl_cons]
              rcases acc with _ | a
              · rw [ih]
              · rw [ih]
                congr 1
                rcases co with ⟨c, o⟩
                have hbr := breakoutP_eq h hrl hrp hlev2 tc (lget_lt h rsLabP (tc + o))
                rw [lget_eq h hrl] at hbr
                obtain ⟨hbr1, hbr2, hbr3⟩ := hbr
                cases c with
                | leaf =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | codePrune =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | node ch =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hbr3, checkNodeP_eq h tcLevel brows hcont fuel (level + 1)
                    (by omega) hbr1 hbr2]
                | autom o' γ =>
                  simp only [add_eq, lget_eq h hrl]
                  rw [hcont γ, blt_eq_decide]
                  rcases hg : containsGamma vgens γ with _ | _
                  · simp
                  · have hok : gammaOkP ctx γ.toList = true := by
                      have := hcont γ
                      rw [hg, containsGammaP, Bool.and_eq_true] at this
                      exact this.1
                    have hγ := gammaOkP_rep h hok
                    have hbr' := breakoutP_eq h hrl hrp hlev2 tc
                      (lget_lt h rsLabP (tc + o'))
                    rw [lget_eq h hrl] at hbr'
                    rw [checkCellsPermP_eq h hbr2 hbr'.1 (mapGammaP_rep h hγ hbr1),
                      cond_beq_true]
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, Bool.cond_true, hcmp, hdisc,
            specMaketargetcellP_eq h hrs.lab hrs.ptn, hrs.numcells]
          rw [cond_beq_true]
          congr 1
          rw [cond_beq]
          congr 1
          exact hfold _ _ _ _ hrs.lab hrs.ptn _ _ (children.zipIdx 0) (some false)
      · -- gt
        have hgt := Nat.compare_eq_gt.mp hcmp
        have hnlt : ¬ (refineL ctxL level lab ptn active numcells).longcode < bc := by
          omega
        have hne : ¬ (refineL ctxL level lab ptn active numcells).longcode = bc := by
          omega
        have hblt : Nat.blt (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [blt_eq_decide, decide_eq_false hnlt]
        have hbeq : Nat.beq (refineL ctxL level lab ptn active numcells).longcode bc =
            false := by rw [beq_eq_decide, decide_eq_false hne]
        cases cert with
        | autom o γ => rfl
        | codePrune =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, Bool.cond_false, hcmp, reduceCtorEq, ite_false]
        | leaf =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, hcmp]
        | node children =>
          rw [checkNodeP, checkNodeL]
          simp only [hcode, hblt, hbeq, Bool.cond_false, hcmp]
  termination_by structural fuel => fuel


/-! # The negative kernel obligation over packed state -/

end Hex.GraphIso.Nauty

namespace Hex.GraphIso

open Nauty

variable {n k : Nat}

theorem mem_toList_lt {a : Array Nat} {b : Nat}
    (h : ∀ i, i < a.size → a[i]! < b) : ∀ x, x ∈ a.toList → x < b := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Array.length_toList] at hi
  have := h i hi
  rw [getBang_eq_atD, atD_eq_getElem _ i (by simpa using hi)] at this
  exact this

theorem size_flatRows (nn : Nat) (flat : List Bool) : (flatRows nn flat).size = nn := by
  rw [flatRows, List.size_toArray, List.length_map, chunkRows_length]

theorem flatRows_small (nn : Nat) (flat : List Bool) :
    ∀ r, r ∈ (flatRows nn flat).toList → r < 2 ^ nn := by
  intro r hr
  rw [flatRows, List.toList_toArray, List.mem_map] at hr
  obtain ⟨seg, _, rfl⟩ := hr
  have hfold : ∀ (l : List Nat) (acc : Nat), (∀ j, j ∈ l → j < nn) → acc < 2 ^ nn →
      l.foldl (fun row j => if atD seg j false then Nauty.insert row j else row) acc <
        2 ^ nn := by
    intro l
    induction l with
    | nil => intro acc _ h; simpa using h
    | cons j rest ih =>
      intro acc hl hacc
      rw [List.foldl_cons]
      refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
      split
      · rw [Nauty.insert, Nat.one_shiftLeft]
        exact Nat.or_lt_two_pow hacc
          (Nat.pow_lt_pow_right (by decide) (hl j (List.mem_cons_self ..)))
      · exact hacc
  exact hfold _ 0 (fun j hj => List.mem_range.mp hj) (Nat.two_pow_pos nn)

/-! # Rows packed from the flat literal

`flatRows` rebuilds each row by probing its segment position by
position, a spine walk per bit; `rowOfSegK` reads the segment once. -/

/-- The bit set of a row segment whose head sits at position `j`. -/
@[expose] def rowOfSegK : List Bool → Nat → Nat
  | [], _ => 0
  | b :: rest, j =>
    cond b (insertK (rowOfSegK rest (Nat.add j 1)) j) (rowOfSegK rest (Nat.add j 1))

theorem atD_of_length_le {α : Type} : ∀ (l : List α) (i : Nat) (d : α),
    l.length ≤ i → atD l i d = d
  | [], _, _, _ => by rw [atD]
  | _ :: l, i + 1, d, h => by
    rw [atD]
    exact atD_of_length_le l i d (by simpa using h)

theorem testBit_rowOfSegK : ∀ (seg : List Bool) (j i : Nat),
    (rowOfSegK seg j).testBit i = (decide (j ≤ i) && atD seg (i - j) false)
  | [], j, i => by
    rw [rowOfSegK, Nat.zero_testBit, atD_of_length_le _ _ _ (Nat.zero_le _)]
    simp
  | b :: rest, j, i => by
    rw [rowOfSegK, add_eq]
    have ih := testBit_rowOfSegK rest (j + 1) i
    rcases b with _ | _
    · rw [Bool.cond_false, ih]
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · simp [Nat.not_le.mpr h, show ¬ j + 1 ≤ i by omega]
      · simp [Nat.sub_self, atD, Nat.not_succ_le_self]
      · have hsub : i - j = (i - (j + 1)) + 1 := by omega
        rw [hsub, atD]
        simp [show j ≤ i by omega, show j + 1 ≤ i by omega]
    · rw [Bool.cond_true, insertK_eq, Nauty.insert, Nat.one_shiftLeft, Nat.testBit_or,
        Nat.testBit_two_pow, ih]
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · simp [Nat.not_le.mpr h, show ¬ j + 1 ≤ i by omega, Nat.ne_of_gt h]
      · simp [Nat.sub_self, atD]
      · have hsub : i - j = (i - (j + 1)) + 1 := by omega
        rw [hsub, atD]
        simp [show j ≤ i by omega, show j + 1 ≤ i by omega, Nat.ne_of_lt h]

theorem testBit_rowFold (seg : List Bool) : ∀ (len a acc i : Nat),
    ((List.range' a len).foldl
      (fun row j => if atD seg j false then Nauty.insert row j else row) acc).testBit i =
      (acc.testBit i || (decide (a ≤ i ∧ i < a + len) && atD seg i false))
  | 0, a, acc, i => by
    simp only [List.range'_zero, List.foldl_nil, Nat.add_zero]
    have : ¬ (a ≤ i ∧ i < a) := by omega
    simp [this]
  | len + 1, a, acc, i => by
    rw [List.range'_succ, List.foldl_cons, testBit_rowFold seg len (a + 1) _ i]
    have hrange : decide (a + 1 ≤ i ∧ i < a + 1 + len) =
        (decide (a ≤ i ∧ i < a + (len + 1)) && decide (i ≠ a)) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq]
      omega
    rcases hs : atD seg a false with _ | _
    · rw [ite_eq_right (by simp [hs]), hrange]
      rcases Decidable.em (i = a) with rfl | hne
      · simp [hs]
      · simp [hne]
    · rw [ite_eq_left (by simp [hs]), Nauty.insert, Nat.one_shiftLeft, Nat.testBit_or,
        Nat.testBit_two_pow, hrange]
      rcases Decidable.em (i = a) with rfl | hne
      · simp [hs]
      · simp [hne, Ne.symm hne]

theorem rowOfSegK_eq (nn : Nat) (seg : List Bool) (hlen : seg.length ≤ nn) :
    rowOfSegK seg 0 =
      (List.range nn).foldl
        (fun row j => if atD seg j false then Nauty.insert row j else row) 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_rowOfSegK, List.range_eq_range', testBit_rowFold, Nat.zero_testBit,
    Nat.sub_zero]
  rcases Decidable.em (i < nn) with hi | hi
  · simp [hi]
  · rw [atD_of_length_le _ _ _ (by omega)]
    simp

theorem chunkRows_length_le (m : Nat) : ∀ (r : Nat) (l : List Bool) (seg : List Bool),
    seg ∈ chunkRows r m l → seg.length ≤ m
  | 0, _, _, h => absurd h List.not_mem_nil
  | r + 1, l, seg, h => by
    rw [chunkRows, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.length_take_le ..
    · exact chunkRows_length_le m r _ seg h

/-- The rows packed with width `n`, read off the flat literal one
segment at a time. -/
@[expose] def packRowsK (nn : Nat) (flat : List Bool) : Nat :=
  pack nn ((chunkRows nn nn flat).map fun seg => rowOfSegK seg 0)

theorem packRowsK_eq (nn : Nat) (flat : List Bool) :
    packRowsK nn flat = pack nn (flatRows nn flat).toList := by
  rw [packRowsK, flatRows, List.toList_toArray]
  congr 1
  exact List.map_congr_left fun seg hseg =>
    rowOfSegK_eq nn seg (chunkRows_length_le nn nn flat seg hseg)

/-- `checkKeyLit` with packed state end to end: the rows packed once
from the tied flat literal, the labelling and partition packed with
the field width `w` sized for positions, the initial partition's
infinity `n + 2`, and every level the replay fuel of `n` reaches. The
negative route's kernel obligation. -/
@[expose] def checkKeyP (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (B : Key) : Bool :=
  if n == 0 then
    B.codes == [] && B.rows == []
  else
    let w := Nat.log2 (n + 2) + 1
    let ctx : CtxP := ⟨n, w, 2 ^ w - 1, packRowsK n flat, 2 ^ n - 1⟩
    checkNodeP ctx 100 B.rows (validGammasP ctx cert) n 1
      (pack w (initialPartition G).1.toList)
      (pack w (initPtn n (n + 2) (initialPartition G).2).toList)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length cert B.codes = some true

theorem checkKeyP_eq (G : Colored n k) (flat : List Bool)
    (cert : CertNode) (B : Key) :
    checkKeyP G flat cert B = checkKeyLit G flat cert B := by
  rw [checkKeyP, checkKeyLit]
  rcases Decidable.em (n = 0) with hn | hn
  · rw [ite_eq_left (by simpa using hn), ite_eq_left (by simpa using hn)]
  · rw [ite_eq_right (by simpa using hn), ite_eq_right (by simpa using hn)]
    dsimp only
    rw [packRowsK_eq]
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    have hok := initial_nodeOk G hn0
    have hw : n + 2 < 2 ^ (Nat.log2 (n + 2) + 1) := Nat.lt_log2_self
    have hctx : CtxRep
        ⟨n, Nat.log2 (n + 2) + 1, 2 ^ (Nat.log2 (n + 2) + 1) - 1,
          pack n (flatRows n flat).toList, 2 ^ n - 1⟩
        (Ctx.toL ⟨n, flatRows n flat⟩) :=
      { n := rfl
        m := rfl
        rm := rfl
        g := ⟨by show (flatRows n flat).toList.length = n
                 rw [Array.length_toList, size_flatRows],
          flatRows_small n flat, rfl⟩
        nlt := by show n + 2 < 2 ^ (Nat.log2 (n + 2) + 1); exact hw }
    have hlab : Rep (Nat.log2 (n + 2) + 1) n
        (pack (Nat.log2 (n + 2) + 1) (initialPartition G).1.toList)
        (initialPartition G).1.toList :=
      ⟨by rw [Array.length_toList, hok.labSize],
        fun x hx => Nat.lt_trans (mem_toList_lt hok.labOk x hx) (by omega), rfl⟩
    have hptn : Rep (Nat.log2 (n + 2) + 1) n
        (pack (Nat.log2 (n + 2) + 1)
          (initPtn n (n + 2) (initialPartition G).2).toList)
        (initPtn n (n + 2) (initialPartition G).2).toList :=
      ⟨by rw [Array.length_toList, hok.ptnSize], fun x hx => ?_, rfl⟩
    · rw [checkNodeP_eq hctx 100 B.rows (containsGammaP_eq hctx cert) n 1
        (by show 1 + n ≤ n + 1; omega) hlab hptn]
    · rw [List.mem_iff_getElem] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      have hv := hok.vals q
      rw [getBang_eq_atD, atD_eq_getElem _ q hq] at hv
      omega

/-- Tying equalities plus two packed-state key certificates with
differing keys prove non-isomorphism: `not_isomorphic_of_checkKeysL`
with the replay over packed state. -/
theorem not_isomorphic_of_checkKeysP {G H : Colored n k}
    {certG certH : Nauty.CertNode} {BG BH : Nauty.Key}
    {LA LB : List Bool}
    (hA : G.graph.adjMatrix.data.toList = LA)
    (hB : H.graph.adjMatrix.data.toList = LB)
    (hG : checkKeyP G LA certG BG = true)
    (hH : checkKeyP H LB certH BH = true)
    (hd : Nauty.checkDiff BG BH = true) : ¬Isomorphic G H := by
  rw [checkKeyP_eq] at hG hH
  exact not_isomorphic_of_checkKeysL hA hB hG hH hd

end Hex.GraphIso
