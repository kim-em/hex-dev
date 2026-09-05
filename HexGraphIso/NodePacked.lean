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
      (by simp [hst.numcells, hst.hint, hst.maxpos, hst.longcode])

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

end Hex.GraphIso.Nauty
