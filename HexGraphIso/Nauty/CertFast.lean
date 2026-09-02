/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert

public section

/-!
A replay-cost clone of the certificate checker for kernel use. The
trusted `checkNode`/`checkChildren` repeat `refine` and `breakout`
applications syntactically; each repetition is a distinct term, so the
kernel's by-pointer whnf cache recomputes them, multiplying replay
cost by roughly the repetition count. `checkNodeF`/`checkChildrenF`
bind those applications once with `let`, whose kernel zeta reduction
substitutes a single shared term, and are proven equal to the trusted
checkers node by node — so `checkKeyF` obligations carry exactly the
trusted semantics at a fraction of the replay cost. Nothing here
extends the trusted base: soundness flows through `checkKeyF_eq` into
`checkKey_sound`.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

mutual

/-- `checkNode` with the per-node `refine` and target-cell results
bound once, for shared kernel reduction. -/
@[expose] def checkNodeF (ctx : Ctx) (tcLevel : Nat) (brows : List Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → CertNode →
      List Nat → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes =>
    match bcodes with
    | [] => none
    | bc :: brest =>
      let rs := refine ctx level lab ptn active numcells
      match cert with
      | .autom _ _ => none
      | .codePrune =>
        if compare rs.longcode bc = .lt then
          some false
        else
          none
      | .leaf =>
        match compare rs.longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAt rs.ptn level ctx.n then
            match keyCmp
              ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
              ⟨bc :: brest, brows⟩ with
            | .gt => none
            | .eq => some true
            | .lt => some false
          else
            none
      | .node children =>
        match compare rs.longcode bc with
        | .gt => none
        | .lt => some false
        | .eq =>
          if discreteAt rs.ptn level ctx.n then
            none
          else
            let tcr := specMaketargetcell ctx rs.lab rs.ptn level
              tcLevel
            if children.length = tcr.2.2 then
              checkChildrenF ctx tcLevel brows fuel level rs.lab
                rs.ptn tcr.1 numcells brest children 0
            else
              none

/-- `checkChildren` with the current offset's `breakout` bound once,
for shared kernel reduction. -/
@[expose] def checkChildrenF (ctx : Ctx) (tcLevel : Nat)
    (brows : List Nat) (fuel level : Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) (brest : List Nat) :
    List CertNode → Nat → Option Bool
  | [], _ => some false
  | c :: rest, o =>
    let br := breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!
    match
      match c with
      | .autom o' γ =>
        if o' < o &&
            checkAutom ctx.g γ ctx.n &&
            checkCellsPerm br.2.1
              (breakout rsLab rsPtn (level + 1) tc
                rsLab[tc + o']!).1
              (br.1.map fun w => γ[w]!)
              (level + 1) ctx.n then
          some false
        else
          none
      | _ =>
        checkNodeF ctx tcLevel brows fuel (level + 1) br.1 br.2.1
          br.2.2 (numcells + 1) c brest
    with
    | none => none
    | some a =>
      match checkChildrenF ctx tcLevel brows fuel level rsLab rsPtn tc
          numcells brest rest (o + 1) with
      | none => none
      | some a' => some (a || a')

end

mutual

/-- The fast checker replays exactly the trusted checker. -/
theorem checkNodeF_eq (ctx : Ctx) (tcLevel : Nat) (brows : List Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (cert : CertNode) (bcodes : List Nat),
      checkNodeF ctx tcLevel brows fuel level lab ptn active numcells
        cert bcodes =
        checkNode ctx tcLevel brows fuel level lab ptn active numcells
          cert bcodes
  | 0, _, _, _, _, _, _, _ => by
    rw [checkNodeF, checkNode]
  | fuel + 1, level, lab, ptn, active, numcells, cert, bcodes => by
    cases bcodes with
    | nil => rw [checkNodeF, checkNode]
    | cons bc brest =>
      cases cert with
      | autom o' γ => rw [checkNodeF, checkNode]
      | codePrune => simp only [checkNodeF, checkNode]
      | leaf =>
        simp only [checkNodeF, checkNode]
        rfl
      | node children =>
        simp only [checkNodeF, checkNode]
        rw [checkChildrenF_eq ctx tcLevel brows fuel level
          (refine ctx level lab ptn active numcells).lab
          (refine ctx level lab ptn active numcells).ptn
          (specMaketargetcell ctx
            (refine ctx level lab ptn active numcells).lab
            (refine ctx level lab ptn active numcells).ptn
            level tcLevel).1
          numcells brest children 0]
        rfl
  termination_by fuel _ _ _ _ _ _ _ => (fuel, 0)

theorem checkChildrenF_eq (ctx : Ctx) (tcLevel : Nat)
    (brows : List Nat) (fuel level : Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) (brest : List Nat) :
    ∀ (certs : List CertNode) (o : Nat),
      checkChildrenF ctx tcLevel brows fuel level rsLab rsPtn tc
        numcells brest certs o =
        checkChildren ctx tcLevel brows fuel level rsLab rsPtn tc
          numcells brest certs o
  | [], _ => by
    rw [checkChildrenF, checkChildren]
  | c :: rest, o => by
    cases c with
    | autom o' γ =>
      simp only [checkChildrenF, checkChildren]
      rw [checkChildrenF_eq ctx tcLevel brows fuel level rsLab rsPtn
        tc numcells brest rest (o + 1)]
      rfl
    | leaf =>
      simp only [checkChildrenF, checkChildren]
      rw [checkChildrenF_eq ctx tcLevel brows fuel level rsLab rsPtn
        tc numcells brest rest (o + 1),
        checkNodeF_eq ctx tcLevel brows fuel (level + 1)]
      rfl
    | codePrune =>
      simp only [checkChildrenF, checkChildren]
      rw [checkChildrenF_eq ctx tcLevel brows fuel level rsLab rsPtn
        tc numcells brest rest (o + 1),
        checkNodeF_eq ctx tcLevel brows fuel (level + 1)]
      rfl
    | node children =>
      simp only [checkChildrenF, checkChildren]
      rw [checkChildrenF_eq ctx tcLevel brows fuel level rsLab rsPtn
        tc numcells brest rest (o + 1),
        checkNodeF_eq ctx tcLevel brows fuel (level + 1)]
      rfl
  termination_by certs _ => (fuel, certs.length + 1)

end

/-- `checkKey` on the fast replay. -/
@[expose] def checkKeyF (G : Colored n k) (cert : CertNode) (B : Key) :
    Bool :=
  if n == 0 then
    B.codes == [] && B.rows == []
  else
    checkNodeF { n := n, g := rowsOf G } 100 B.rows n 1
      (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2)
      (initActive (initialPartition G).2)
      (initialPartition G).2.length cert B.codes = some true

theorem checkKeyF_eq (G : Colored n k) (cert : CertNode) (B : Key) :
    checkKeyF G cert B = checkKey G cert B := by
  rw [checkKeyF, checkKey, checkNodeF_eq]

end Hex.GraphIso.Nauty
