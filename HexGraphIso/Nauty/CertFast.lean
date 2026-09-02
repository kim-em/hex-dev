/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert
public import HexBasic.OfFn

public section

/-!
A replay-cost clone of the certificate checker for kernel use. The
trusted `checkNode`/`checkChildren` pair is mutually recursive over
two argument shapes, which compiles by well-founded recursion; the
kernel of an importing module cannot unfold it, so `decide`-style
certificate obligations get stuck. `checkNodeF` is a single
structurally recursive function (fuel-first, the child sweep an inline
fold, the per-node `refine`/`breakout` results bound once with `let`
for shared reduction), proven equal to the trusted checker, so
`checkKeyF` obligations replay exactly the trusted semantics and
reduce in any module's kernel. Nothing here extends the trusted base:
soundness flows through `checkKeyF_eq` into `checkKey_sound`.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- `checkNode` as one structural recursion: the children are replayed
by an inline fold accumulating the achieved flag, with `none`
absorbing. -/
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
              (children.zipIdx 0).foldl
                (fun acc (co : CertNode × Nat) =>
                  match acc with
                  | none => none
                  | some a =>
                    let br := breakout rs.lab rs.ptn (level + 1) tcr.1
                      rs.lab[tcr.1 + co.2]!
                    match
                      match co.1 with
                      | .autom o' γ =>
                        if o' < co.2 &&
                            checkAutom ctx.g γ ctx.n &&
                            checkCellsPerm br.2.1
                              (breakout rs.lab rs.ptn (level + 1)
                                tcr.1 rs.lab[tcr.1 + o']!).1
                              (Hex.Array.map' (fun w => γ[w]!) br.1)
                              (level + 1) ctx.n then
                          some false
                        else
                          none
                      | _ =>
                        checkNodeF ctx tcLevel brows fuel (level + 1)
                          br.1 br.2.1 br.2.2 (numcells + 1) co.1 brest
                    with
                    | none => none
                    | some a' => some (a || a'))
                (some false)
            else
              none
  termination_by structural fuel => fuel

/-- The fold over one child list agrees with `checkChildren`, given
that the recursive replays agree at the child fuel. -/
theorem checkNodeF_fold_eq (ctx : Ctx) (tcLevel : Nat)
    (brows : List Nat) (fuel level : Nat) (rsLab rsPtn : Array Nat)
    (tc numcells : Nat) (brest : List Nat)
    (ih : ∀ (level' : Nat) (lab ptn : Array Nat)
      (active numcells' : Nat) (cert : CertNode) (bcodes : List Nat),
      checkNodeF ctx tcLevel brows fuel level' lab ptn active
        numcells' cert bcodes =
        checkNode ctx tcLevel brows fuel level' lab ptn active
          numcells' cert bcodes) :
    ∀ (certs : List CertNode) (o : Nat) (a : Bool),
      ((certs.zipIdx o).foldl
        (fun acc (co : CertNode × Nat) =>
          match acc with
          | none => none
          | some a =>
            let br := breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + co.2]!
            match
              match co.1 with
              | .autom o' γ =>
                if o' < co.2 &&
                    checkAutom ctx.g γ ctx.n &&
                    checkCellsPerm br.2.1
                      (breakout rsLab rsPtn (level + 1) tc
                        rsLab[tc + o']!).1
                      (Hex.Array.map' (fun w => γ[w]!) br.1)
                      (level + 1) ctx.n then
                  some false
                else
                  none
              | _ =>
                checkNodeF ctx tcLevel brows fuel (level + 1)
                  br.1 br.2.1 br.2.2 (numcells + 1) co.1 brest
            with
            | none => none
            | some a' => some (a || a'))
        (some a)) =
      (match checkChildren ctx tcLevel brows fuel level rsLab rsPtn tc
          numcells brest certs o with
      | none => none
      | some a' => some (a || a'))
  | [], o, a => by
    rw [checkChildren]
    simp [List.zipIdx_nil]
  | c :: rest, o, a => by
    have hnone : ∀ (tail : List (CertNode × Nat)),
        tail.foldl
          (fun acc (co : CertNode × Nat) =>
            match acc with
            | none => none
            | some a =>
              let br := breakout rsLab rsPtn (level + 1) tc
                rsLab[tc + co.2]!
              match
                match co.1 with
                | .autom o' γ =>
                  if o' < co.2 &&
                      checkAutom ctx.g γ ctx.n &&
                      checkCellsPerm br.2.1
                        (breakout rsLab rsPtn (level + 1) tc
                          rsLab[tc + o']!).1
                        (Hex.Array.map' (fun w => γ[w]!) br.1)
                        (level + 1) ctx.n then
                    some false
                  else
                    none
                | _ =>
                  checkNodeF ctx tcLevel brows fuel (level + 1)
                    br.1 br.2.1 br.2.2 (numcells + 1) co.1 brest
              with
              | none => none
              | some a' => some (a || a'))
          none = none := by
      intro tail
      induction tail with
      | nil => rfl
      | cons hd tl tail_ih =>
        rw [List.foldl_cons]
        exact tail_ih
    cases c with
    | autom o' γ =>
      rw [checkChildren, List.zipIdx_cons, List.foldl_cons]
      simp only []
      rw [Hex.Array.map'_eq_map]
      cases hc : (o' < o &&
          checkAutom ctx.g γ ctx.n &&
          checkCellsPerm
            (breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).2.1
            (breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o']!).1
            ((breakout rsLab rsPtn (level + 1) tc
              rsLab[tc + o]!).1.map fun w => γ[w]!)
            (level + 1) ctx.n : Bool) with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact hnone (rest.zipIdx (o + 1))
      | true =>
        simp only [ite_true]
        rw [checkNodeF_fold_eq ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest ih rest (o + 1) (a || false)]
        generalize checkChildren ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest rest (o + 1) = res
        cases res with
        | none => rfl
        | some a3 => simp
    | leaf =>
      rw [checkChildren, List.zipIdx_cons, List.foldl_cons] <;>
        try (intro o2 g2 h2; exact CertNode.noConfusion h2)
      simp only []
      rw [ih]
      generalize checkNode ctx tcLevel brows fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) CertNode.leaf brest = cres
      cases cres with
      | none => exact hnone (rest.zipIdx (o + 1))
      | some a2 =>
        rw [checkNodeF_fold_eq ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest ih rest (o + 1) (a || a2)]
        generalize checkChildren ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest rest (o + 1) = res
        cases res with
        | none => rfl
        | some a3 => simp [Bool.or_assoc]
    | codePrune =>
      rw [checkChildren, List.zipIdx_cons, List.foldl_cons] <;>
        try (intro o2 g2 h2; exact CertNode.noConfusion h2)
      simp only []
      rw [ih]
      generalize checkNode ctx tcLevel brows fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) CertNode.codePrune brest = cres
      cases cres with
      | none => exact hnone (rest.zipIdx (o + 1))
      | some a2 =>
        rw [checkNodeF_fold_eq ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest ih rest (o + 1) (a || a2)]
        generalize checkChildren ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest rest (o + 1) = res
        cases res with
        | none => rfl
        | some a3 => simp [Bool.or_assoc]
    | node children =>
      rw [checkChildren, List.zipIdx_cons, List.foldl_cons] <;>
        try (intro o2 g2 h2; exact CertNode.noConfusion h2)
      simp only []
      rw [ih]
      generalize checkNode ctx tcLevel brows fuel (level + 1)
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.1
        (breakout rsLab rsPtn (level + 1) tc rsLab[tc + o]!).2.2
        (numcells + 1) (CertNode.node children) brest = cres
      cases cres with
      | none => exact hnone (rest.zipIdx (o + 1))
      | some a2 =>
        rw [checkNodeF_fold_eq ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest ih rest (o + 1) (a || a2)]
        generalize checkChildren ctx tcLevel brows fuel level rsLab
          rsPtn tc numcells brest rest (o + 1) = res
        cases res with
        | none => rfl
        | some a3 => simp [Bool.or_assoc]

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
        rcases compare (refine ctx level lab ptn active
          numcells).longcode bc with _ | _ | _ <;> simp only []
        rcases Decidable.em (discreteAt (refine ctx level lab ptn
            active numcells).ptn level ctx.n = true) with hd | hd
        · simp only [hd, ite_true]
        · rw [Bool.eq_false_of_ne_true hd]
          simp only [Bool.false_eq_true, ite_false]
          rcases Decidable.em (children.length =
              (specMaketargetcell ctx (refine ctx level lab ptn
                active numcells).lab (refine ctx level lab ptn active
                numcells).ptn level tcLevel).2.2) with hl | hl
          · simp only [hl, ite_true]
            rw [checkNodeF_fold_eq ctx tcLevel brows fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn
              (specMaketargetcell ctx
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                level tcLevel).1
              numcells brest
              (checkNodeF_eq ctx tcLevel brows fuel) children 0 false]
            rcases checkChildren ctx tcLevel brows fuel level
              (refine ctx level lab ptn active numcells).lab
              (refine ctx level lab ptn active numcells).ptn
              (specMaketargetcell ctx
                (refine ctx level lab ptn active numcells).lab
                (refine ctx level lab ptn active numcells).ptn
                level tcLevel).1
              numcells brest children 0 with _ | a
            · rfl
            · simp only [Bool.false_or]
          · simp only [hl, ite_false]

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
