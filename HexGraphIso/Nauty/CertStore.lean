/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CertReplay
import all HexGraphIso.Nauty.CertAutom
import all HexGraphIso.Nauty.CertReplay

public section

/-!
Certificate-store validity for the trace-driven producer.  The producer
checks each witness immediately before emitting an automorphism prune, so
validity is a structural invariant of the emitted certificate and does not
depend on the search-side generator store.
-/

namespace Hex.GraphIso.Nauty

theorem certifyNodeAutom_automsOk (ctx : Ctx n) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (bcodes : List Nat) (st : AutState),
      AutomsOk (fun γ => checkAutom ctx.g γ = true)
        (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
          bcodes st).1
  | 0, _, _, _, _, _, _, _ => trivial
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st => by
    rcases bcodes with _ | ⟨bc, brest⟩
    · rw [certifyNodeAutom.eq_def]
      dsimp only
      split <;> trivial
    · rw [certifyNodeAutom.eq_def]
      dsimp only
      split
      · trivial
      · split
        · trivial
        · trivial
        · split
          · trivial
          · let P := fun γ => checkAutom ctx.g γ = true
            let rs := refine ctx level lab ptn active numcells
            let tcr := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
            let masks := cellMasks n rs.lab rs.ptn level
            let step :
                (List CertNode × AutState ×
                    Option (Nat × Array (Array Nat × Array Nat))) →
                  Nat →
                  List CertNode × AutState ×
                    Option (Nat × Array (Array Nat × Array Nat)) :=
              fun acc o =>
                let (kids, st, cache) := acc
                let cache' := usableGens masks st cache
                let descend : Unit → List CertNode × AutState ×
                    Option (Nat × Array (Array Nat × Array Nat)) :=
                  fun _ =>
                    let br := breakout n rs.lab rs.ptn (level + 1) tcr.1
                      rs.lab[tcr.1 + o]!
                    let (child, st') := certifyNodeAutom ctx tcLevel fuel
                      (level + 1) br.1 br.2.1 br.2.2
                      (rs.numcells + 1) brest st
                    (child :: kids, st', some cache')
                match witness? n rs.lab tcr.1 cache'.2 o with
                | some (o', γ) =>
                  if childCellsOk ctx rs.lab rs.ptn level tcr.1 o o'
                      γ then
                    (.autom o' γ :: kids, st, some cache')
                  else
                    descend ()
                | none => descend ()
            have hstep : ∀ acc o,
                (∀ c ∈ acc.1, AutomsOk P c) →
                ∀ c ∈ (step acc o).1, AutomsOk P c := by
              intro acc o hacc c hc
              rcases acc with ⟨kids, stx, cache⟩
              let cache' := usableGens masks stx cache
              let br := breakout n rs.lab rs.ptn (level + 1) tcr.1
                rs.lab[tcr.1 + o]!
              rcases hout : certifyNodeAutom ctx tcLevel fuel
                  (level + 1) br.1 br.2.1 br.2.2
                  (rs.numcells + 1) brest stx with ⟨child, st'⟩
              have hchild : AutomsOk P child := by
                have hr := certifyNodeAutom_automsOk ctx tcLevel fuel
                  (level + 1) br.1 br.2.1 br.2.2
                  (rs.numcells + 1) brest stx
                rw [hout] at hr
                exact hr
              rcases hw : witness? n rs.lab tcr.1 cache'.2 o with
                _ | ⟨o', γ⟩
              · simp only [step, cache', hw, br, hout] at hc
                rcases List.mem_cons.mp hc with rfl | hc
                · exact hchild
                · exact hacc c hc
              · rcases Decidable.em
                    (childCellsOk ctx rs.lab rs.ptn level tcr.1 o o'
                      γ = true) with hcc | hcc
                · simp only [step, cache', hw, hcc, ite_true] at hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · rw [AutomsOk, childCellsOk] at *
                    simp only [Bool.and_eq_true] at hcc
                    exact hcc.1.1
                  · exact hacc c hc
                · simp only [step, cache', hw, hcc, Bool.false_eq_true,
                    ite_false, br, hout] at hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact hchild
                  · exact hacc c hc
            have hfold : ∀ (os : List Nat) acc,
                (∀ c ∈ acc.1, AutomsOk P c) →
                ∀ c ∈ (os.foldl step acc).1, AutomsOk P c := by
              intro os
              induction os with
              | nil => intro acc hacc; exact hacc
              | cons o os ih =>
                intro acc hacc
                rw [List.foldl_cons]
                exact ih _ (hstep acc o hacc)
            change AutomsOk P
              (.node (((List.range tcr.2.2).foldl step
                ([], st.charge, none)).1.reverse))
            rw [AutomsOk]
            apply automsOkList_of_forall
            intro c hc
            rw [List.mem_reverse] at hc
            exact hfold (List.range tcr.2.2) ([], st.charge, none)
              (fun c hc => nomatch hc) c hc

/-- Every automorphism record in a produced candidate has passed the
trusted automorphism checker. -/
theorem produceCand_automsOk {n k : Nat} (G : Colored n k)
    {budget : Option Nat} {cert : CertNode} {B : Key n}
    (h : produceCand G budget = some (cert, B)) :
    AutomsOk (fun γ => checkAutom (rowsOf G) γ = true) cert := by
  rw [produceCand] at h
  dsimp only at h
  split at h
  · cases h
  · let ctx : Ctx n := { g := rowsOf G }
    let st1 := (runColoredTraced G).autos.foldl
      (fun st γ => st.admit ctx γ) (AutState.init n budget)
    let st2 := { st1 with
      refLeaf := some (runColoredTraced G).result.canonlab }
    rcases hw : certifyNodeAutom ctx 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length
        ((runColoredTraced G).bestCodes ++ [codeSentinel]) st2 with
      ⟨cert', st3⟩
    simp only [ctx, st1, st2, hw] at h
    split at h
    · cases h
    · have hcert : cert' = cert :=
        congrArg Prod.fst (Option.some.inj h)
      subst cert
      have hok := certifyNodeAutom_automsOk ctx 100 n 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive n (initialPartition G).2)
        (initialPartition G).2.length
        ((runColoredTraced G).bestCodes ++ [codeSentinel]) st2
      rw [hw] at hok
      exact hok

/-- Once the traced key equals the specification key, no further store
hypothesis is needed for totality: every emitted automorphism has already
passed the trusted checker. -/
theorem certifyCanon?_isSome_of_keyEq {n k : Nat} (G : Colored n k)
    (hdom : canonSpecKey G = tracedKey G) :
    (certifyCanon? G).isSome :=
  certifyCanon?_isSome_of_dominated G hdom fun _ _ hp =>
    produceCand_automsOk G hp

end Hex.GraphIso.Nauty
