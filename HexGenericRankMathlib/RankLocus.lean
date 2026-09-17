/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Provider
public import HexDeterminantalIdealMathlib.Tactic
public meta import HexGenericRankMathlib.Provider
public meta import HexDeterminantalIdealMathlib.Provider
public meta import Lean

public meta section

namespace HexGenericRankMathlib

open Lean Meta Elab Tactic

/-- Compute the generic threshold from the same sealed polynomial entry lists.
The locus theorem holds for every threshold, so no separate generic-rank
certificate is replayed in the kernel. -/
@[tactic HexDeterminantalIdealMathlib.rankLocusDefault]
def evalRankLocusDefault : Tactic := fun stx => withMainContext do
  let cfg := (← HexDeterminantalIdealMathlib.elabLocusConfig stx[1]).provider
  let A ← Term.elabTerm stx[2] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let A ← instantiateMVars A
  let p ← HexDeterminantalIdealMathlib.Provider.reify A cfg
  let k := p.batch.sealed.n
  let r ← match p.data with
    | .integer L => pure (Provider.integerWitness k p.lit.n p.lit.m L).rank
    | .residue q L =>
      let entries := L.map (List.map (List.map (fun t => (t.1, (t.2 : Int)))))
      let some (_, c) := Provider.residueWitness? q k p.lit.n p.lit.m entries
        | throwError "rank_locus: declined: invalid residue coefficient evidence"
      pure c.rank
  let result ← HexDeterminantalIdealMathlib.Provider.locus p r cfg
  let (_, goal) ← (← getMainGoal).note `h result.iffProof (some (← result.proposition))
  replaceMainGoal [goal]

end HexGenericRankMathlib
