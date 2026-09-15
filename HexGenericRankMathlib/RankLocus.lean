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

/-- Supply the generic threshold using the locus request's sealed batch.
Natural residues are passed as nonnegative integer representatives so both
providers quote definitionally identical polynomial matrices. -/
@[tactic HexDeterminantalIdealMathlib.rankLocusDefault]
def evalRankLocusDefault : Tactic := fun stx => withMainContext do
  let cfg := (← HexDeterminantalIdealMathlib.elabLocusConfig stx[1]).provider
  let A ← Term.elabTerm stx[2] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let A ← instantiateMVars A
  let p ← HexDeterminantalIdealMathlib.Provider.reify A cfg
  let (modulus, entries) := match p.data with
    | .integer L => (none, L.flatten.toArray)
    | .residue q L => (some q, L.flatten.toArray.map (List.map (fun t => (t.1, (t.2 : Int)))))
  let generic ← Provider.withEvidence (HexDeterminantalIdealMathlib.Provider.evidence p.batch) do
    match modulus with
    | none => Provider.batchResult A p.lit p.batch none (some entries)
    | some q =>
      let charInst ← mkAppOptM ``Modular.residueChar #[mkNatLit q, none]
      let domainInst ← mkAppOptM ``Modular.residueDomain #[mkNatLit q, none, none]
      Provider.withEvidence [charInst, domainInst] do
        Provider.batchResult A p.lit p.batch (some q) (some entries)
  unless ← isDefEq p.polynomial generic.polynomial do
    throwError "rank_locus: the generic threshold did not preserve the reified polynomial matrix"
  let _ ← HexDeterminantalIdealMathlib.Provider.checkProofBudget p #[generic.genericProof] cfg
  let result ← HexDeterminantalIdealMathlib.Provider.locus p generic.rank cfg
  let (_, goal) ← (← getMainGoal).note `h result.iffProof (some (← result.proposition))
  replaceMainGoal [goal]

end HexGenericRankMathlib
