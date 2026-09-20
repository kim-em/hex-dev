/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib
public meta import HexRealFormulaMathlib.Reify

public section

namespace Hex.RealFormula.ProofProbe

open Lean Elab Command Term Meta Qq

private meta def emitProof (name : Name) (source : Expr) (params : Array Expr := #[]) : TermElabM Unit := do
  let r ← Reify.reify! source params
  addDecl (.thmDecl { name, levelParams := [], type := ← inferType r.proof, value := r.proof })

syntax "real_formula_probe " ident " : " term : command
elab_rules : command
  | `(real_formula_probe $id:ident : $source:term) => do
      let name := (← getCurrNamespace) ++ id.getId
      liftTermElabM do
        let source ← elabType source
        synthesizeSyntheticMVarsNoPostponing
        emitProof name (← instantiateMVars source)

syntax "real_parameter_probe " ident : command
elab_rules : command
  | `(real_parameter_probe $id:ident) => do
      let name := (← getCurrNamespace) ++ id.getId
      liftTermElabM do
        withLocalDeclD `a q(ℝ) fun a => do
          let a : Q(ℝ) := a
          emitProof name q(∃ x : ℝ, x ^ 2 / 2 + $a * x ≤ 3 / 2) #[a]

end Hex.RealFormula.ProofProbe
