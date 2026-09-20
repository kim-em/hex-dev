/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import PrimeCert
public section

namespace LanguagePrototype

-- A proof-producing extension outside PrimeCert's original modules.
theorem trial17 : Nat.Prime 17 := by decide +kernel

open Lean PrimeCert.Meta in
meta def trialMethod : PrimeCertMethod `Lean.Parser.Term.num := fun _ _ =>
  pure ⟨17, mkNatLit 17, mkConst ``trial17⟩

@[prime_cert trial17] meta def trialExtension : PrimeCert.Meta.PrimeCertExt where
  syntaxName := `Lean.Parser.Term.num
  methodName := ``trialMethod

end LanguagePrototype
