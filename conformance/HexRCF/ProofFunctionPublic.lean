/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.DependentQuote
public section
namespace Hex.RCF.ProofFunctionPublic

theorem first : Hex.RCF.DependentQuote.proofFunction = some 7 :=
  Hex.RCF.DependentQuote.proofFunction_checked

theorem continued : Hex.RCF.DependentQuote.continuedFunction = some 29 :=
  Hex.RCF.DependentQuote.continuedFunction_checked

end Hex.RCF.ProofFunctionPublic
