/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.DecisionCheck
public import HexRCF.Soundness

public section

/-!
# Soundness of compiled RCF decisions

The Mathlib-free certificate construction and decision pipeline live in
`HexRCF.DecisionCheck`. This module connects an accepted compiled verdict to
the real-valued reflected sentence semantics.
-/

namespace Hex.RCF

/-- Every true compiled verdict proves the reflected sentence. -/
theorem decide_sound (s : Sentence) (h : decide s = some true) : s.toProp := by
  obtain ⟨cert, hcert⟩ := decide_eq_some_true_imp_exists_cert h
  exact check_sound s cert hcert

end Hex.RCF
