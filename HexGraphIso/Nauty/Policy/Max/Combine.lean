/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Root
public import HexGraphIso.Nauty.Policy.Max.FirstLeaf
public import HexGraphIso.Nauty.Policy.Max.Finish
public import HexGraphIso.Nauty.Policy.Max.Bad
public import HexGraphIso.Nauty.Policy.Max.Coset
public import HexGraphIso.Nauty.Policy.Max.NodeTrace
public import HexGraphIso.Nauty.Policy.Max.SweepTrace
import all HexGraphIso.Nauty.Policy.Max.Rules
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Every actual maximum and accumulated-trace rule composes in one
recursive policy, including first-leaf installation and sweep completion. -/
theorem rules (G : Colored n k) (tcLevel : Nat) : Rules G tcLevel where
  first_leaf := first_leaf G tcLevel
  first_branch := first_branch G tcLevel
  other_branch := other_branch G tcLevel
  auto_first := auto_first G tcLevel
  auto_canon := auto_canon G tcLevel
  better := better_rule G tcLevel
  bad := bad_rule G tcLevel
  visit := visit G tcLevel
  skip := skip G tcLevel
  finish := finish G tcLevel
  node_trace := node_trace G tcLevel
  sweep_trace := sweep_trace G tcLevel

end Hex.GraphIso.Nauty.Max
