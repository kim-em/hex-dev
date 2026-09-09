/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstComplete
public import HexGraphIso.Nauty.Policy.MaxRoot
import all HexGraphIso.Nauty.Policy.FirstComplete
import all HexGraphIso.Nauty.Policy.MaxRoot
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

/-- The actual nonempty root initializes the complete first-path
contract. Only strictly smaller maximum and trace calls remain premises.
This entry point supports reasoning about first-path matches without importing
generator completeness; the umbrella builds it alongside the complete key
and generation interfaces. -/
theorem root_first {n k : Nat} (G : Colored n k) (hn0 : 0 < n)
    (hn : ∀ f, f < n + 2 → (contract G 100).nodeValid f
      (Generic.nodeCall { g := rowsOf G } (n + 2) 100 f)) :
    let ctx : Ctx n := { g := rowsOf G }
    let f := root G
    let out := Nauty.node true ctx (n + 2) 100 (n + 2) f.level f.numcells f.entry
    out.1 = .unwind 0 false ∧
      ∃ targets key, Generation.RefPath ctx 100 out.2.allsamelevel 1
        (f.entry.refined ctx 1 f.numcells) targets key ∧
        Generation.Matches ctx 1 out.2 targets key := by
  obtain ⟨last, leaf, hp⟩ := initial_path G hn0
  exact firstPath_complete hp hn (root_input G hn0)

end Hex.GraphIso.Nauty.Max
