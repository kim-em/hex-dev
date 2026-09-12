/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathCodes
public import HexGraphIso.Nauty.Sparse.Depth

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every code recorded by a native descent is a real refinement code,
strictly below the sentinel later written by leaf installation. -/
theorem CodePath.codes_lt {G : Hex.SparseGraph n} {base last : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} {codes : List Nat}
    (h : CodePath G base root path last leaf codes) (hr : root.longcode < codeSentinel) :
    ∀ c ∈ codes, c < codeSentinel := by
  induction h with
  | refl =>
    intro c hc
    exact (List.mem_singleton.mp hc) ▸ hr
  | step tc len o scratch hc hb hn ho hs tail ih =>
    intro c hm
    rcases List.mem_cons.mp hm with he | hm
    · exact he ▸ hr
    · apply ih ?_ c hm
      exact refineWith_code_lt _ _ _ _ _ _ _

end Hex.GraphIso.Nauty.Sparse
