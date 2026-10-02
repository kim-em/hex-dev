/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Path

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native descent carrying each executed refinement code, including
the terminal node's code. The sentinel is recorded separately by leaf
installation. Scratch arguments are the actual arguments at each step. -/
inductive CodePath (G : Hex.SparseGraph n) :
    Nat → RefineSt n → List (Nat × Nat) → Nat → RefineSt n → List Nat → Type where
  | refl (level : Nat) (st : RefineSt n) : CodePath G level st [] level st [st.longcode]
  | step {level last : Nat} {st leaf : RefineSt n} {path : List (Nat × Nat)} {codes : List Nat}
      (tc len o : Nat) (scratch : Scratch)
      (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
      (hs : Scratch.Bounded n scratch)
      (tail : CodePath G (level + 1)
        (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) path last leaf codes) :
      CodePath G level st ((tc, o) :: path) last leaf (st.longcode :: codes)

namespace CodePath

variable {G : Hex.SparseGraph n} {base last : Nat} {root leaf : RefineSt n}
  {path : List (Nat × Nat)} {codes : List Nat}

/-- Every step follows the native unhinted target rule at its actual
refined state. The first-path construction establishes this predicate. -/
@[expose] def Selects (tcLevel : Nat) :
    {base last : Nat} → {root leaf : RefineSt n} → {path : List (Nat × Nat)} → {codes : List Nat} →
      CodePath G base root path last leaf codes → Prop
  | _, _, _, _, _, _, .refl _ _ => True
  | _, _, _, _, _, _, @CodePath.step _ _ level _ st _ _ _ tc _ _ _ _ _ _ _ _ tail =>
    tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1) ∧ tail.Selects tcLevel

/-- Forgetting codes retains the exact same native descent. -/
theorem descent (h : CodePath G base root path last leaf codes) :
    DescPath G base root path last leaf := by
  induction h with
  | refl => exact .refl _ _
  | step tc len o scratch hc hb hn ho hs tail ih => exact .step tc len o scratch hc hb hn ho hs ih

theorem length (h : CodePath G base root path last leaf codes) : codes.length = path.length + 1 := by
  induction h with
  | refl => rfl
  | step tc len o scratch hc hb hn ho hs tail ih => simp only [List.length_cons, ih]

theorem head (h : CodePath G base root path last leaf codes) : codes[0]! = root.longcode := by
  cases h <;> rfl

end CodePath
end Hex.GraphIso.Nauty.Sparse
