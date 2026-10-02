/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Graph
public import HexGraphIso.Nauty.Cert.CanonForm

public section

namespace Hex.GraphIso.Nauty.Sparse

private theorem scatter_loop (lab : Array Nat) :
    ∀ (positions : List Nat) (inv : Array Nat),
      (forIn positions inv (fun i a =>
        pure (ForInStep.yield (a.set! lab[i]! i))) : Id (Array Nat)) =
        invPerm.go lab positions inv
  | [], _ => rfl
  | i :: positions, inv => by
    simp only [List.forIn_cons, invPerm.go, pure_bind]
    exact scatter_loop lab positions (inv.set! lab[i]! i)

/-- The sparse array loop computes the shared inverse permutation. -/
theorem inverse_eq {lab : Array Nat} (hsize : lab.size = n) :
    inverse n lab = invPerm lab := by
  unfold inverse invPerm
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step = List.range n := by
    simp [List.range_eq_range']
  rw [hrange, scatter_loop, hsize]
  rfl

@[simp] theorem inverse_size {lab : Array Nat} (hsize : lab.size = n) :
    (inverse n lab).size = n := by
  rw [inverse_eq hsize, invPerm_size, hsize]

/-- Inverse scatter recovers a position from its vertex. -/
theorem inverse_get {lab : Array Nat} (hsize : lab.size = n)
    (hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b)
    {i : Nat} (hi : i < n) (hv : lab[i]! < n) :
    (inverse n lab)[lab[i]!]! = i := by
  rw [inverse_eq hsize]
  exact getElem!_invPerm lab (by simpa [hsize] using hinj)
    (by omega) (by omega)

/-- Every entry of a nonempty inverse array is an in-range position. -/
theorem inverse_lt {lab : Array Nat} (hsize : lab.size = n)
    (hn : 0 < n) (v : Nat) : (inverse n lab)[v]! < n := by
  rw [inverse_eq hsize, ← hsize]
  exact getElem!_invPerm_lt (by omega) v

/-- A checked label supplies the permutation hypotheses of inverse scatter. -/
theorem inverse_label {lab : Array Nat} {l : Label n}
    (h : Label.ofArray? n lab = some l) (i : Fin n) :
    (inverse n lab)[(l.get i).val]! = i.val := by
  have hs := (Label.ofArray?_bounds h).1
  have hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b := by
    intro a b ha hb hab
    have he : l.get ⟨a, ha⟩ = l.get ⟨b, hb⟩ := Fin.ext (by
      simpa only [Label.ofArray?_get h] using hab)
    exact congrArg Fin.val (l.perm.get_inj he)
  rw [Label.ofArray?_get h]
  exact inverse_get hs hinj i.isLt (by
    rw [← Label.ofArray?_get h i.val i.isLt]
    exact (l.get i).isLt)

/-- On a checked label, inverse scatter is its old-to-new transporter. -/
theorem inverse_toPerm {lab : Array Nat} {l : Label n}
    (h : Label.ofArray? n lab = some l) (v : Fin n) :
    (inverse n lab)[v.val]! = (l.toPerm.get v).val := by
  simpa only [Label.get_toPerm_get] using inverse_label h (l.toPerm.get v)

end Hex.GraphIso.Nauty.Sparse
