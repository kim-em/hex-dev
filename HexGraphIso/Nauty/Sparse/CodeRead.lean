/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Key
public import HexGraph.Sparse.Relabel
public import HexGraphIso.Nauty.Sparse.Search
public import HexGraphIso.Nauty.Policy.CodeState
public import HexGraphIso.LabelArray
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Read an installed native incumbent from its stable code array and
checked label. This semantic observation does not expand sparse rows. -/
@[expose] def State.best (G : Hex.SparseGraph n) (st : State n) : Option (Key n) :=
  if st.canonlevel = 0 then none else
    (Label.ofArray? n st.canonlab).map fun l =>
      ⟨(List.range' 1 st.canonlevel).map (fun i => st.canoncode[i]!) ++ [codeSentinel],
        G.relabel l.perm⟩

/-- During code overwriting, the semantic incumbent retains its complete
saved code sequence. Its graph is still the actual saved native label. -/
@[expose] def State.key (G : Hex.SparseGraph n) (bs : List Nat) (st : State n) : Option (Key n) :=
  if bs = [] then none else
    (Label.ofArray? n st.canonlab).map fun l => ⟨bs ++ [codeSentinel], G.relabel l.perm⟩

/-- A stable canonical code array reads exactly the semantic sparse key. -/
theorem best_eq_key {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n} {comparison : Int}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon comparison)
    (hne : comparison ≠ 1) : State.best G st = State.key G bs st := by
  rw [State.best, State.key, code_read h hne, h.blen]
  cases bs <;> simp

/-- Either settled leaf verdict exposes the same native incumbent. -/
theorem settled_read {G : Hex.SparseGraph n} {cs bs : List Nat} {st : State n}
    (h : Settled cs bs st) : State.best G st = State.key G bs st := by
  cases h with
  | codes hm hn => exact best_eq_key hm (by omega)
  | rows hm _ => exact best_eq_key hm (by decide)

/-- Installing the first leaf exposes precisely its executed code chain
and sparse relabelling, once the code machine has been initialized. -/
theorem firstterminal_best {G : Hex.SparseGraph n} {cs : List Nat} {st : State n} {l : Label n}
    (h : Codes cs cs (firstterminal cs.length st)) (hne : cs ≠ [])
    (hl : Label.ofArray? n st.lab = some l) :
    State.best G (firstterminal cs.length st) = some ⟨cs ++ [codeSentinel], G.relabel l.perm⟩ := by
  rw [best_eq_key h (by change (0 : Int) ≠ 1; decide)]
  simp only [State.key, hne, ite_false]
  have he : (firstterminal cs.length st).canonlab = st.lab := by unfold firstterminal; rfl
  rw [he, hl]
  rfl

end Hex.GraphIso.Nauty.Sparse
