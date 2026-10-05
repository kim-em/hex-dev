/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.Automorphism
public import HexGraphIsoMathlib.TacticSupport
public import HexGraphIso.Kernel.CheckKey
public import HexPermGroupMathlib.Kernel

public section

/-!
# Kernel certificates for explicit graph automorphism groups

An automorphism certificate follows a point-stabilizer chain.  At one level
it records a base point and a list containing every possible image of that
point.  For every same-colour vertex outside the list it records canonical-key
certificates for the two graphs obtained by individualizing the base point and
that vertex.  Different checked keys prove that no automorphism has the
excluded image.  The next level is checked on the individualized graph.

The Boolean checker only replays packed graph-refinement certificates.  Its
soundness theorem bounds the order of the full automorphism group by the
product of the recorded orbit bounds; it does not trust the producer's search
or its claimed orbits.
-/

namespace Hex.GraphIso.Aut.Kernel

open Hex.GraphIso.Nauty

variable {n k : Nat}

/-- One checked canonical key. -/
structure KeyCert where
  cert : CertNode
  key : GraphIso.Kernel.Key

instance : Inhabited KeyCert := ⟨⟨CertNode.leaf, ⟨[], []⟩⟩⟩

/-- Evidence excluding one vertex as the image of a level's base point. -/
structure Separation where
  vertex : Nat
  witness : KeyCert

instance : Inhabited Separation := ⟨⟨0, default⟩⟩

/-- One point-stabilizer level. -/
structure Level where
  base : Nat
  orbit : List Nat
  reference : KeyCert
  excluded : List Separation

instance : Inhabited Level := ⟨⟨0, [], default, []⟩⟩

/-- A point-stabilizer certificate. -/
inductive Certificate where
  | done
  | step (level : Level) (rest : Certificate)

instance : Inhabited Certificate := ⟨.done⟩

/-- The product of the recorded orbit bounds. -/
@[expose] def Certificate.bound : Certificate → Nat
  | .done => 1
  | .step L rest => L.orbit.length * rest.bound

/-- Find the exclusion evidence for a vertex. -/
@[expose] def Level.find? (L : Level) (w : Nat) : Option KeyCert :=
  (L.excluded.find? fun e => e.vertex == w).map (fun e => e.witness)

/-- Check the evidence for one possible image of the base point. -/
@[expose] def Level.checkImage (G : Colored n k) (rows : Nat)
    (v : Fin n) (_Hv : Colored n (k + 1)) (L : Level) (w : Nat) : Bool :=
  if hw : w < n then
    let u : Fin n := ⟨w, hw⟩
    if L.orbit.contains w then true
    else if G.coloring.cells[u] != G.coloring.cells[v] then true
    else
      match indiv? G u, L.find? w with
      | some Hw, some evidence =>
          GraphIso.Kernel.checkKey Hw rows evidence.cert evidence.key &&
            checkDiffL L.reference.key evidence.key
      | _, _ => false
  else false

/-- Check one level, including its reference key and every excluded image. -/
@[expose] def Level.check (G : Colored n k) (rows : Nat)
    (v : Fin n) (Hv : Colored n (k + 1)) (L : Level) : Bool :=
  decide L.orbit.Nodup &&
  L.orbit.all (fun w => decide (w < n)) &&
  L.orbit.contains v.val &&
  GraphIso.Kernel.checkKey Hv rows L.reference.cert L.reference.key &&
  (List.range n).all (L.checkImage G rows v Hv)

/-- Replay a point-stabilizer certificate.  Every successful step adds one
colour, so a terminal certificate is accepted only after the colouring has at
least as many colours as vertices. -/
@[expose] def check : {k : Nat} → Colored n k → Nat → Certificate → Bool
  | k, _G, _rows, .done => decide (n ≤ k)
  | _k, G, rows, .step L rest =>
      if hv : L.base < n then
        let v : Fin n := ⟨L.base, hv⟩
        match indiv? G v with
        | none => false
        | some H => L.check G rows v H && check H rows rest
      else false

/-- Assemble an accepted step from separately replayed level and suffix
certificates.  The tactic uses this theorem to keep each kernel reduction
small. -/
theorem check_step {G : Colored n k} {rows : Nat} (L : Level)
    {rest : Certificate} (hv : L.base < n) {H : Colored n (k + 1)}
    (hH : indiv? G ⟨L.base, hv⟩ = some H)
    (hL : L.check G rows ⟨L.base, hv⟩ H = true)
    (hrest : check H rows rest = true) :
    check G rows (.step L rest) = true := by
  rw [check]
  simp only [dite_eq_left hv]
  rw [hH]
  simpa only [Bool.and_eq_true] using And.intro hL hrest

private def keyCert? (budget : Nat) (G : Colored n k) : Option KeyCert := do
  let (cert, key) ← GraphIso.Kernel.certifyKey? budget G
  return ⟨cert, key⟩

private def excluded? (budget : Nat) (G : Colored n k)
    (w : Fin n) : Option Separation := do
  let H ← indiv? G w
  let witness ← keyCert? budget H
  return ⟨w.val, witness⟩

private def certifyAux (budget : Nat) :
    (fuel : Nat) → {k : Nat} → Colored n k → Option Certificate
  | 0, k, _G => if n ≤ k then some .done else none
  | fuel + 1, k, G =>
      if n ≤ k then some .done
      else
        match (List.finRange n).find? fun v => (indiv? G v).isSome with
        | none => none
        | some v =>
            match indiv? G v with
            | none => none
            | some H => do
                let orbit := (List.range n).filter fun w =>
                  (Aut.orbits G)[w]! == (Aut.orbits G)[v.val]!
                let reference ← keyCert? budget H
                let excludedVertices := (List.finRange n).filter fun w =>
                  !orbit.contains w.val && G.coloring.cells[w].val == G.coloring.cells[v].val
                let excluded ← excludedVertices.mapM (excluded? budget G)
                let rest ← certifyAux budget fuel H
                return .step ⟨v.val, orbit, reference, excluded⟩ rest

/-- Run the untrusted automorphism and canonical-form searches and record a
point-stabilizer certificate for kernel replay.  `budget` bounds each
canonical-form certificate search. -/
def certify? (budget : Nat) (G : Colored n k) : Option Certificate :=
  certifyAux budget n G

/-- An accepted level contains the image of its base point under every
automorphism of the current coloured graph. -/
theorem Level.image_mem {G : Colored n k} {rows : Nat} {v : Fin n}
    {Hv : Colored n (k + 1)} {L : Level}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hHv : indiv? G v = some Hv) (hcheck : L.check G rows v Hv = true)
    {p : Perm n} (hp : IsIso G G p) : (p.get v).val ∈ L.orbit := by
  classical
  simp only [Level.check, Bool.and_eq_true] at hcheck
  by_contra hmem
  have himage := List.all_eq_true.mp hcheck.2 (p.get v).val
    (List.mem_range.mpr (p.get v).isLt)
  have hcolor : G.coloring.cells[p.get v] = G.coloring.cells[v] := hp.cells_eq v
  rw [Level.checkImage, dite_eq_left (p.get v).isLt] at himage
  simp [hmem, hcolor] at himage
  cases hHw : indiv? G (p.get v) with
  | none => simp [hHw] at himage
  | some Hw =>
    cases he : L.find? (p.get v).val with
    | none => simp [hHw, he] at himage
    | some evidence =>
      simp only [hHw, he, Bool.and_eq_true] at himage
      have href := hcheck.1.2
      have hrowsHv : GraphIso.Kernel.packRows n Hv.graph.adjMatrix.data.toList = rows := by
        rw [(Aut.indiv_fields hHv).1, hrows]
      have hrowsHw : GraphIso.Kernel.packRows n Hw.graph.adjMatrix.data.toList = rows := by
        rw [(Aut.indiv_fields hHw).1, hrows]
      have hnot := GraphIso.Kernel.not_isomorphic_of_checkKeys
        hrowsHv hrowsHw href himage.1 himage.2
      exact hnot (Isomorphic.intro p (Aut.indiv_isIso_map hHv hHw hp rfl))

/-- The list at an accepted level bounds the actual orbit of its base point. -/
theorem Level.orbitSize_le {G : Colored n k} {rows : Nat} {v : Fin n}
    {Hv : Colored n (k + 1)} {L : Level}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hHv : indiv? G v = some Hv) (hcheck : L.check G rows v Hv = true) :
    Aut.orbitSize G v ≤ L.orbit.length := by
  classical
  let _ := Fintype.ofFinite (MulAction.orbit (Aut.group G) v)
  have horbit (w : MulAction.orbit (Aut.group G) v) : w.val.val ∈ L.orbit := by
    obtain ⟨p, hp, hpv⟩ := ((Aut.mem_orbit G v w.val).mp w.property).elim
    rw [← hpv]
    exact L.image_mem hrows hHv hcheck hp
  let f : MulAction.orbit (Aut.group G) v → Fin L.orbit.length := fun w =>
    ⟨L.orbit.idxOf w.val.val, List.idxOf_lt_length_of_mem (horbit w)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    exact (List.idxOf_inj (horbit a)).mp (congrArg Fin.val hab)
  rw [Aut.orbitSize_card, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Acceptance bounds the full automorphism-group order by the product of
the recorded point-orbit bounds. -/
theorem card_le_bound {G : Colored n k} {rows : Nat} {c : Certificate}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hcheck : check G rows c = true) : Nat.card (Aut.group G) ≤ c.bound := by
  induction c generalizing k with
  | done =>
    simp only [check, decide_eq_true_eq] at hcheck
    rw [Aut.card_discrete hcheck]
    rfl
  | step L rest ih =>
    rw [check] at hcheck
    split at hcheck
    · rename_i hv
      dsimp only at hcheck
      split at hcheck
      · contradiction
      · rename_i H hH
        simp only [Bool.and_eq_true] at hcheck
        have hrowsH : GraphIso.Kernel.packRows n H.graph.adjMatrix.data.toList = rows := by
          rw [(Aut.indiv_fields hH).1, hrows]
        rw [Aut.indiv_card hH]
        exact Nat.mul_le_mul (L.orbitSize_le hrows hH hcheck.1)
          (ih hrowsH hcheck.2)
    · contradiction

/-- Acceptance bounds the order reported by the executable automorphism
search. -/
theorem order_le_bound {G : Colored n k} {rows : Nat} {c : Certificate}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hcheck : check G rows c = true) : Aut.order G ≤ c.bound := by
  rw [Aut.order_card]
  exact card_le_bound hrows hcheck

end Hex.GraphIso.Aut.Kernel

namespace Hex.GraphIso.Aut

variable {n k : Nat}

/-- The full colour-preserving automorphism group as a Mathlib subgroup of
`Equiv.Perm (Fin n)`. -/
def equivGroup (G : Colored n k) : Subgroup (Equiv.Perm (Fin n)) :=
  (group G).map Perm.equiv.toMonoidHom

@[simp] theorem mem_equivGroup (G : Colored n k) (p : Equiv.Perm (Fin n)) :
    p ∈ equivGroup G ↔ IsIso G G (Perm.ofEquiv p) := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change IsIso G G (Perm.ofEquiv q.toEquiv)
    rw [Perm.ofEquiv_toEquiv]
    exact (Aut.mem_group G q).mp hq
  · intro hp
    refine ⟨Perm.ofEquiv p, hp, ?_⟩
    exact Perm.toEquiv_ofEquiv p

/-- The existing completeness theorem, transported to the Mathlib-facing
permutation representation. -/
theorem equivGroup_eq_mapClosure (G : Colored n k) :
    equivGroup G =
      (Subgroup.closure {p | p ∈ Aut.gens G}).map Perm.equiv.toMonoidHom := by
  rw [Aut.closure_eq_group]
  rfl

/-- The executable and Mathlib-facing presentations of the full
automorphism group have the same cardinality. -/
theorem card_equivGroup (G : Colored n k) :
    Nat.card (equivGroup G) = Nat.card (group G) := by
  rw [equivGroup_eq_mapClosure, Aut.closure_eq_group]
  symm
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (group G) Perm.equiv.toMonoidHom Perm.equiv.injective).toEquiv

theorem isIso_nil (G : Colored n k) :
    ∀ g ∈ ([] : List (Equiv.Perm (Fin n))), IsIso G G (Perm.ofEquiv g) := by
  simp

theorem isIso_cons {G : Colored n k} {g : Equiv.Perm (Fin n)}
    {gs : List (Equiv.Perm (Fin n))} (hg : IsIso G G (Perm.ofEquiv g))
    (hgs : ∀ p ∈ gs, IsIso G G (Perm.ofEquiv p)) :
    ∀ p ∈ g :: gs, IsIso G G (Perm.ofEquiv p) := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with hp | hp
  · rw [hp]
    exact hg
  · exact hgs p hp

/-- A certified lower bound of the same size as the graph certificate's
upper bound identifies a generator subgroup with the full automorphism
group. -/
theorem closure_eq_equivGroup {G : Colored n k}
    {gs : List (Equiv.Perm (Fin n))} {gc : Kernel.Certificate} {rows N : Nat}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hgraph : Kernel.check G rows gc = true)
    (hgens : ∀ g ∈ gs, IsIso G G (Perm.ofEquiv g))
    (hcard : Nat.card (Subgroup.closure {g | g ∈ gs}) = N)
    (hbound : gc.bound = N) :
    Subgroup.closure {g | g ∈ gs} = equivGroup G := by
  apply Subgroup.eq_of_le_of_card_ge
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    exact (mem_equivGroup G g).mpr (hgens g hg)
  · rw [card_equivGroup, hcard]
    have hf := Kernel.order_le_bound hrows hgraph
    rw [Aut.order_card, hbound] at hf
    exact hf

/-- A generator subgroup certified to meet the graph certificate's upper
bound determines the full automorphism-group order. -/
theorem card_equivGroup_eq {G : Colored n k}
    {gs : List (Equiv.Perm (Fin n))} {gc : Kernel.Certificate} {rows N : Nat}
    (hrows : GraphIso.Kernel.packRows n G.graph.adjMatrix.data.toList = rows)
    (hgraph : Kernel.check G rows gc = true)
    (hgens : ∀ g ∈ gs, IsIso G G (Perm.ofEquiv g))
    (hcard : Nat.card (Subgroup.closure {g | g ∈ gs}) = N)
    (hbound : gc.bound = N) : Nat.card (equivGroup G) = N := by
  rw [← closure_eq_equivGroup hrows hgraph hgens hcard hbound]
  exact hcard

end Hex.GraphIso.Aut

namespace Hex.GraphIso.Mathlib

universe u
variable {V : Type u} [Fintype V] {n k : Nat}

/-- A bare graph automorphism is the same thing as an automorphism of its
one-cell coloured view. -/
def graphAutEquiv (G : SimpleGraph V) (h : 0 < Fintype.card V) :
    (G ≃g G) ≃ Colored.Iso (onecell G h) (onecell G h) where
  toFun f := ⟨f, fun _ => Subsingleton.elim _ _⟩
  invFun f := f.graphIso
  left_inv _ := rfl
  right_inv _ := Colored.Iso.ext (fun _ => rfl)

/-- Encoding identifies the cardinality of a Mathlib coloured graph's
automorphism type with the executable graph's `Equiv.Perm` subgroup. -/
theorem card_coloredIso (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] :
    Nat.card (Colored.Iso G G) = Nat.card (Aut.equivGroup (encode e G)) :=
  (Nat.card_congr (autEquiv e G).toEquiv).trans (Aut.card_equivGroup _).symm

/-- The corresponding cardinality identity for an uncoloured Mathlib graph. -/
theorem card_graphIso (e : V ≃ Fin n) (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 0 < Fintype.card V) :
    Nat.card (G ≃g G) = Nat.card (Aut.equivGroup (encode e (onecell G h))) :=
  (Nat.card_congr (graphAutEquiv G h)).trans (card_coloredIso e _)

end Hex.GraphIso.Mathlib
