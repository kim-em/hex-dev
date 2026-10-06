/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Pack

public section

/-!
Kernel certificates for generated permutation groups and their Boolean checker.

A certificate is a list of stabilizer-chain levels in raw form. The checker is
split into pieces (`inputsOk`, `levelOk` and `pairsOk` over ranges of Schreier
pairs) so that a large certificate can be checked in several declarations,
each within the default kernel budget. `check` is their conjunction.
-/

namespace Hex.PermGroup.Kernel

open Hex.Kernel

/-- One level of a kernel certificate. `orbit`, `reps`, `invs` and `parents`
are read at indices below `size` only. -/
structure Level where
  /-- The base point. -/
  base : Nat
  /-- The number of orbit points. -/
  size : Nat
  /-- The packed generators of this level. -/
  gens : List Nat
  /-- Orbit point `j`, with `orbit.get 0 = base`. -/
  orbit : Lean.RArray Nat
  /-- The packed transversal element mapping `base` to orbit point `j`. -/
  reps : Lean.RArray Nat
  /-- The packed inverse of `reps.get j`. -/
  invs : Lean.RArray Nat
  /-- For `0 < j`, the Schreier-tree edge `(i, k)` with `reps.get j = gens[i] * reps.get k`. -/
  parents : Lean.RArray (Nat × Nat)
  /-- Field `x` is `j + 1` when `x` is orbit point `j`, and `0` off the orbit. -/
  lookup : Nat
  /-- For each generator of the next level, the Schreier-pair indices `(i, j)`
  of the Schreier generators whose product it is. -/
  next : List (List (Nat × Nat))

instance : Inhabited Level :=
  ⟨⟨0, 0, [], .leaf 0, .leaf 0, .leaf 0, .leaf (0, 0), 0, []⟩⟩

/-- A kernel certificate: the nontrivial levels of a stabilizer chain. -/
abbrev Certificate := List Level

/-- Generator `i` of a level (`0` out of range). -/
@[expose] def gen (L : Level) (i : Nat) : Nat := L.gens.getD i 0

/-- The Schreier generator `t_k⁻¹ * s_i * t_j` with `t_k(base) = s_i(t_j(base))`. -/
@[expose] def schreier (n W : Nat) (L : Level) (i j : Nat) : Nat :=
  let s := gen L i
  let k := Nat.sub (field W L.lookup (field W s (L.orbit.get j))) 1
  comp n W (L.invs.get k) (comp n W s (L.reps.get j))

/-- Sift a packed permutation through the levels, accepting as soon as the
residual is `e`. -/
@[expose] def sift (n W e : Nat) : List Level → Nat → Bool
  | [], x => Nat.beq x e
  | L :: rest, x =>
    cond (Nat.beq x e) true <|
      let j := field W L.lookup (field W x L.base)
      cond (Nat.beq j 0) false (sift n W e rest (comp n W (L.invs.get (Nat.sub j 1)) x))

/-- Items 3 and 5 of the SPEC's checker for the Schreier pairs `p` with
`lo ≤ p < hi`, where pair `p` is generator `p / size` and orbit point `p % size`. -/
@[expose] def pairsOk (n W e : Nat) (L : Level) (rest : List Level) (lo hi : Nat) : Bool :=
  allRange (Nat.sub hi lo) fun t =>
    let p := Nat.add lo t
    let i := Nat.div p L.size
    let j := Nat.mod p L.size
    let y := field W (gen L i) (L.orbit.get j)
    (!Nat.beq (field W L.lookup y) 0) && sift n W e rest (schreier n W L i j)

/-- Item 1: the orbit and lookup table agree, and every point is below `n`. -/
@[expose] def shapeOk (n W : Nat) (L : Level) : Bool :=
  Nat.blt L.base n && Nat.blt 0 L.size && Nat.beq (L.orbit.get 0) L.base &&
  allRange L.size (fun j =>
    Nat.blt (L.orbit.get j) n && Nat.beq (field W L.lookup (L.orbit.get j)) (Nat.succ j)) &&
  allRange n (fun x =>
    let v := field W L.lookup x
    Nat.beq v 0 || (Nat.ble v L.size && Nat.beq (L.orbit.get (Nat.sub v 1)) x))

/-- Item 4: the transversal follows its Schreier tree, and the stored inverses
are inverses. -/
@[expose] def transversalOk (n W e : Nat) (L : Level) : Bool :=
  Nat.beq (L.reps.get 0) e &&
  allRange L.size (fun j =>
    Nat.beq j 0 ||
      (Nat.blt (L.parents.get j).1 L.gens.length && Nat.blt (L.parents.get j).2 j &&
        Nat.beq (field W (gen L (L.parents.get j).1) (L.orbit.get (L.parents.get j).2))
          (L.orbit.get j) &&
        Nat.beq (L.reps.get j)
          (comp n W (gen L (L.parents.get j).1) (L.reps.get (L.parents.get j).2)))) &&
  allRange L.size (fun j => Nat.beq (comp n W (L.invs.get j) (L.reps.get j)) e)

/-- The product of the Schreier generators at the given pairs, leftmost
outermost; `e` for no pairs. -/
@[expose] def schreierProduct (n W e : Nat) (L : Level) : List (Nat × Nat) → Nat
  | [] => e
  | q :: qs => comp n W (schreier n W L q.1 q.2) (schreierProduct n W e L qs)

/-- Item 6: each generator of the next level is the product of the Schreier
generators at its recorded indices. -/
@[expose] def nextOk (n W e : Nat) (L : Level) (nextGens : List Nat) : Bool :=
  Nat.beq L.next.length nextGens.length &&
  (L.next.zip nextGens).all fun q =>
    q.1.all (fun p => Nat.blt p.1 L.gens.length && Nat.blt p.2 L.size) &&
      Nat.beq (schreierProduct n W e L q.1) q.2

/-- The generators of the first of the given levels, or none. -/
@[expose] def headGens : List Level → List Nat
  | [] => []
  | L :: _ => L.gens

/-- Items 1, 4 and 6 for one level followed by `rest`. Generators need not be
closed under inverses: in a finite group the inverse of a generator is one of
its powers. -/
@[expose] def levelOk (n W e : Nat) (L : Level) (rest : List Level) : Bool :=
  shapeOk n W L && transversalOk n W e L && nextOk n W e L (headGens rest)

/-- Item 2 for the inputs: every input sifts through the certificate, and every
first-level generator is an input or composes with one to the identity. -/
@[expose] def inputsOk (n W e : Nat) (inputs : List Nat) (c : List Level) : Bool :=
  (inputs.all fun x => sift n W e c x) &&
    ((headGens c).all fun s => inputs.any fun x => Nat.beq s x || Nat.beq (comp n W s x) e)

/-- Every level checked, each against the levels after it. -/
@[expose] def levelsOk (n W e : Nat) : List Level → Bool
  | [] => true
  | L :: rest =>
    levelOk n W e L rest && pairsOk n W e L rest 0 (Nat.mul L.gens.length L.size) &&
      levelsOk n W e rest

/-- The complete kernel check of a certificate for packed inputs of degree `n`. -/
@[expose] def check (n : Nat) (inputs : List Nat) (c : Certificate) : Bool :=
  inputsOk n (width n) (ident n (width n)) inputs c &&
    levelsOk n (width n) (ident n (width n)) c

/-- The order certified by `c`: the product of its orbit sizes. -/
@[expose] def order (c : Certificate) : Nat := c.foldr (fun L acc => Nat.mul L.size acc) 1

/-! # Assembling the pieces -/

theorem pairsOk_append (n W e : Nat) (L : Level) (rest : List Level) {lo mid hi : Nat}
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi)
    (ha : pairsOk n W e L rest lo mid = true) (hb : pairsOk n W e L rest mid hi = true) :
    pairsOk n W e L rest lo hi = true := by
  simp only [pairsOk, allRange_eq, List.all_eq_true, List.mem_range, Hex.Kernel.sub_eq,
    Hex.Kernel.add_eq] at ha hb ⊢
  intro t ht
  by_cases hlt : t < mid - lo
  · exact ha t hlt
  · have := hb (t - (mid - lo)) (by omega)
    rwa [show mid + (t - (mid - lo)) = lo + t by omega] at this

theorem pairsOk_nil (n W e : Nat) (L : Level) (rest : List Level) (k : Nat) :
    pairsOk n W e L rest k k = true := by
  simp [pairsOk, allRange_eq]

end Hex.PermGroup.Kernel
