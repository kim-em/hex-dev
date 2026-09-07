/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Cert
public import HexLLL.Reduction

@[expose] public section

namespace Hex.LatticeEnum

variable {n m : Nat} {b : Basis n m} {t : Vector Rat m}

/-- Reuse the same basis orthogonalization for another target, recomputing its projection and residual. -/
def retarget (p : Prepared b t) (target : Vector Rat m) : Prepared b target :=
  let projection := Hex.Vector.ofFn' fun i => target.dotProduct (p.orthogonal.getRow i) / p.norms[i]
  { p.toData with projection, residual := subtract target (Matrix.vecMul projection p.orthogonal) }

/-- A checked change of working basis, retaining the original input in its type. -/
structure BasisChange (b : Basis n m) where
  /-- Independent working basis used for search. -/
  working : Basis n m
  /-- Forward transformation of original rows into working rows. -/
  forward : Matrix Int n n
  /-- Reverse transformation of working rows into original rows. -/
  reverse : Matrix Int n n
  /-- Both integer product identities passed the existing same-lattice checker. -/
  checked : Matrix.sameLatticeCert b.rows working.rows forward reverse = true

/-- Validate a supplied independent working basis and both integer transformations. -/
def checkBasisChange (b : Basis n m) (rows : Matrix Int n m) (forward reverse : Matrix Int n n) :
    Option (BasisChange b) := do
  let working ← ofMatrix? rows
  if h : Matrix.sameLatticeCert b.rows working.rows forward reverse = true then
    return ⟨working, forward, reverse, h⟩
  else none

/-- The original basis is always an available checked working basis. -/
def BasisChange.identity (b : Basis n m) : BasisChange b :=
  ⟨b, Matrix.identity n, Matrix.identity n, by
    simp only [Matrix.sameLatticeCert, Bool.and_eq_true, Matrix.mulEqCert_iff, Matrix.identity_mul, and_self]⟩

/-- Reconstruct original coefficients using the transpose of the forward row transform. -/
def BasisChange.point (change : BasisChange b) (t : Vector Rat m) (q : Point n m) : Point n m :=
  LatticeEnum.point b t (change.forward.transpose * q.coefficients)

/-- Transform and sort every reported point in original-basis coordinates. -/
def BasisChange.points (change : BasisChange b) (t : Vector Rat m) (ps : List (Point n m)) : List (Point n m) :=
  sortPoints (ps.map (change.point t))

/-- Enumerate using the checked working basis and return original coefficients. -/
def BasisChange.enumerate (change : BasisChange b) (t : Vector Rat m) (r : Rat) : List (Point n m) :=
  change.points t (LatticeEnum.enumerate change.working t r)

/-- Transport both complete and partial enumeration output; pending suffixes refer to the working basis. -/
def BasisChange.enumerateWith (change : BasisChange b) (budget : Budget) (t : Vector Rat m) (r : Rat) :
    Enumeration n m :=
  match LatticeEnum.enumerateWith budget change.working t r with
  | .complete ps tree counts => .complete (change.points t ps) tree counts
  | .incomplete ps pending counts => .incomplete (change.points t ps) pending counts

/-- Transport an all-minima result to original coefficients. -/
def BasisChange.minimum (change : BasisChange b) (t : Vector Rat m) (answer : Minimum n m) : Minimum n m :=
  ⟨change.points t answer.points, answer.distanceSq⟩

/-- Transport optimization output, keeping pending traversal coordinates in the working basis. -/
def BasisChange.optimization (change : BasisChange b) (t : Vector Rat m) : Optimization n m → Optimization n m
  | .complete answer tree counts => .complete (change.minimum t answer) tree counts
  | .incomplete incumbent ps pending phase counts =>
    .incomplete (change.point t incumbent) (change.points t ps) pending phase counts

/-- All closest vectors computed in a checked working basis. -/
def BasisChange.closest (change : BasisChange b) (t : Vector Rat m) : Minimum n m :=
  change.minimum t (LatticeEnum.closest change.working t)

/-- Budgeted closest-vector search with original-basis answers. -/
def BasisChange.closestWith (change : BasisChange b) (budget : Budget) (t : Vector Rat m) : Optimization n m :=
  change.optimization t (LatticeEnum.closestWith budget change.working t)

/-- All shortest nonzero vectors computed in a checked working basis. -/
def BasisChange.shortest (change : BasisChange b) : Option (Minimum n m) :=
  (LatticeEnum.shortest change.working).map (change.minimum 0)

/-- Budgeted shortest-vector search with original-basis answers. -/
def BasisChange.shortestWith (change : BasisChange b) (budget : Budget) : Option (Optimization n m) :=
  (LatticeEnum.shortestWith budget change.working).map (change.optimization 0)

/-- Package the working tree with its checked transforms and original-basis points. -/
def BasisChange.certificate (change : BasisChange b) (t : Vector Rat m) (r : Rat) : Certificate n m :=
  let cert := enumerationCertificate change.working t r
  { cert with forward := change.forward, reverse := change.reverse, points := change.points t cert.points }

/-- Transform a native optimum certificate while retaining its complete working-basis tree. -/
def BasisChange.optimumCertificate (change : BasisChange b) (t : Vector Rat m)
    (cert : OptimumCertificate n m) : OptimumCertificate n m :=
  ⟨change.point t cert.candidate, { cert.enumeration with
    forward := change.forward
    reverse := change.reverse
    points := change.points t cert.enumeration.points }⟩

/-- Produce a closest-vector certificate in original input coordinates after preprocessing. -/
def BasisChange.closestCertificate (change : BasisChange b) (t : Vector Rat m) : OptimumCertificate n m :=
  change.optimumCertificate t (LatticeEnum.closestCertificate change.working t)

/-- Produce a shortest-vector certificate in original input coordinates after preprocessing. -/
def BasisChange.shortestCertificate (change : BasisChange b) : Option (OptimumCertificate n m) :=
  (LatticeEnum.shortestCertificate change.working).map (change.optimumCertificate 0)

/-- Recover row coordinates by nearest plane using a shared orthogonalization.
A proposed change is accepted only after replaying both exact matrix identities. -/
def rowCoordinates (p : Prepared b t) (rows : Matrix Int n m) : Matrix Int n n :=
  Matrix.ofRows (Hex.Vector.ofFn' fun i =>
    nearestPlane (retarget p (castVector (rows.getRow i))) n (Nat.le_refl n) 0)

/-- Try the existing LLL reducer and validate both recovered row transforms.
Rank zero and rejected preprocessing use the checked identity change. The default
parameters and optional external-provider policy are exactly those of `Hex.lll`. -/
def lllPreprocess (b : Basis n m) (δ : Rat := 3/4)
    (hδ : (121 / 400 : Rat) < δ := by grind) (hδ' : δ ≤ 1 := by grind) : BasisChange b :=
  if hn : 1 ≤ n then
    let rows := Hex.lll b.rows δ hδ hδ' hn
    match ofMatrix? rows with
    | none => .identity b
    | some working =>
      let forward := rowCoordinates (prepare b 0) rows
      let reverse := rowCoordinates (prepare working 0) b.rows
      if h : Matrix.sameLatticeCert b.rows working.rows forward reverse = true then
        ⟨working, forward, reverse, h⟩
      else .identity b
  else .identity b

end Hex.LatticeEnum
