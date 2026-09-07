/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Basic

@[expose] public section

namespace Hex.LatticeEnum

/-- Rational triangular coefficients recovered from a single integer pass. -/
def coefficientsOfData (gs : GramSchmidt.Int.Data n) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if j < i then (gs.ν[(i, j)] : Rat) / gs.d[j.val + 1]
    else if i = j then 1 else 0

/-- Orthogonalize a prefix by forward substitution in the triangular matrix.
Each orthogonal row is computed once and reused by all later rows. -/
def orthogonalRows (rows : Matrix Int n m) (mu : Matrix Rat n n) :
    (k : Nat) → k ≤ n → Vector (Vector Rat m) k
  | 0, _ => #v[]
  | k + 1, hk =>
    let previous := orthogonalRows rows mu k (by omega)
    let i : Fin n := ⟨k, by omega⟩
    let projection := Fin.foldl k (fun acc j =>
      acc + mu[(i, (⟨j.val, by omega⟩ : Fin n))] • previous[j]) 0
    previous.push (((rows.getRow i).map fun x : Int => (x : Rat)) - projection)

/-- Rational data carried by an exhaustive certificate. -/
structure Data (n m : Nat) where
  /-- Unit lower-triangular Gram-Schmidt coefficient matrix. -/
  mu : Matrix Rat n n
  /-- Rational orthogonalized rows. -/
  orthogonal : Matrix Rat n m
  /-- Squared norms of the orthogonal rows. -/
  norms : Vector Rat n
  /-- Coordinates of the target projection in the orthogonal rows. -/
  projection : Vector Rat n
  /-- Component of the target orthogonal to the row span. -/
  residual : Vector Rat m

/-- Prepared data tied to one original basis and one target. -/
structure Prepared (b : Basis n m) (t : Vector Rat m) extends Data n m

/-- Prepare exact Gram-Schmidt data and retain the target's off-span component. -/
def prepare (b : Basis n m) (t : Vector Rat m) : Prepared b t :=
  let gs := GramSchmidt.Int.data b.rows
  let mu := coefficientsOfData gs
  let orthogonal := Matrix.ofRows (orthogonalRows b.rows mu n (Nat.le_refl n))
  let norms := Vector.ofFn fun i : Fin n =>
    (gs.d[i.val + 1] : Rat) / gs.d[i.val]
  let projection := Vector.ofFn fun i : Fin n =>
    t.dotProduct (orthogonal.getRow i) / norms[i]
  ⟨⟨mu, orthogonal, norms, projection, t - Matrix.vecMul projection orthogonal⟩⟩

variable {n m : Nat} {b : Basis n m} {t : Vector Rat m}

/-- Finite rational identities checked by certificate replay. -/
def Data.Valid (p : Data n m) (rows : Matrix Int n m) (t : Vector Rat m) : Prop :=
  (∀ i : Fin n, 0 < p.norms[i] ∧ p.norms[i] = (p.orthogonal.getRow i).normSq) ∧
  (∀ i j : Fin n, (i < j → p.mu[(i, j)] = 0) ∧
    (i = j → p.mu[(i, j)] = 1) ∧
    (i ≠ j → (p.orthogonal.getRow i).dotProduct (p.orthogonal.getRow j) = 0)) ∧
  p.mu * p.orthogonal = GramSchmidt.castIntMatrix rows ∧
  (∀ i : Fin n, p.projection[i] = t.dotProduct (p.orthogonal.getRow i) / p.norms[i]) ∧
  p.residual = t - Matrix.vecMul p.projection p.orthogonal

/-- Replay rational identities for untrusted certificate data. -/
def Data.check (p : Data n m) (rows : Matrix Int n m) (t : Vector Rat m) : Bool :=
  let reconstructed := p.mu * p.orthogonal
  decide (
    (∀ i : Fin n, 0 < p.norms[i] ∧ p.norms[i] = (p.orthogonal.getRow i).normSq) ∧
    (∀ i j : Fin n, (i < j → p.mu[(i, j)] = 0) ∧
      (i = j → p.mu[(i, j)] = 1) ∧
      (i ≠ j → (p.orthogonal.getRow i).dotProduct (p.orthogonal.getRow j) = 0)) ∧
    (∀ i : Fin n, ∀ j : Fin m, reconstructed[(i, j)] = ((rows[(i, j)] : Int) : Rat)) ∧
    (∀ i : Fin n, p.projection[i] = t.dotProduct (p.orthogonal.getRow i) / p.norms[i]) ∧
    p.residual = subtract t (Matrix.vecMul p.projection p.orthogonal))

/-- The kernel-reducible data check decides exactly the preparation identities. -/
@[simp] theorem Data.check_iff (p : Data n m) (rows : Matrix Int n m) (t : Vector Rat m) :
    p.check rows t = true ↔ p.Valid rows t := by
  have hc : (∀ i : Fin n, ∀ j : Fin m,
      (p.mu * p.orthogonal)[(i, j)] = ((rows[(i, j)] : Int) : Rat)) ↔
      p.mu * p.orthogonal = GramSchmidt.castIntMatrix rows := by
    constructor
    · intro h
      apply Matrix.ext_getElem
      intro i j
      simpa [GramSchmidt.castIntMatrix] using h i j
    · intro h i j
      rw [h]
      simp [GramSchmidt.castIntMatrix]
  simp only [Data.check, decide_eq_true_eq, hc, subtract_eq, Data.Valid]

/-- Validity includes the exact basis and target of the prepared value. -/
def Prepared.Valid (p : Prepared b t) : Prop := p.toData.Valid b.rows t

/-- Replay every preparation identity by exact rational arithmetic. -/
def Prepared.check (p : Prepared b t) : Bool := p.toData.check b.rows t

/-- Centre for the next coefficient after a suffix has been chosen. -/
def Data.centre (p : Data n m) (z : Vector Int n) (i : Fin n) : Rat :=
  p.projection[i] - (List.finRange n).foldl (fun acc j =>
    if i < j then acc + p.mu[(j, i)] * (z[j] : Rat) else acc) 0

/-- Allocation-free compiled centre calculation; the exposed definition remains kernel-reducible. -/
def Data.centreImpl (p : Data n m) (z : Vector Int n) (i : Fin n) : Rat :=
  p.projection[i] - Fin.foldl n (fun acc j =>
    if i < j then acc + p.mu[(j, i)] * (z[j] : Rat) else acc) 0

@[csimp] theorem Data.centre_eq_impl : @Data.centre = @Data.centreImpl := by
  funext n m p z i
  simp only [Data.centre, Data.centreImpl, Fin.foldl_eq_finRange_foldl]

/-- Centre in data prepared for this basis and target. -/
def Prepared.centre (p : Prepared b t) (z : Vector Int n) (i : Fin n) : Rat :=
  p.toData.centre z i


end Hex.LatticeEnum
