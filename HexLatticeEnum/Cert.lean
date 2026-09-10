/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Shortest

@[expose] public section

namespace Hex.LatticeEnum

/-- Literal data for replay of an exhaustive ball, including optional preprocessing.
The identity transforms represent a run in the original basis. -/
structure Certificate (n m : Nat) where
  /-- Working row basis used by the coefficient tree. -/
  rows : Matrix Int n m
  /-- Forward row transformation from the original basis. -/
  forward : Matrix Int n n
  /-- Reverse row transformation to the original basis. -/
  reverse : Matrix Int n n
  /-- Rational preparation data, independently checked at replay time. -/
  data : Data n m
  /-- Exhaustive fixed-radius tree. -/
  tree : Tree
  /-- Claimed original-basis results in ambient lexicographic order. -/
  points : List (Point n m)

/-- Remaining replay budget and reconstructed leaves. -/
structure Replay (n m : Nat) where
  /-- Directly reconstructed original-basis points. -/
  points : List (Point n m)
  /-- Unconsumed node allowance. -/
  remaining : Nat

/-- Exact child coverage, allowing any permutation but no missing or duplicate labels. -/
def checkLabels (interval : Interval) (children : List (Int × Tree)) : Bool :=
  children.length == interval.size &&
    Hex.List.sort (children.map Prod.fst) (fun x y => x ≤ y) ==
      (List.range interval.size).map (fun (i : Nat) => interval.lo + (i : Int))

/-- Replay a coefficient tree with a global node limit and recomputed suffix costs.
The checker descends by dimension and consumes the allowance across siblings. -/
def replayAux (rows : Matrix Int n m) (t : Vector Rat m) (radius : Rat)
    (forward : Matrix Int n n) (data : Data n m) (residualSq : Rat) :
    (k : Nat) → k ≤ n → Vector Int n → Rat → Tree → Nat → Option (Replay n m)
  | _, _, _, _, _, 0 => none
  | 0, _, z, _, tree, fuel + 1 =>
    let p := pointRows rows t (forward.transpose * z)
    match tree with
    | .leaf => if p.distanceSq ≤ radius then some ⟨[p], fuel⟩ else none
    | .empty => if radius < p.distanceSq then some ⟨[], fuel⟩ else none
    | .node .. => none
  | k + 1, hk, z, suffix, tree, fuel + 1 =>
    let i : Fin n := ⟨k, by omega⟩
    let centre := data.centre z i
    let interval := bounds centre data.norms[i] (radius - residualSq - suffix)
    match tree with
    | .leaf => none
    | .empty => if interval.size == 0 then some ⟨[], fuel⟩ else none
    | .node claimed children => do
      if claimed != interval || interval.size > fuel || !checkLabels interval children then none
      else
        let visitChild := fun (a : Int) (tree : Tree) (remaining : Nat) =>
          let delta := (a : Rat) - centre
          replayAux rows t radius forward data residualSq k (by omega) (z.set k a (by omega))
            (suffix + data.norms[i] * delta * delta) tree remaining
        let rec loop (children : List (Int × Tree)) (remaining : Nat)
            (points : List (Point n m)) : Option (Replay n m) := do
          match children with
          | [] => some ⟨points.reverse, remaining⟩
          | (a, tree) :: children =>
            let child ← visitChild a tree remaining
            loop children child.remaining (child.points.reverse ++ points)
        loop children fuel []
termination_by k _ _ _ _ _ => k

/-- Replay computes the constant residual norm once, independently of producer caches. -/
def replay (rows : Matrix Int n m) (t : Vector Rat m) (radius : Rat)
    (forward : Matrix Int n n) (data : Data n m) (k : Nat) (hk : k ≤ n)
    (z : Vector Int n) (suffix : Rat) (tree : Tree) (maxNodes : Nat) : Option (Replay n m) :=
  replayAux rows t radius forward data data.residual.normSq k hk z suffix tree maxNodes

/-- Check transforms, preparation identities, every branch, and the claimed output.
The replay bound is independent of the producer's resource limits. -/
def checkEnumerationWith (maxNodes : Nat) (rows : Matrix Int n m) (t : Vector Rat m)
    (radius : Rat) (cert : Certificate n m) : Bool :=
  Matrix.sameLatticeCert rows cert.rows cert.forward cert.reverse &&
    cert.data.check cert.rows t &&
    match replay rows t radius cert.forward cert.data n (Nat.le_refl n) (Vector.replicate n 0) 0 cert.tree maxNodes with
    | none => false
    | some result => decide (sortPoints result.points = cert.points)

/-- Exact number of nodes in an exhaustive tree. -/
def Tree.nodes : Tree → Nat
  | .empty | .leaf => 1
  | .node _ children => 1 + (children.attach.map fun child => child.val.2.nodes).sum
termination_by tree => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem child.property
  have hp : sizeOf child.val = 1 + sizeOf child.val.1 + sizeOf child.val.2 := by
    cases child.val
    rfl
  simp_all
  omega

/-- Unbudgeted replay uses the exact node count of the finite supplied tree. -/
def checkEnumeration (rows : Matrix Int n m) (t : Vector Rat m)
    (radius : Rat) (cert : Certificate n m) : Bool :=
  checkEnumerationWith cert.tree.nodes rows t radius cert

/-- Produce a complete certificate in the original basis using the common traversal. -/
def enumerationCertificate (b : Basis n m) (t : Vector Rat m) (radius : Rat) : Certificate n m :=
  let p := prepare b t
  let run := traverse b t p {} .ball n (Nat.le_refl n) 0 0 { radius := radius }
  ⟨b.rows, Matrix.identity n, Matrix.identity n, p.toData,
    run.tree.getD .empty, sortPoints run.state.points⟩

/-- An attained optimum together with an exhaustive ball at its exact distance. -/
structure OptimumCertificate (n m : Nat) where
  /-- Directly checked candidate proving attainment. -/
  candidate : Point n m
  /-- Exhaustive ball containing every possible improvement and tie. -/
  enumeration : Certificate n m

/-- Package the exhaustive tie pass without repeating preparation or enumeration. -/
def optimumCertificate (b : Basis n m) (p : Prepared b t)
    (run : OptimumRun n m) : OptimumCertificate n m :=
  ⟨run.incumbent, ⟨b.rows, Matrix.identity n, Matrix.identity n, p.toData,
    run.traversal.tree.getD .empty, sortPoints run.traversal.state.points⟩⟩

/-- Produce an attained closest point and the complete fixed-radius certificate for all ties. -/
def closestCertificate (b : Basis n m) (t : Vector Rat m) : OptimumCertificate n m :=
  let p := prepare b t
  let seed := point b t (nearestPlane p n (Nat.le_refl n) 0)
  optimumCertificate b p (optimize {} b t p .closest seed)

/-- Produce a shortest-vector certificate; rank zero has no nonzero optimum. -/
def shortestCertificate (b : Basis n m) : Option (OptimumCertificate n m) :=
  shortestSeed b |>.map fun seed =>
    let p := prepare b 0
    optimumCertificate b p (optimize {} b 0 p .shortest seed)

/-- Replay a global closest-vector certificate with a limit on visited certificate nodes. -/
def checkClosestWith (maxNodes : Nat) (rows : Matrix Int n m) (t : Vector Rat m)
    (cert : OptimumCertificate n m) : Bool :=
  checkPoint rows t cert.candidate &&
    checkEnumerationWith maxNodes rows t cert.candidate.distanceSq cert.enumeration &&
    cert.enumeration.points.all (fun p => p.distanceSq == cert.candidate.distanceSq)

/-- Replay a global closest-vector certificate, including every tie. -/
def checkClosest (rows : Matrix Int n m) (t : Vector Rat m) (cert : OptimumCertificate n m) : Bool :=
  checkClosestWith cert.enumeration.tree.nodes rows t cert

/-- Replay a global nonzero shortest-vector certificate with a limit on visited certificate nodes. -/
def checkShortestWith (maxNodes : Nat) (rows : Matrix Int n m) (cert : OptimumCertificate n m) : Bool :=
  decide (cert.candidate.ambient ≠ Vector.replicate m 0) &&
    checkPoint rows (Vector.replicate m 0) cert.candidate &&
    checkEnumerationWith maxNodes rows (Vector.replicate m 0) cert.candidate.distanceSq cert.enumeration &&
    cert.enumeration.points.all (fun p => decide (p.ambient = Vector.replicate m 0) ||
      p.distanceSq == cert.candidate.distanceSq)

/-- Replay a global nonzero shortest-vector certificate, including both signs. -/
def checkShortest (rows : Matrix Int n m) (cert : OptimumCertificate n m) : Bool :=
  checkShortestWith cert.enumeration.tree.nodes rows cert

end Hex.LatticeEnum
