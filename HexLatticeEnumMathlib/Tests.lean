/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexLatticeEnum
import HexLatticeEnumMathlib

/-! Build-only examples of mathematical preparation and literal kernel certificate replay. -/

open Hex Hex.LatticeEnum HexLatticeEnumMathlib

example (b : Basis n m) (t : Vector Rat m) : (prepare b t).Valid := prepare_valid b t

example (b : Basis n m) : Function.Injective (vector b) := vector_injective b

example (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) :
    distanceSq b t z = (prepare b t).residual.normSq +
      ∑ i : Fin n, (prepare b t).norms[i] * ((z[i] : Rat) - (prepare b t).centre z i) ^ 2 :=
  distance_decomposition (prepare b t).toData b.rows t (prepare_valid b t) z

example (b : Basis n m) (t : Vector Rat m) (v : Vector Int m) :
    v ∈ (closest b t).points.map Point.ambient ↔
      b.rows.memLattice v ∧ ∀ w, b.rows.memLattice w → distance v t ≤ distance w t :=
  closest_spec b t v

example (b : Basis n m) : shortest b = none ↔ n = 0 := shortest_none b

example (b : Basis n m) (answer : Minimum n m) (h : shortest b = some answer)
    (v : Vector Int m) : v ∈ answer.points.map Point.ambient ↔
      b.rows.memLattice v ∧ v ≠ 0 ∧
        ∀ w, b.rows.memLattice w → w ≠ 0 → distance v 0 ≤ distance w 0 :=
  shortest_spec b answer h v

example (b : Basis n m) (t : Vector Rat m) (r : Rat) :
    checkEnumeration b.rows t r (enumerationCertificate b t r) = true :=
  enumerationCertificate_check b t r

example (b : Basis n m) (t : Vector Rat m) : checkClosest b.rows t (closestCertificate b t) = true :=
  closestCertificate_check b t

example (b : Basis n m) (cert : OptimumCertificate n m) (h : shortestCertificate b = some cert) :
    checkShortest b.rows cert = true := shortestCertificate_check b cert h

example (b : Basis n m) (t : Vector Rat m) (budget : Budget) :
    OptimizationSpec b t .closest (closestWith budget b t) := closestWith_spec b t budget

example (b : Basis n m) (t : Vector Rat m) (r : Rat) (budget : Budget) :
    match enumerateWith budget b t r with
    | .complete _ _ counts | .incomplete _ _ counts => Within budget counts :=
  enumerateWith_within b t r budget

example (b : Basis n m) (change : BasisChange b) (t : Vector Rat m) (r : Rat) :
    change.enumerate t r = enumerate b t r := change_enumerate change t r

example (b : Basis n m) (change : BasisChange b) (t : Vector Rat m) (r : Rat) :
    checkEnumeration b.rows t r (change.certificate t r) = true := change_certificate_check change t r

private def halfCertificate : Certificate 1 1 where
  rows := Matrix.ofRows #v[#v[1]]
  forward := Matrix.ofRows #v[#v[1]]
  reverse := Matrix.ofRows #v[#v[1]]
  data := ⟨Matrix.ofRows #v[#v[1]], Matrix.ofRows #v[#v[1]], #v[1], #v[1/2], #v[0]⟩
  tree := .node ⟨0, 1⟩ [(0, .leaf), (1, .leaf)]
  points := [⟨#v[0], #v[0], 1/4⟩, ⟨#v[1], #v[1], 1/4⟩]

example : checkPoint (Matrix.ofRows #v[#v[1]]) #v[1/2]
    (⟨#v[0], #v[0], 1/4⟩ : Point 1 1) = true := by decide +kernel
example : Matrix.sameLatticeCert (Matrix.ofRows #v[#v[1]]) halfCertificate.rows
    halfCertificate.forward halfCertificate.reverse = true := by decide +kernel
example : halfCertificate.data.check halfCertificate.rows #v[1/2] = true := by decide +kernel
example : checkEnumeration (Matrix.ofRows #v[#v[1]]) #v[1/2] (1/4) halfCertificate = true := by
  decide +kernel

example : checkClosest (Matrix.ofRows #v[#v[1]]) #v[1/2]
    ⟨⟨#v[0], #v[0], 1/4⟩, halfCertificate⟩ = true := by decide +kernel

example : checkClosestWith 3 (Matrix.ofRows #v[#v[1]]) #v[1/2]
    ⟨⟨#v[0], #v[0], 1/4⟩, halfCertificate⟩ = true := by decide +kernel

example : checkClosestWith 2 (Matrix.ofRows #v[#v[1]]) #v[1/2]
    ⟨⟨#v[0], #v[0], 1/4⟩, halfCertificate⟩ = false := by decide +kernel

example (b : Basis 1 1) (hb : b.rows = Matrix.ofRows #v[#v[1]]) :
    Optimal b #v[1/2] .closest (⟨#v[0], #v[0], 1/4⟩ : Point 1 1) := by
  apply (checkClosestWith_sound 3 b #v[1/2] ⟨⟨#v[0], #v[0], 1/4⟩, halfCertificate⟩ ?_).1
  rw [hb]
  decide +kernel

example (b : Basis 1 1) (hb : b.rows = Matrix.ofRows #v[#v[1]]) :
    Optimal b #v[1/2] .closest (⟨#v[0], #v[0], 1/4⟩ : Point 1 1) := by
  apply (checkClosest_sound b #v[1/2] ⟨⟨#v[0], #v[0], 1/4⟩, halfCertificate⟩ ?_).1
  rw [hb]
  decide +kernel

example (b : Basis 1 1) (hb : b.rows = Matrix.ofRows #v[#v[1]]) (v : Vector Int 1) :
    v ∈ halfCertificate.points.map Point.ambient ↔ b.rows.memLattice v ∧ distance v #v[1/2] ≤ 1/4 := by
  apply checkEnumeration_sound b #v[1/2] (1/4) halfCertificate ?_ v
  rw [hb]
  decide +kernel

example : (bounds 0 1 4).lo = -2 := by decide +kernel

private def unitCertificate : Certificate 1 1 where
  rows := Matrix.ofRows #v[#v[1]]
  forward := Matrix.ofRows #v[#v[1]]
  reverse := Matrix.ofRows #v[#v[1]]
  data := ⟨Matrix.ofRows #v[#v[1]], Matrix.ofRows #v[#v[1]], #v[1], #v[0], #v[0]⟩
  tree := .node ⟨-1, 1⟩ [(0, .leaf), (-1, .leaf), (1, .leaf)]
  points := [⟨#v[-1], #v[-1], 1⟩, ⟨#v[0], #v[0], 0⟩, ⟨#v[1], #v[1], 1⟩]

example : checkShortest (Matrix.ofRows #v[#v[1]])
    ⟨⟨#v[1], #v[1], 1⟩, unitCertificate⟩ = true := by decide +kernel

example : checkShortestWith 4 (Matrix.ofRows #v[#v[1]])
    ⟨⟨#v[1], #v[1], 1⟩, unitCertificate⟩ = true := by decide +kernel

example : checkShortestWith 3 (Matrix.ofRows #v[#v[1]])
    ⟨⟨#v[1], #v[1], 1⟩, unitCertificate⟩ = false := by decide +kernel

example : checkEnumeration (Matrix.ofRows #v[#v[1]]) #v[0] 1
    { unitCertificate with tree := .node ⟨-1, 1⟩ [(0, .leaf), (1, .leaf)] } = false := by
  decide +kernel

example (c : Rat) (interval : Interval) :
    ((coefficients interval c).toList).Pairwise (Nearer c) := coefficients_ordered interval c

example (c : Rat) (z : Int) : Nearer c (nearest c) z := nearest_spec c z

example (b : Basis n m) (t : Vector Rat m) (x : EuclideanSpace Real (Fin m)) :
    x ∈ ((closest b t).points.map Point.ambient).map realVector ↔
      x ∈ realLattice b ∧ ∀ y ∈ realLattice b, dist x (realTarget t) ≤ dist y (realTarget t) :=
  closest_real_spec b t x

example (b : Basis n m) : IsDiscrete (realLattice b : Set (EuclideanSpace Real (Fin m))) :=
  realLattice_discrete b

example (b : Basis n m) (a : Minimum n m) (h : shortest b = some a) (r : Real) :
    IsPacking b r ↔ r ≤ Real.sqrt (a.distanceSq : Real) / 2 := packing_radius b a h r

example (b : Basis n m) (a : Minimum n m) (h : shortest b = some a) :
    (contacts b (Real.sqrt (a.distanceSq : Real) / 2)).ncard = a.points.length :=
  kissing_number b a h

example (b : Basis n m) (hn : 1 ≤ n) :
    Hex.isLLLReduced (lllPreprocess b).working.rows (3/4) (11/20) :=
  lllPreprocess_reduced b (3/4) (by norm_num) (by norm_num) hn

example (b : Basis n m) (change : BasisChange b) (t : Vector Rat m) :
    checkClosest b.rows t (change.closestCertificate t) = true :=
  change_closestCertificate_check change t

example (b : Basis n m) (change : BasisChange b) (c : OptimumCertificate n m)
    (h : change.shortestCertificate = some c) : checkShortest b.rows c = true :=
  change_shortestCertificate_check change c h
