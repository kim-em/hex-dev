/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Reconstruction
public import HexModularMatrix.Solve
public import HexModularMatrix.FlatImage
public import HexBasic.Rand

public section

namespace Hex.Matrix
namespace Dixon

/-- Flat forward elimination avoids copying trailing minors or computing inverses.
The original determinant elimination handles failed checked candidates. -/
def flatImage (A : Matrix Int n n) (m : Nat) : Option (Vector Int 1) :=
  if h : 0 < m ∧ m < 2 ^ 31 then
    letI : ZMod64.Bounds m := ⟨h.1, h.2⟩
    match flatDet? (A.mapEntries (ZMod64.intCast m)) with
    | some d => some (Vector.replicate 1 (d.toNat : Int))
    | none => DetImage.image A m
  else none

theorem flatImage_eq {A : Matrix Int n n} {m : Nat} {r : Vector Int 1}
    (h : flatImage A m = some r) (i : Fin 1) : r[i] % (m : Int) = det A % (m : Int) := by
  unfold flatImage at h
  split at h <;> try contradiction
  rename_i hm
  letI : ZMod64.Bounds m := ⟨hm.1, hm.2⟩
  split at h
  · rename_i d hd
    cases h
    have he := flatDet?_eq hd
    rw [det_mapEntries A (ZMod64.intCast m)
      (Lean.Grind.Ring.intCast_zero) (Lean.Grind.Ring.intCast_one)
      (Lean.Grind.Ring.intCast_add) (Lean.Grind.Ring.intCast_mul)] at he
    have ht := congrArg (fun x : ZMod64 m => (x.toNat : Int)) he
    rw [ZMod64.toNat_intCast] at ht
    simp only [Fin.getElem_fin, Vector.getElem_replicate, ← ht, Int.emod_emod]
  · exact DetImage.image_eq h i

/-- Reuse the decomposition's determinant image without another elimination. -/
def detImage (D : Decomp n) (m : Nat) : Option (Vector Int 1) :=
  if m = D.p then some (Vector.replicate 1 D.detImage) else flatImage D.A m

theorem detImage_eq {D : Decomp n} {m : Nat} {r : Vector Int 1}
    (h : detImage D m = some r) (i : Fin 1) :
    r[i] % (m : Int) = det D.A % (m : Int) := by
  unfold detImage at h
  split at h
  · rename_i hm
    cases h
    simp only [Fin.getElem_fin, Vector.getElem_replicate, hm]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr D.detImage_congr).symm
  · exact flatImage_eq h i

/-- A cofactor image exists only when the divisor is a unit at this modulus. -/
def cofactorImage (D : Decomp n) (d : Int) (m : Nat) : Option (Vector Int 1) :=
  if h : 0 < m ∧ m < 2 ^ 31 then
    letI : ZMod64.Bounds m := ⟨h.1, h.2⟩
    do
      let u ← ZMod64.inv? (ZMod64.intCast m d)
      let r ← detImage D m
      return Vector.replicate 1 ((ZMod64.intCast m r[0] * u).toNat : Int)
  else none

theorem cofactorImage_eq {D : Decomp n} {d : Int} {m : Nat} {r : Vector Int 1}
    (hd : d ∣ det D.A) (h : cofactorImage D d m = some r) (i : Fin 1) :
    r[i] % (m : Int) = (det D.A / d) % (m : Int) := by
  unfold cofactorImage at h
  split at h <;> try contradiction
  rename_i hm
  letI : ZMod64.Bounds m := ⟨hm.1, hm.2⟩
  obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have hinv := ZMod64.inv?_eq_some hu
  have himage : ZMod64.intCast m v[0] = ZMod64.intCast m (det D.A) := by
    apply ZMod64.ext_toNat
    apply Int.ofNat_inj.mp
    rw [ZMod64.toNat_intCast, ZMod64.toNat_intCast]
    exact detImage_eq hv 0
  have hprod : ZMod64.intCast m (det D.A) =
      ZMod64.intCast m d * ZMod64.intCast m (det D.A / d) := by
    calc
      ZMod64.intCast m (det D.A) = ZMod64.intCast m (d * (det D.A / d)) :=
        congrArg (ZMod64.intCast m) (Int.mul_ediv_cancel' hd).symm
      _ = _ := Lean.Grind.Ring.intCast_mul _ _
  have heq : ZMod64.intCast m v[0] * u = ZMod64.intCast m (det D.A / d) := by
    rw [himage, hprod]
    grind only
  simp only [Fin.getElem_fin, Vector.getElem_replicate, heq,
    ZMod64.toNat_intCast, Int.emod_emod]

/-- CRT state for the cofactor, beginning with the already computed image. -/
def cofactorCrtWith (D : Decomp n) (d : Int) (bound fuel : Nat) :
    Option (Modular.CrtVec 1) :=
  Modular.crtLoop (cofactorImage D d)
    (fun state => if 2 * bound < state.modulus then some state else none)
    (#[D.p] ++ ((ZMod64.primesBelow (2 ^ 31 - 1) fuel).map (·.m)).filter (· != D.p)) fuel

theorem cofactorCrtWith_eq {D : Decomp n} {d : Int} {bound fuel : Nat}
    {state : Modular.CrtVec 1} (hd : d ∣ det D.A)
    (hb : (det D.A / d).natAbs ≤ bound) (h : cofactorCrtWith D d bound fuel = some state) :
    state.value[0] = det D.A / d := by
  unfold cofactorCrtWith at h
  obtain ⟨consumed, s, _, _, _, trace, haccept⟩ := Modular.crtLoop_trace h
  split at haccept <;> try contradiction
  rename_i hbound
  cases haccept
  apply state.eq_of_congr (0 : Fin 1) (by omega)
  have hc := trace.congr (Vector.replicate 1 (det D.A / d)) (by
    intro j hj _ r hr i
    simpa only [Fin.getElem_fin, Vector.getElem_replicate] using cofactorImage_eq hd hr i)
  simpa only [Fin.getElem_fin, Vector.getElem_replicate] using hc (0 : Fin 1)

/-- First generate enough primes for the reduced bound; use the full budget
if skipped moduli prevent reconstruction from that prefix. -/
def cofactorCrt? (D : Decomp n) (d : Int) (bound fuel : Nat) :
    Option (Modular.CrtVec 1) :=
  match cofactorCrtWith D d bound (min fuel (bound.log2 / 30 + 2)) with
  | some state => some state
  | none => cofactorCrtWith D d bound fuel

theorem cofactorCrt?_eq {D : Decomp n} {d : Int} {bound fuel : Nat}
    {state : Modular.CrtVec 1} (hd : d ∣ det D.A)
    (hb : (det D.A / d).natAbs ≤ bound) (h : cofactorCrt? D d bound fuel = some state) :
    state.value[0] = det D.A / d := by
  unfold cofactorCrt? at h
  split at h
  · rename_i S hs
    cases h
    exact cofactorCrtWith_eq hd hb hs
  · exact cofactorCrtWith_eq hd hb h

/-- A seeded small integer right-hand side, consuming exactly one word per entry. -/
def draw (n : Nat) (r : Rand) : Vector Int n × Rand :=
  Fin.foldl n (fun (v, r) i =>
    let (word, r) := r.next
    (v.set i.val ((word.toNat % 65536 : Nat) - (32768 : Int)), r))
    (Vector.replicate n 0, r)

/-- Reduce and check a candidate before using its denominator as a divisor. -/
def cofactorWith (D : Decomp n) (b y : Vector Int n) (d : Int) (fuel : Nat) : Option Int := do
  let (_, d) ← check D.A b y d
  let state ← cofactorCrt? D d (hadamardBound D.A / d.natAbs) fuel
  return d * state.value[0]

theorem cofactorWith_eq [LawfulDetBound] {D : Decomp n} {b z : Vector Int n}
    {e : Int} {fuel : Nat} {v : Int} (h : cofactorWith D b z e fuel = some v) : v = det D.A := by
  obtain ⟨⟨y, d⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨state, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  obtain ⟨heq, hpos⟩ := check_spec hs
  have hd := dvd_det_of_mulVec D.det_ne_zero heq hpos (check_reduced hs)
  have hb : (det D.A / d).natAbs ≤ hadamardBound D.A / d.natAbs := by
    rw [Int.natAbs_ediv_of_dvd hd]
    exact Nat.div_le_div_right (LawfulDetBound.natAbs_det_le D.A)
  rw [cofactorCrt?_eq hd hb hc]
  exact Int.mul_ediv_cancel' hd

def viaDivisor (D : Decomp n) (b : Vector Int n) (fuel : Nat) : Option Int := do
  let (y, d) ← solveWith D b
  cofactorWith D b y d fuel

theorem viaDivisor_eq [LawfulDetBound] {D : Decomp n} {b : Vector Int n}
    {fuel : Nat} {v : Int} (h : viaDivisor D b fuel = some v) : v = det D.A := by
  obtain ⟨⟨y, d⟩, _, hc⟩ := Option.bind_eq_some_iff.mp h
  exact cofactorWith_eq hc

end Dixon

/-- Dixon's reduced denominator followed by CRT of the determinant cofactor.
The returned random state records the draws even when reconstruction exhausts fuel. -/
def detViaDivisorWith (A : Matrix Int n n) (r : Rand) (fuel : Nat) : Option Int × Rand :=
  if fuel = 0 then (none, r)
  else match decomp? A (solveFuel A) with
  | none => (none, r)
  | some D =>
    let (b, r) := Dixon.draw n r
    (Dixon.viaDivisor D b fuel, r)

theorem detViaDivisorWith_eq [LawfulDetBound] {A : Matrix Int n n} {r : Rand}
    {fuel : Nat} {d : Int} (h : (detViaDivisorWith A r fuel).1 = some d) : d = det A := by
  unfold detViaDivisorWith at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i D hD
  have heq := Dixon.viaDivisor_eq h
  rwa [decomp?_A hD] at heq

end Hex.Matrix
