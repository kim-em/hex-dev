/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Image
public import HexModularMatrix.Bound
public import HexModArith.Modulus
public import HexModular.Loop

public section

/-! Bounded CRT reconstruction of integer determinants. -/

namespace Hex.Matrix

namespace DetImage

/-- Reduce an integer matrix at a usable word modulus and produce one CRT coordinate. -/
def image (A : Matrix Int n n) (m : Nat) : Option (Vector Int 1) :=
  if h : 0 < m ∧ m < 2 ^ 31 then
    letI : ZMod64.Bounds m := ⟨h.1, h.2⟩
    (detMod? (A.mapEntries (ZMod64.intCast m))).map fun d =>
      Vector.replicate 1 (d.toNat : Int)
  else none

/-- Every produced image is a residue of the integer determinant. -/
theorem image_eq {A : Matrix Int n n} {m : Nat} {r : Vector Int 1}
    (h : image A m = some r) (i : Fin 1) :
    r[i] % (m : Int) = det A % (m : Int) := by
  unfold image at h
  split at h
  · rename_i hm
    letI : ZMod64.Bounds m := ⟨hm.1, hm.2⟩
    obtain ⟨d, hd, hr⟩ := Option.map_eq_some_iff.mp h
    rw [← hr]
    simpa only [Fin.getElem_fin, Vector.getElem_replicate] using (detMod?_reduce A hd).symm
  · contradiction

end DetImage

/-- The accumulated CRT state at the strict determinant bound. Its modulus
is available to conformance and benchmark clients inspecting reconstruction. -/
def detCrt? (A : Matrix Int n n) (bound fuel : Nat) : Option (Modular.CrtVec 1) :=
  Modular.crtLoop (DetImage.image A)
    (fun state => if 2 * bound < state.modulus then some state else none)
    ((ZMod64.primesBelow (2 ^ 31 - 1) fuel).map fun p => p.m) fuel

/-- Reconstruct the determinant once the accumulated modulus exceeds twice
the caller's bound, or return `none` on exhaustion. -/
def detBounded? (A : Matrix Int n n) (bound fuel : Nat) : Option Int :=
  (detCrt? A bound fuel).map fun state => state.value[0]

/-- Multi-modular reconstruction at the Hadamard bound. -/
def detModular? (A : Matrix Int n n) (fuel : Nat) : Option Int :=
  detBounded? A (hadamardBound A) fuel

/-- A successful bounded reconstruction is correct under the caller's bound. -/
theorem detBounded?_eq {A : Matrix Int n n} {bound fuel : Nat} {d : Int}
    (hB : (det A).natAbs ≤ bound) (h : detBounded? A bound fuel = some d) :
    d = det A := by
  obtain ⟨result, hresult, hd⟩ := Option.map_eq_some_iff.mp h
  unfold detCrt? at hresult
  obtain ⟨consumed, state, _, _, _, trace, haccept⟩ := Modular.crtLoop_trace hresult
  split at haccept
  · rename_i hbound
    cases haccept
    rw [← hd]
    apply result.eq_of_congr (0 : Fin 1) (by omega)
    have hc := trace.congr (Vector.replicate 1 (det A)) (by
      intro j hj _ r hr i
      simpa only [Fin.getElem_fin, Vector.getElem_replicate] using DetImage.image_eq hr i)
    simpa only [Fin.getElem_fin, Vector.getElem_replicate] using hc (0 : Fin 1)
  · contradiction

/-- Successful reconstruction at the Hadamard bound is correct whenever that
bound satisfies Hadamard's determinant inequality. -/
theorem detModular?_eq [LawfulDetBound] {A : Matrix Int n n} {fuel : Nat} {d : Int}
    (h : detModular? A fuel = some d) : d = det A :=
  detBounded?_eq (LawfulDetBound.natAbs_det_le A) h

/-- The row-norm route requires no bound instance. -/
theorem detBounded?_rowNorm {A : Matrix Int n n} {fuel : Nat} {d : Int}
    (h : detBounded? A (rowNormBound A) fuel = some d) : d = det A :=
  detBounded?_eq (natAbs_det_le_rowNormBound A) h

end Hex.Matrix
