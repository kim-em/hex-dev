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
public import HexBareiss.Bareiss

public section

/-! Bounded CRT reconstruction and the total modular/Bareiss dispatcher. -/

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

namespace Hex.ModularMatrix

/-- Determinant methods recorded by the dispatcher. The divisor method is
reserved for the Dixon/divisor extension. -/
inductive Method where
  | modular | divisor | bareiss
  deriving Repr, BEq, DecidableEq

/-- A determinant value and the methods attempted in order. The final method
in `first :: rest` supplies the value. -/
structure DetData where
  value : Int
  first : Method
  rest : List Method
  deriving Repr, BEq, DecidableEq

/-- Try bounded modular reconstruction, then use Bareiss on exhaustion. -/
def detWith (A : Matrix Int n n) (fuel : Nat) : DetData :=
  match A.detModular? fuel with
  | some d => ⟨d, .modular, []⟩
  | none => ⟨A.bareiss, .modular, [.bareiss]⟩

/-- The default budget allows roughly one 30-bit image per bound word, with
two spare images and a cap of 16384. Exhaustion always dispatches to Bareiss. -/
def defaultFuel (A : Matrix Int n n) : Nat :=
  min 16384 (A.hadamardBound.log2 / 30 + 2)

/-- The total integer determinant, with Bareiss as the finite-supply fallback. -/
@[expose]
def det (A : Matrix Int n n) : Int := (detWith A (defaultFuel A)).value

/-- A successful modular reconstruction records only the modular method. -/
theorem detWith_modular {A : Matrix Int n n} {fuel : Nat} {d : Int}
    (h : A.detModular? fuel = some d) : detWith A fuel = ⟨d, .modular, []⟩ := by
  simp [detWith, h]

/-- Exhaustion records the Bareiss fallback after the modular attempt. -/
theorem detWith_bareiss {A : Matrix Int n n} {fuel : Nat}
    (h : A.detModular? fuel = none) :
    detWith A fuel = ⟨A.bareiss, .modular, [.bareiss]⟩ := by
  simp [detWith, h]

/-- Correctness of the successful modular route in the Mathlib-free layer. -/
theorem detWith_modular_eq [Matrix.LawfulDetBound] {A : Matrix Int n n}
    {fuel : Nat} {d : Int} (h : A.detModular? fuel = some d) :
    (detWith A fuel).value = A.det := by
  rw [detWith_modular h]
  exact Matrix.detModular?_eq h

end Hex.ModularMatrix
