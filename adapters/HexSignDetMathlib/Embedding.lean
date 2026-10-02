/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {L : Type w}
variable [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K] [LinearOrder K]
variable [Field L] [DecidableEq L] [LinearOrder L]
variable (f : E → K) (hfz : ∀ a, f a = 0 ↔ a = 0)
variable (g : E → L) (hgz : ∀ a, g a = 0 ↔ a = 0)
variable (ι : K →+* L) (hι : StrictMono ι)
variable (hvalue : ∀ a, g a = ι (f a))

omit [LinearOrder K] [LinearOrder L] in
include hvalue in
/-- Interpreting stored coefficients in an extension maps the original
polynomial coefficient by coefficient. Storage need not be injective. -/
theorem interpret_embedding (p : DensePoly E) :
    interpret g hgz p = (interpret f hfz p).map ι := by
  ext i
  simp only [coeff_interpret, Polynomial.coeff_map, hvalue]

include hι hvalue in
/-- An ordered field embedding preserves every query sign, in its original
position, at the image of a point. -/
theorem signsAt_embedding (qs : List (DensePoly E)) (x : K) :
    signsAt g hgz qs (ι x) = signsAt f hfz qs x := by
  unfold signsAt
  apply List.map_congr_left
  intro q _
  rw [interpret_embedding f hfz g hgz ι hvalue, Polynomial.eval_map_apply,
    hι.sign_comp]

omit [Zero E] [DecidableEq E] [DecidableEq K] [DecidableEq L] in
include hι hvalue in
/-- Finite and infinite interval constraints are preserved under the ordered
embedding. No rational separation of roots is needed. -/
theorem interval_embedding (a b : Endpoint E) (x : K) :
    Tarski.InInterval (a.map g) (b.map g) (ι x) ↔
      Tarski.InInterval (a.map f) (b.map f) x := by
  cases a <;> cases b <;>
    simp [Endpoint.map, Tarski.inInterval_iff, hvalue, hι.lt_iff_lt]

include hι hvalue in
/-- A root of a nonzero interpreted polynomial remains a root in the same
interval after embedding its field. -/
theorem root_mem_embedding (p : DensePoly E)
    (a b : Endpoint E) (x : K)
    (hx : x ∈ Tarski.rootsIn (interpret f hfz p) (a.map f) (b.map f)) :
    ι x ∈ Tarski.rootsIn (interpret g hgz p) (a.map g) (b.map g) := by
  have hp : interpret f hfz p ≠ 0 := by
    intro hzero
    have hmem := (Tarski.mem_rootsIn _ _ _ x).mp hx
    simpa only [hzero, Polynomial.roots_zero, Multiset.notMem_zero] using hmem.1
  have hp' : interpret g hgz p ≠ 0 := by
    rw [interpret_embedding f hfz g hgz ι hvalue]
    exact (Polynomial.map_ne_zero_iff ι.injective).mpr hp
  rw [Tarski.mem_rootsIn_iff _ hp']
  obtain ⟨hroot, hinterval⟩ := (Tarski.mem_rootsIn_iff _ hp _ _ _).mp hx
  refine ⟨?_, (interval_embedding f g ι hι hvalue a b x).mpr hinterval⟩
  rw [interpret_embedding f hfz g hgz ι hvalue, Polynomial.eval_map_apply, hroot,
    map_zero]

variable {Ctx : Type u'} [DecidableEq Ctx]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [IsStrictOrderedRing K] [IsRealClosed K]
variable [IsStrictOrderedRing L] [IsRealClosed L]
variable (hf1 : f 1 = 1) (hfa : ∀ a b, f (a + b) = f a + f b)
variable (hfs : ∀ a b, f (a - b) = f a - f b)
variable (hfm : ∀ a b, f (a * b) = f a * f b)
variable (hfnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hg1 : g 1 = 1) (hga : ∀ a b, g (a + b) = g a + g b)
variable (hgs : ∀ a b, g (a - b) = g a - g b)
variable (hgm : ∀ a b, g (a * b) = g a * g b)
variable (hgnat : ∀ n : Nat, g (n : E) = (n : L))
variable {sign : E → Int}
variable (hfsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (hgsign : ∀ a, sign a = (SignType.sign (g a) : Int))

include hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hι hvalue in
/-- The same validated descriptor selects the image of its original root
under an ordered real-closed-field embedding. Partial encodings, noninjective
coefficient storage and infinite endpoints are included. -/
theorem Descriptor.root_map {context : Ctx} (d : Descriptor E Ctx sign context) :
    d.root g hgz hg1 hga hgs hgm hgnat hgsign =
      ι (d.root f hfz hf1 hfa hfs hfm hfnat hfsign) := by
  obtain ⟨hx, hsigns⟩ := d.root_spec f hfz hf1 hfa hfs hfm hfnat hfsign
  symm
  apply d.root_unique g hgz hg1 hga hgs hgm hgnat hgsign
  · exact root_mem_embedding f hfz g hgz ι hι hvalue _ _ _ _ hx
  · rw [signsAt_embedding f hfz g hgz ι hι hvalue]
    exact hsigns

include hf1 hfa hfs hfm hfnat hfsign hι in
/-- Composing a coefficient interpretation with an ordered field embedding
preserves the selected root. All target interpretation laws are derived from
the source laws and the embedding. -/
theorem Descriptor.root_comp {context : Ctx} (d : Descriptor E Ctx sign context) :
    d.root (fun a => ι (f a))
        (fun a => (map_eq_zero ι).trans (hfz a))
        (by rw [hf1, map_one])
        (fun a b => by rw [hfa, map_add])
        (fun a b => by rw [hfs, map_sub])
        (fun a b => by rw [hfm, map_mul])
        (fun n => by rw [hfnat, map_natCast])
        (fun a => by rw [hι.sign_comp]; exact hfsign a) =
      ι (d.root f hfz hf1 hfa hfs hfm hfnat hfsign) := by
  apply d.root_map f hfz (fun a => ι (f a)) _ ι hι (fun _ => rfl)

end Hex.SignDet
