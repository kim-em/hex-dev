/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Convert
public import HexSignDetTheory.RootProducer
public import HexSignDetTheory.SelectedRoot

public section

namespace Hex.SignDet

open HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {F : Type v} {K : Type w} {Ctx : Type u'} {NewCtx : Type v'}
variable [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hfz : ∀ a, f a = 0 ↔ a = 0)
variable (g : F → K) (hgz : ∀ a, g a = 0 ↔ a = 0)
variable (convert : E → F) (hcz : ∀ a, convert a = 0 ↔ a = 0)
variable (hvalue : ∀ a, g (convert a) = f a)

omit [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue in
/-- Converted coefficients denote the same polynomial; injectivity is not
required on either representation. -/
theorem convert_interpret (p : DensePoly E) :
    interpret g hgz (DensePoly.Interpret.map convert hcz p) = interpret f hfz p := by
  ext i
  simp only [coeff_interpret, DensePoly.Interpret.map_coeff, hvalue]

omit [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]
    [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue in
/-- Both finite and infinite endpoint values survive representation changes. -/
theorem convert_endpoint (a : Endpoint E) : (a.map convert).map g = a.map f := by
  cases a <;> simp [Endpoint.map, hvalue]

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue in
/-- Value-preserving conversion retains squarefreeness and both strict
endpoint guards of the semantic root domain. -/
theorem domain_convert (p : DensePoly E) (a b : Endpoint E) :
    HexSturmTheory.Domain g hgz (DensePoly.Interpret.map convert hcz p)
      (a.map convert) (b.map convert) ↔ HexSturmTheory.Domain f hfz p a b := by
  simp only [HexSturmTheory.Domain, convert_interpret f hfz g hgz convert hcz hvalue]
  cases a <;> cases b <;>
    simp [Endpoint.map, HexSturmTheory.EndpointLt, HexSturmTheory.Nonvanishing, hvalue]

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue in
/-- A coefficient conversion preserving values preserves the exact mathematical
prepared domain, including strict endpoints and endpoint nonvanishing. -/
theorem RawDescriptor.map_domain (context : NewCtx) (raw : RawDescriptor E Ctx) :
    HexSturmTheory.Domain g hgz (raw.map convert hcz context).head
      (raw.map convert hcz context).lower (raw.map convert hcz context).upper ↔
    HexSturmTheory.Domain f hfz raw.head raw.lower raw.upper :=
  domain_convert f hfz g hgz convert hcz hvalue raw.head raw.lower raw.upper

variable [NatCast E] [Mul E] [NatCast F] [Mul F]
variable (hfnat : ∀ n : Nat, f (n : E) = (n : K)) (hfm : ∀ a b, f (a * b) = f a * f b)
variable (hgnat : ∀ n : Nat, g (n : F) = (n : K)) (hgm : ∀ a b, g (a * b) = g a * g b)

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue hfnat hfm hgnat hgm in
/-- The new executable derivative queries have the same signs as the old ones
at every point. They are reconstructed under the target's ordinary operations;
the conversion need not preserve operations as literal representations. -/
theorem RawDescriptor.map_signs (context : NewCtx) (raw : RawDescriptor E Ctx)
    (hw : raw.wellFormed = true) (x : K) :
    signsAt g hgz (raw.map convert hcz context).queries x = signsAt f hfz raw.queries x := by
  have hw' : (raw.map convert hcz context).wellFormed = true :=
    (raw.map_wellFormed convert hcz context).trans hw
  change (raw.map convert hcz context).queries.map _ = raw.queries.map _
  rw [RawDescriptor.querySigns g hgz hgnat hgm _ hw',
    RawDescriptor.querySigns f hfz hfnat hfm _ hw]
  simp only [RawDescriptor.map, convert_interpret f hfz g hgz convert hcz hvalue]

variable [One E] [Add E] [Sub E] [DecidableEq Ctx]
variable [One F] [Add F] [Sub F] [Neg F] [Inv F] [DecidableEq NewCtx]
variable (hf1 : f 1 = 1) (hfa : ∀ a b, f (a + b) = f a + f b)
variable (hfs : ∀ a b, f (a - b) = f a - f b)
variable (hg1 : g 1 = 1) (hga : ∀ a b, g (a + b) = g a + g b)
variable (hgs : ∀ a b, g (a - b) = g a - g b)
variable (hgn : ∀ a, g (-a) = -g a) (hgi : ∀ a, g a⁻¹ = (g a)⁻¹)
variable {sign : E → Int} (hfsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (newSign : F → Int) (hgsign : ∀ a, newSign a = (SignType.sign (g a) : Int))

include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgn hgi hgsign hvalue in
/-- The actual conversion succeeds for value-preserving coefficient maps.
The source's count-one evidence supplies the new unique-root condition;
no general Thom injectivity or isolating-interval theorem is assumed. -/
theorem Descriptor.convert_success {context : Ctx} (newContext : NewCtx)
    (source : Descriptor E Ctx sign context) :
    ∃ target, source.convert convert hcz newSign newContext = .ok (.ok target) := by
  unfold Descriptor.convert
  let raw := source.raw.map convert hcz newContext
  obtain ⟨hw, _, hc, hone⟩ := RawDescriptor.check_eq source.accepted
  have hd := source.evidence.check_domain f hfz hf1 hfa hfs hfm hfnat sign hfsign
    context source.raw.head source.raw.lower source.raw.upper source.raw.queries hc
  have counted := source.evidence.count_roots f hfz hf1 hfa hfs hfm hfnat sign hfsign
    context source.raw.head source.raw.lower source.raw.upper source.raw.queries hc source.raw.signs
  have hcount : ((Tarski.rootsIn (interpret f hfz source.raw.head)
      (source.raw.lower.map f) (source.raw.upper.map f)).filter
      (fun x => signsAt f hfz source.raw.queries x = source.raw.signs)).card = 1 :=
    counted.symm.trans ((source.evidence.table_lookup hc source.raw.signs).symm.trans hone)
  apply (Descriptor.build_success_iff g hgz hg1 hga hgs hgm hgnat hgn hgi newSign hgsign
    newContext raw).mpr
  refine ⟨rfl, (source.raw.map_wellFormed convert hcz newContext).trans hw, ?_, ?_⟩
  · exact (source.raw.map_domain f hfz g hgz convert hcz hvalue newContext).mpr hd
  · dsimp only [raw]
    simp_rw [source.raw.map_signs f hfz g hgz convert hcz hvalue hfnat hfm hgnat hgm newContext hw]
    simpa only [RawDescriptor.map, convert_interpret f hfz g hgz convert hcz hvalue,
      convert_endpoint f g convert hvalue] using hcount

include hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue in
/-- Successful checked conversion preserves the selected mathematical root,
including changes of literal context and noninjective coefficient carriers. -/
theorem Descriptor.convert_root {context : Ctx} (newContext : NewCtx)
    (source : Descriptor E Ctx sign context) (target : Descriptor F NewCtx newSign newContext)
    (h : source.convert convert hcz newSign newContext = .ok (.ok target)) :
    target.root g hgz hg1 hga hgs hgm hgnat hgsign =
      source.root f hfz hf1 hfa hfs hfm hfnat hfsign := by
  unfold Descriptor.convert at h
  have hraw := Descriptor.build_raw h
  have hw := (RawDescriptor.check_eq source.accepted).1
  obtain ⟨hmem, hsigns⟩ := target.root_spec g hgz hg1 hga hgs hgm hgnat hgsign
  rw [hraw] at hmem hsigns
  apply source.root_unique f hfz hf1 hfa hfs hfm hfnat hfsign
  · simpa only [RawDescriptor.map, convert_interpret f hfz g hgz convert hcz hvalue,
      convert_endpoint f g convert hvalue] using hmem
  · rw [source.raw.map_signs f hfz g hgz convert hcz hvalue hfnat hfm hgnat hgm newContext hw] at hsigns
    exact hsigns

end Hex.SignDet
