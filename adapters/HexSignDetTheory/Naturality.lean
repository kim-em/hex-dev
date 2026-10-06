/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Convert
public import HexSignDetTheory.RootProducer
public import HexSignDetTheory.SelectedRoot
public import HexSignDetTheory.SelectedProducer
public import HexSignDetTheory.ComparisonProducer
public import HexSignDetTheory.TableProducer
public import HexSignDetTheory.ThomRoots

/-! Preservation of public results under checked coefficient and context conversion.
Literal certificate data is checked again; the conclusions concern the actual
computed signs, comparisons and complete root counts. -/

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

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include hvalue in
/-- Converted queries have the same ordered evaluation signs at every point. -/
theorem signsAt_convert (qs : List (DensePoly E)) (x : K) :
    signsAt g hgz (qs.map (DensePoly.Interpret.map convert hcz)) x =
      signsAt f hfz qs x := by
  unfold signsAt
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  change (SignType.sign ((interpret g hgz (DensePoly.Interpret.map convert hcz q)).eval x) : Int) =
    (SignType.sign ((interpret f hfz q).eval x) : Int)
  rw [convert_interpret f hfz g hgz convert hcz hvalue]

variable [NatCast E] [Mul E] [NatCast F] [Mul F]
variable (hfnat : ∀ n : Nat, f (n : E) = (n : K)) (hfm : ∀ a b, f (a * b) = f a * f b)
variable (hgnat : ∀ n : Nat, g (n : F) = (n : K)) (hgm : ∀ a b, g (a * b) = g a * g b)

variable [One E] [Add E] [Sub E] [DecidableEq Ctx]
variable [One F] [Add F] [Sub F] [Neg F] [Inv F] [DecidableEq NewCtx]
variable (hf1 : f 1 = 1) (hfa : ∀ a b, f (a + b) = f a + f b)
variable (hfs : ∀ a b, f (a - b) = f a - f b)
variable (hg1 : g 1 = 1) (hga : ∀ a b, g (a + b) = g a + g b)
variable (hgs : ∀ a b, g (a - b) = g a - g b)
variable (hgn : ∀ a, g (-a) = -g a) (hgi : ∀ a, g a⁻¹ = (g a)⁻¹)
variable {sign : E → Int} (hfsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (newSign : F → Int) (hgsign : ∀ a, newSign a = (SignType.sign (g a) : Int))

variable [Neg E] [Inv E]
variable (hfn : ∀ a, f (-a) = -f a) (hfi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue hfn hfi hgn hgi in
/-- The total selected-root sign is unchanged after successful checked
conversion, even when the new context and coefficient types differ. -/
theorem Descriptor.convert_signAt {context : Ctx} (newContext : NewCtx)
    (source : Descriptor E Ctx sign context) (target : Descriptor F NewCtx newSign newContext)
    (checked : source.convert convert hcz newSign newContext = .ok (.ok target))
    (q : DensePoly E) :
    target.signAt (DensePoly.Interpret.map convert hcz q) = source.signAt q := by
  have same := source.convert_root (f := f) (hfz := hfz) (g := g) (hgz := hgz)
    (convert := convert) (hcz := hcz) (hvalue := hvalue)
    (hfnat := hfnat) (hfm := hfm) (hgnat := hgnat) (hgm := hgm)
    (hf1 := hf1) (hfa := hfa) (hfs := hfs) (hfsign := hfsign)
    (hg1 := hg1) (hga := hga) (hgs := hgs) (hgsign := hgsign) (newSign := newSign) newContext target checked
  rw [target.signAt_correct g hgz hg1 hga hgs hgm hgnat hgsign hgn hgi,
    source.signAt_correct f hfz hf1 hfa hfs hfm hfnat hfsign hfn hfi,
    convert_interpret f hfz g hgz convert hcz hvalue, same]

variable [Div E] [Div F]
variable (hfd : ∀ a b, f (a / b) = f a / f b)
variable (hgd : ∀ a b, g (a / b) = g a / g b)

include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue
    hfn hfi hgn hgi hfd hgd in
/-- Successful conversion of both selected roots preserves all three results
of the actual total comparison, including different defining polynomials. -/
theorem Descriptor.convert_compare {context : Ctx} (newContext : NewCtx)
    (left right : Descriptor E Ctx sign context)
    (left' right' : Descriptor F NewCtx newSign newContext)
    (hl : left.convert convert hcz newSign newContext = .ok (.ok left'))
    (hr : right.convert convert hcz newSign newContext = .ok (.ok right')) :
    left'.compare right' = left.compare right := by
  have sameLeft := left.convert_root (f := f) (hfz := hfz) (g := g) (hgz := hgz)
    (convert := convert) (hcz := hcz) (hvalue := hvalue)
    (hfnat := hfnat) (hfm := hfm) (hgnat := hgnat) (hgm := hgm)
    (hf1 := hf1) (hfa := hfa) (hfs := hfs) (hfsign := hfsign)
    (hg1 := hg1) (hga := hga) (hgs := hgs) (hgsign := hgsign) (newSign := newSign) newContext left' hl
  have sameRight := right.convert_root (f := f) (hfz := hfz) (g := g) (hgz := hgz)
    (convert := convert) (hcz := hcz) (hvalue := hvalue)
    (hfnat := hfnat) (hfm := hfm) (hgnat := hgnat) (hgm := hgm)
    (hf1 := hf1) (hfa := hfa) (hfs := hfs) (hfsign := hfsign)
    (hg1 := hg1) (hga := hga) (hgs := hgs) (hgsign := hgsign) (newSign := newSign) newContext right' hr
  rw [left'.compare_correct g hgz hg1 hga hgs hgm hgnat hgsign hgn hgi hgd right',
    left.compare_correct f hfz hf1 hfa hfs hfm hfnat hfsign hfn hfi hfd right,
    sameLeft, sameRight]

omit [Div E] [Div F] in
include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue
    hfn hfi hgn hgi in
/-- Every count in an actual returned table is unchanged under a
value-preserving coefficient conversion. The integer sign word retains its
original order, and omitted words still have count zero. -/
theorem determine_convert_counts (context : Ctx) (newContext : NewCtx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (reduced : Bool)
    (table : SignTable qs.length)
    (table' : SignTable (qs.map (DensePoly.Interpret.map convert hcz)).length)
    (hs : determine sign context p a b qs reduced = some table)
    (ht : determine newSign newContext (DensePoly.Interpret.map convert hcz p)
      (a.map convert) (b.map convert) (qs.map (DensePoly.Interpret.map convert hcz)) reduced =
        some table') (word : List Int) : table'.count word = table.count word := by
  have sourceCounts := (determine_correct f hfz hf1 hfa hfs hfm hfnat hfn hfi
    sign hfsign context p a b qs reduced table hs).2 word
  have targetCounts := (determine_correct g hgz hg1 hga hgs hgm hgnat hgn hgi
    newSign hgsign newContext (DensePoly.Interpret.map convert hcz p)
    (a.map convert) (b.map convert) (qs.map (DensePoly.Interpret.map convert hcz))
    reduced table' ht).2 word
  rw [targetCounts, sourceCounts]
  simp only [convert_interpret f hfz g hgz convert hcz hvalue,
    convert_endpoint f g convert hvalue, signsAt_convert f hfz g hgz convert hcz hvalue]

omit [Div E] [Div F] in
include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue
    hfn hfi hgn hgi in
/-- The actual option-valued table API succeeds on precisely the same domains
after coefficient and literal context conversion. -/
theorem determine_convert_isSome (context : Ctx) (newContext : NewCtx)
    (p : DensePoly E) (a b : Endpoint E) (qs : List (DensePoly E)) (reduced : Bool) :
    (determine newSign newContext (DensePoly.Interpret.map convert hcz p)
      (a.map convert) (b.map convert) (qs.map (DensePoly.Interpret.map convert hcz))
      reduced).isSome = true ↔
    (determine sign context p a b qs reduced).isSome = true := by
  rw [determine_isSome g hgz hg1 hga hgs hgm hgnat hgn hgi newSign hgsign,
    determine_isSome f hfz hf1 hfa hfs hfm hfnat hfn hfi sign hfsign]
  exact domain_convert f hfz g hgz convert hcz hvalue p a b

omit [Div E] [Div F] in
include hfz hgz hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue
    hfn hfi hgn hgi in
/-- Actual root-list success is preserved by value-preserving coefficient
and context conversion, including domains with no roots. -/
theorem Descriptor.buildRoots_convert_isSome (context : Ctx) (newContext : NewCtx)
    (p : DensePoly E) (a b : Endpoint E) :
    (∃ out, Descriptor.buildRoots newSign newContext (DensePoly.Interpret.map convert hcz p)
      (a.map convert) (b.map convert) = .ok (some out)) ↔
    (∃ out, Descriptor.buildRoots sign context p a b = .ok (some out)) := by
  rw [Descriptor.buildRoots_isSome g hgz hg1 hga hgs hgm hgnat hgsign hgn hgi,
    Descriptor.buildRoots_isSome f hfz hf1 hfa hfs hfm hfnat hfsign hfn hfi]
  exact domain_convert f hfz g hgz convert hcz hvalue p a b

omit [Div E] [Div F] in
include hf1 hfa hfs hfm hfnat hfsign hg1 hga hgs hgm hgnat hgsign hvalue in
/-- The actual root enumeration returns the same ordered mathematical roots
after value-preserving coefficient conversion. This compares returned lists,
including empty ones, rather than separately enumerating abstract roots. -/
theorem Descriptor.buildRoots_convert_roots (context : Ctx) (newContext : NewCtx)
    (p : DensePoly E) (a b : Endpoint E)
    (out : List (Descriptor E Ctx sign context))
    (out' : List (Descriptor F NewCtx newSign newContext))
    (hs : Descriptor.buildRoots sign context p a b = .ok (some out))
    (ht : Descriptor.buildRoots newSign newContext (DensePoly.Interpret.map convert hcz p)
      (a.map convert) (b.map convert) = .ok (some out')) :
    out'.map (fun d => d.root g hgz hg1 hga hgs hgm hgnat hgsign) =
      out.map (fun d => d.root f hfz hf1 hfa hfs hfm hfnat hfsign) := by
  have sourceRoots := Descriptor.buildRoots_coverage f hfz hf1 hfa hfs hfm hfnat hfsign hs
  have targetRoots := Descriptor.buildRoots_coverage g hgz hg1 hga hgs hgm hgnat hgsign ht
  apply (Descriptor.buildRoots_ordered g hgz hg1 hga hgs hgm hgnat hgsign ht).eq_of_mem_iff
    (Descriptor.buildRoots_ordered f hfz hf1 hfa hfs hfm hfnat hfsign hs)
  intro x
  rw [← targetRoots.1 x, ← sourceRoots.1 x,
    convert_interpret f hfz g hgz convert hcz hvalue,
    convert_endpoint f g convert hvalue, convert_endpoint f g convert hvalue]

end Hex.SignDet
