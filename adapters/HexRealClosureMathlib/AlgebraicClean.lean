/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexPolyMathlib.Interpret
public import HexRealClosure.Algebraic
public section
namespace Hex.RealClosure.Algebraic.Clean
variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
private abbrev Coeff (clean : E → Bool) := {a : E // clean a = true}

omit [One E] [Add E] [Sub E] [Mul E] in
private def lift (clean : E → Bool) [Zero (Coeff clean)]
    (p : DensePoly E) (hp : ∀ i, clean (p.coeff i) = true) : DensePoly (Coeff clean) :=
  DensePoly.ofCoeffs (Array.ofFn (fun i : Fin p.size => ⟨p.coeff i, hp i⟩))

omit [One E] [Add E] [Sub E] [Mul E] in
private theorem map_lift (clean : E → Bool) [Zero (Coeff clean)]
    (hz : ∀ a : Coeff clean, a.val = 0 ↔ a = 0)
    (p : DensePoly E) (hp : ∀ i, clean (p.coeff i) = true) :
    DensePoly.Interpret.map Subtype.val hz (lift clean p hp) = p := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.Interpret.map_coeff]
  simp only [lift, DensePoly.coeff_ofCoeffs]
  by_cases hi : i < p.size
  · simp [Array.getD, hi]
  · simp [Array.getD, hi, DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)]
    exact (hz 0).mpr rfl

omit [One E] [Add E] [Sub E] [Mul E] in
private theorem map_clean (clean : E → Bool) [Zero (Coeff clean)]
    (hz : ∀ a : Coeff clean, a.val = 0 ↔ a = 0) (p : DensePoly (Coeff clean)) :
    ∀ i, clean ((DensePoly.Interpret.map Subtype.val hz p).coeff i) = true := by
  intro i
  rw [DensePoly.Interpret.map_coeff]
  exact (p.coeff i).property

variable (clean : E → Bool) (hz : clean 0 = true) (h1 : clean 1 = true)
variable (ha : ∀ a b, clean a = true → clean b = true → clean (a + b) = true)
variable (hs : ∀ a b, clean a = true → clean b = true → clean (a - b) = true)
variable (hm : ∀ a b, clean a = true → clean b = true → clean (a * b) = true)

omit [One E] [Add E] [Sub E] [Mul E] in
include hz in
/-- The stored-array check also covers omitted zero coefficients. -/
theorem array_iff (p : DensePoly E) : p.toArray.all clean = true ↔
    ∀ i, clean (p.coeff i) = true := by
  constructor
  · intro h i
    by_cases hi : i < p.toArray.size
    · have hc := (Array.all_eq_true.mp h) i hi
      have he : p.toArray[i] = p.coeff i := by
        rw [← DensePoly.toArray_getD p i]
        have hip : i < p.size := by simpa using hi
        simp [Array.getD, hip]
      simpa only [he] using hc
    · have he : p.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le p
        (by simpa using Nat.le_of_not_gt hi)
      rw [he]
      exact hz
  · intro h
    apply Array.all_eq_true.mpr
    intro i hi
    have he : p.toArray[i] = p.coeff i := by
      rw [← DensePoly.toArray_getD p i]
      have hip : i < p.size := by simpa using hi
      simp [Array.getD, hip]
    simpa only [he] using h i

include hz h1 ha hs hm in
/-- Monic division preserves a coefficient predicate closed under its actual
ordinary operations. The clean subtype needs no ring or field laws. -/
theorem remainder (p q : DensePoly E)
    (hp : ∀ i, clean (p.coeff i) = true) (hq : ∀ i, clean (q.coeff i) = true)
    (hmonic : q.Monic) :
    ∀ i, clean ((DensePoly.divModMonic p q hmonic).2.coeff i) = true := by
  let C := {a : E // clean a = true}
  let : Zero C := ⟨⟨0, hz⟩⟩
  let : One C := ⟨⟨1, h1⟩⟩
  let : Add C := ⟨fun a b => ⟨a.val + b.val, ha _ _ a.property b.property⟩⟩
  let : Sub C := ⟨fun a b => ⟨a.val - b.val, hs _ _ a.property b.property⟩⟩
  let : Mul C := ⟨fun a b => ⟨a.val * b.val, hm _ _ a.property b.property⟩⟩
  let f : C → E := Subtype.val
  have hzero : ∀ a : C, f a = 0 ↔ a = 0 := by
    intro a
    constructor
    · intro h; apply Subtype.ext; exact h
    · intro h; rw [h]; rfl
  let lift (r : DensePoly E) (hr : ∀ i, clean (r.coeff i) = true) : DensePoly C :=
    DensePoly.ofCoeffs (Array.ofFn (fun i : Fin r.size => ⟨r.coeff i, hr i⟩))
  have lift_spec (r : DensePoly E) (hr : ∀ i, clean (r.coeff i) = true) :
      DensePoly.Interpret.map f hzero (lift r hr) = r := by
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.Interpret.map_coeff]
    simp only [lift, DensePoly.coeff_ofCoeffs]
    by_cases hi : i < r.size
    · simp [Array.getD, hi, f]
    · simp [Array.getD, hi, f, DensePoly.coeff_eq_zero_of_size_le r (Nat.le_of_not_gt hi)]
      rfl
  let P := lift p hp
  let Q := lift q hq
  have hP : DensePoly.Interpret.map f hzero P = p := lift_spec p hp
  have hQ : DensePoly.Interpret.map f hzero Q = q := lift_spec q hq
  have hQmonic : Q.Monic := by
    apply Subtype.ext
    have hl := DensePoly.Interpret.map_leading f hzero Q
    rw [hQ] at hl
    exact hl.symm.trans hmonic
  have hr := congrArg Prod.snd (DensePoly.Interpret.map_divModMonic f hzero
    (fun _ _ => rfl) (fun _ _ => rfl) rfl P Q hQmonic)
  dsimp only at hr
  simp only [hP, hQ] at hr
  intro i
  rw [← hr, DensePoly.Interpret.map_coeff]
  exact ((DensePoly.divModMonic P Q hQmonic).2.coeff i).property
omit [One E] [Sub E] [Mul E] in
include hz ha in
theorem add (p q : DensePoly E) (hp : ∀ i, clean (p.coeff i) = true)
    (hq : ∀ i, clean (q.coeff i) = true) : ∀ i, clean ((p + q).coeff i) = true := by
  let C := Coeff clean
  let : Zero C := ⟨⟨0, hz⟩⟩
  let : Add C := ⟨fun a b => ⟨a.val + b.val, ha _ _ a.property b.property⟩⟩
  have hzero : ∀ a : C, a.val = 0 ↔ a = 0 := by
    intro a
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let P := lift clean p hp
  let Q := lift clean q hq
  have he : DensePoly.Interpret.map Subtype.val hzero (P + Q) = p + q := by
    rw [DensePoly.Interpret.map_add Subtype.val hzero (fun _ _ => rfl),
      map_lift clean hzero p hp, map_lift clean hzero q hq]
  rw [← he]
  exact map_clean clean hzero (P + Q)

omit [One E] [Add E] [Mul E] in
include hz hs in
theorem sub (p q : DensePoly E) (hp : ∀ i, clean (p.coeff i) = true)
    (hq : ∀ i, clean (q.coeff i) = true) : ∀ i, clean ((p - q).coeff i) = true := by
  let C := Coeff clean
  let : Zero C := ⟨⟨0, hz⟩⟩
  let : Sub C := ⟨fun a b => ⟨a.val - b.val, hs _ _ a.property b.property⟩⟩
  have hzero : ∀ a : C, a.val = 0 ↔ a = 0 := by
    intro a
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let P := lift clean p hp
  let Q := lift clean q hq
  have he : DensePoly.Interpret.map Subtype.val hzero (P - Q) = p - q := by
    rw [DensePoly.Interpret.map_sub Subtype.val hzero (fun _ _ => rfl),
      map_lift clean hzero p hp, map_lift clean hzero q hq]
  rw [← he]
  exact map_clean clean hzero (P - Q)

omit [One E] [Sub E] in
include hz ha hm in
theorem mul (p q : DensePoly E) (hp : ∀ i, clean (p.coeff i) = true)
    (hq : ∀ i, clean (q.coeff i) = true) : ∀ i, clean ((p * q).coeff i) = true := by
  let C := Coeff clean
  let : Zero C := ⟨⟨0, hz⟩⟩
  let : Add C := ⟨fun a b => ⟨a.val + b.val, ha _ _ a.property b.property⟩⟩
  let : Mul C := ⟨fun a b => ⟨a.val * b.val, hm _ _ a.property b.property⟩⟩
  have hzero : ∀ a : C, a.val = 0 ↔ a = 0 := by
    intro a
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  let P := lift clean p hp
  let Q := lift clean q hq
  have he : DensePoly.Interpret.map Subtype.val hzero (P * Q) = p * q := by
    rw [DensePoly.Interpret.map_mul Subtype.val hzero (fun _ _ => rfl) (fun _ _ => rfl),
      map_lift clean hzero p hp, map_lift clean hzero q hq]
  rw [← he]
  exact map_clean clean hzero (P * Q)

end Hex.RealClosure.Algebraic.Clean

namespace Hex.RealClosure.Algebraic
variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable (context : Context E Ctx coeffSign parent)
variable (hz : context.cleanCoeff 0 = true) (h1 : context.cleanCoeff 1 = true)
variable (ha : ∀ a b, context.cleanCoeff a = true → context.cleanCoeff b = true →
  context.cleanCoeff (a + b) = true)
variable (hs : ∀ a b, context.cleanCoeff a = true → context.cleanCoeff b = true →
  context.cleanCoeff (a - b) = true)
variable (hm : ∀ a b, context.cleanCoeff a = true → context.cleanCoeff b = true →
  context.cleanCoeff (a * b) = true)

include hz h1 ha hs hm in
/-- Retained monic remainders preserve the predecessor's recursive storage
predicate whenever it is closed under the operations division performs. -/
theorem Context.reduce_clean (p : DensePoly E) (hp : p.toArray.all context.cleanCoeff = true) :
    (context.reduce p).toArray.all context.cleanCoeff = true := by
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  unfold reduce
  split
  · rename_i hreduce
    have hc := context.reduce_checked.symm.trans hreduce
    have hhead := (Bool.and_eq_true_iff.mp hc).2
    exact Clean.remainder context.cleanCoeff hz h1 ha hs hm p context.root.raw.head
      ((Clean.array_iff context.cleanCoeff hz p).mp hp)
      ((Clean.array_iff context.cleanCoeff hz context.root.raw.head).mp hhead)
      (context.monic_of_reduce hreduce)
  · exact (Clean.array_iff context.cleanCoeff hz p).mp hp

include hz h1 ha hs hm in
/-- Canonical-zero packing and retained reduction both preserve clean inputs. -/
theorem Element.ofPoly_clean (p : DensePoly E) (hp : p.toArray.all context.cleanCoeff = true) :
    (Element.ofPoly (context := context) p).isClean = true := by
  unfold isClean polynomial
  rw [stored_ofPoly]
  by_cases hsign : context.signPoly (context.reduce p) = 0
  · simp only [hsign, ↓reduceDIte]
    apply (Clean.array_iff context.cleanCoeff hz 0).mpr
    intro i
    rw [DensePoly.coeff_zero]
    exact hz
  · simp only [hsign, ↓reduceDIte]
    exact context.reduce_clean hz h1 ha hs hm p hp
namespace Element

include hz in
theorem zero_clean : (0 : Element context).isClean = true := by
  rw [isClean, polynomial_zero]
  apply (Clean.array_iff context.cleanCoeff hz 0).mpr
  intro i
  rw [DensePoly.coeff_zero]
  exact hz

include hz h1 ha hs hm in
theorem ofCoeff_clean (c : E) (hc : context.cleanCoeff c = true) :
    (ofCoeff (context := context) c).isClean = true := by
  rw [ofCoeff]
  apply ofPoly_clean context hz h1 ha hs hm
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  intro i
  rw [DensePoly.coeff_C]
  split
  · exact hc
  · exact hz

include hz h1 ha hs hm in
theorem one_clean : (1 : Element context).isClean = true :=
  ofCoeff_clean context hz h1 ha hs hm 1 h1

include hz h1 ha hs hm in
theorem add_clean (a b : Element context) (hac : a.isClean = true) (hbc : b.isClean = true) :
    (a + b).isClean = true := by
  change (ofPoly (a.polynomial + b.polynomial)).isClean = true
  apply ofPoly_clean context hz h1 ha hs hm
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  exact Clean.add context.cleanCoeff hz ha a.polynomial b.polynomial
    ((Clean.array_iff context.cleanCoeff hz _).mp hac)
    ((Clean.array_iff context.cleanCoeff hz _).mp hbc)

include hz h1 ha hs hm in
theorem sub_clean (a b : Element context) (hac : a.isClean = true) (hbc : b.isClean = true) :
    (a - b).isClean = true := by
  change (ofPoly (a.polynomial - b.polynomial)).isClean = true
  apply ofPoly_clean context hz h1 ha hs hm
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  exact Clean.sub context.cleanCoeff hz hs a.polynomial b.polynomial
    ((Clean.array_iff context.cleanCoeff hz _).mp hac)
    ((Clean.array_iff context.cleanCoeff hz _).mp hbc)

include hz h1 ha hs hm in
theorem mul_clean (a b : Element context) (hac : a.isClean = true) (hbc : b.isClean = true) :
    (a * b).isClean = true := by
  change (ofPoly (a.polynomial * b.polynomial)).isClean = true
  apply ofPoly_clean context hz h1 ha hs hm
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  exact Clean.mul context.cleanCoeff hz ha hm a.polynomial b.polynomial
    ((Clean.array_iff context.cleanCoeff hz _).mp hac)
    ((Clean.array_iff context.cleanCoeff hz _).mp hbc)

include hz h1 ha hs hm in
theorem neg_clean (a : Element context) (hac : a.isClean = true) : (-a).isClean = true := by
  change (ofPoly (0 - a.polynomial)).isClean = true
  apply ofPoly_clean context hz h1 ha hs hm
  apply (Clean.array_iff context.cleanCoeff hz _).mpr
  apply Clean.sub context.cleanCoeff hz hs
  · intro i; rw [DensePoly.coeff_zero]; exact hz
  · exact (Clean.array_iff context.cleanCoeff hz _).mp hac

end Element

/-- info: 'Hex.RealClosure.Algebraic.Context.reduce_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Context.reduce_clean
/-- info: 'Hex.RealClosure.Algebraic.Element.mul_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.mul_clean
end Hex.RealClosure.Algebraic
