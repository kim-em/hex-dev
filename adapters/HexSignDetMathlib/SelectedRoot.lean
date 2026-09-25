/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor
public import HexSignDetMathlib.RootModel

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hsign in
/-- Count-one replay identifies exactly one root satisfying all selected
formal-derivative signs jointly, for partial as well as full encodings. -/
theorem Descriptor.existsUnique_root (context : Ctx) (d : Descriptor E Ctx sign context) :
    ∃! x, x ∈ Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f) ∧
      signsAt f hz d.raw.queries x = d.raw.signs := by
  have accepted := d.accepted
  simp only [RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have counted := d.evidence.count_roots f hz h1 ha hs hm hnat sign hsign context
    d.raw.head d.raw.lower d.raw.upper d.raw.queries accepted.1.2 d.raw.signs
  have hone : ((Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs)).card = 1 :=
    counted.symm.trans accepted.2
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
  have mem : x ∈ (Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs) := by
    rw [hx]
    exact Finset.mem_singleton_self x
  refine ⟨x, Finset.mem_filter.mp mem, ?_⟩
  intro y hy
  have member : y ∈ (Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
      (fun x => signsAt f hz d.raw.queries x = d.raw.signs) := Finset.mem_filter.mpr hy
  rw [hx] at member
  exact Finset.mem_singleton.mp member

/-- The mathematical root identified by an accepted descriptor. -/
noncomputable def Descriptor.root (context : Ctx) (d : Descriptor E Ctx sign context) : K :=
  Classical.choose (d.existsUnique_root f hz h1 ha hs hm hnat sign hsign context)

/-- The selected root lies in the descriptor's interval and satisfies all
of its derivative signs at that same point. -/
theorem Descriptor.root_spec (context : Ctx) (d : Descriptor E Ctx sign context) :
    d.root f hz h1 ha hs hm hnat sign hsign context ∈
        Tarski.rootsIn (interpret f hz d.raw.head) (d.raw.lower.map f) (d.raw.upper.map f) ∧
      signsAt f hz d.raw.queries (d.root f hz h1 ha hs hm hnat sign hsign context) = d.raw.signs := by
  exact (Classical.choose_spec (d.existsUnique_root f hz h1 ha hs hm hnat sign hsign context)).1

/-- Any root with the checked encoding denotes the same selected value. -/
theorem Descriptor.root_unique (context : Ctx) (d : Descriptor E Ctx sign context) (x : K)
    (hx : x ∈ Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f))
    (hxs : signsAt f hz d.raw.queries x = d.raw.signs) :
    x = d.root f hz h1 ha hs hm hnat sign hsign context := by
  exact (Classical.choose_spec (d.existsUnique_root f hz h1 ha hs hm hnat sign hsign context)).2 x ⟨hx, hxs⟩

end Hex.SignDet
