/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Algebraic
public import HexRealClosureTheory.TransportSelected

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hn hi in
/-- The actual algebraic-level arithmetic supplies the closed coefficient
interpretation used by finite query transport. Membership is universal here
because every stored value has a selected-root interpretation. -/
theorem Context.closed (context : Context E Ctx coeffSign parent) :
    Transport.Closed
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      (fun _ => True) := by
  refine {
    zero := trivial
    add := by intros; trivial
    mul := by intros; trivial
    sub := by intros; trivial
    one := trivial
    natCast := by intros; trivial
    read_zero := ?_
    read_add := ?_
    read_mul := ?_
    read_sub := ?_
    read_one := ?_
    read_natCast := ?_ }
  · exact Element.denote_zero f hz h1 ha hs hm hnat hsign
  · intro a b _ _
    exact Element.denote_add f hz h1 ha hs hm hnat hsign hn hi a b
  · intro a b _ _
    exact Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi a b
  · intro a b _ _
    exact Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi a b
  · exact Element.denote_one f hz h1 ha hs hm hnat hsign hn hi
  · intro n
    exact Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi n

include hn hi in
/-- Canonical source zero makes every stored polynomial's top coefficient
nonzero after interpretation, as required by the finite checker transport. -/
theorem Context.leading (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) :
    Transport.Leading
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign) p := by
  intro hsize hzero
  have hsource := (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi
    (p.coeff (p.size - 1))).mp hzero
  have hlead := DensePoly.leadingCoeff_ne_zero_of_pos_size p hsize
  rw [DensePoly.leadingCoeff_eq_coeff_last p hsize] at hlead
  exact hlead hsource

include hn hi in
/-- Source signs agree with the sign of their actual selected values. -/
theorem Element.readSign {context : Context E Ctx coeffSign parent}
    (a : Element context) :
    (SignType.sign (a.denote f hz h1 ha hs hm hnat hsign) : Int) = a.sign :=
  (a.sign_spec f hz h1 ha hs hm hnat hsign hn hi).symm

include hn hi in
/-- Every scale in an actual signed-remainder chain has the required target
sign, including terminal scales. -/
theorem Context.chainSigns (context : Context E Ctx coeffSign parent)
    (cert : Hex.SignedRemainderChain (Element context)) :
    Transport.ChainSigns
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int)) cert := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _
  · exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _
  · intro i bound
    exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _
  · intro i bound
    exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _
  · intro scale q hterminal
    exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi scale

/-- All literal chain scalars and coefficients are in the total algebraic
value domain. -/
theorem Context.chainDomain (context : Context E Ctx coeffSign parent)
    (cert : Hex.SignedRemainderChain (Element context)) :
    Transport.ChainDomain (fun _ : Element context => True) cert := by
  constructor <;> intros <;> trivial

/-- Every endpoint belongs to the total algebraic value domain. -/
theorem Context.endpointDomain (context : Context E Ctx coeffSign parent)
    (e : Hex.Endpoint (Element context)) :
    Transport.EndpointDomain (fun _ : Element context => True) e := by
  cases e <;> trivial

include hn hi in
/-- Finite endpoint evaluations and infinite leading coefficients retain
their actual selected signs. -/
theorem Context.endpointSigns (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (e : Hex.Endpoint (Element context)) :
    Transport.EndpointAgreement
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int)) p e := by
  cases e <;> exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _

include hn hi in
/-- Every literal Tarski certificate over an algebraic level carries the
finite interpretation facts needed to replay it over the selected ambient
values. The certificate's own validity remains a separate checker premise. -/
theorem Context.queryData {D : Type z}
    (context : Context E Ctx coeffSign parent)
    (p q : DensePoly (Element context))
    (a b : Hex.Endpoint (Element context))
    (cert : Hex.TarskiCertificate (Element context) (Element context) D) :
    Transport.QueryData
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int)) p q a b cert := by
  apply Transport.QueryData.of_closed
    (read := fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (S := fun _ => True)
    (data := context.closed f hz h1 ha hs hm hnat hsign hn hi)
    (sourceSign := Element.sign)
    (targetSign := fun x : K => (SignType.sign x : Int))
  · intro i bound; trivial
  · intro i bound; trivial
  · exact context.chainDomain cert.squarefree
  · exact context.chainDomain cert.remainders
  · exact context.leading f hz h1 ha hs hm hnat hsign hn hi p
  · intro r member
    exact context.leading f hz h1 ha hs hm hnat hsign hn hi r
  · intro r member
    exact context.leading f hz h1 ha hs hm hnat hsign hn hi r
  · exact context.chainSigns f hz h1 ha hs hm hnat hsign hn hi cert.squarefree
  · exact context.chainSigns f hz h1 ha hs hm hnat hsign hn hi cert.remainders
  · exact context.endpointDomain a
  · exact context.endpointDomain b
  · intro x y _ _
    exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi (x - y)
  · exact context.endpointSigns f hz h1 ha hs hm hnat hsign hn hi p a
  · exact context.endpointSigns f hz h1 ha hs hm hnat hsign hn hi p b
  · intro r member
    exact context.endpointSigns f hz h1 ha hs hm hnat hsign hn hi r a
  · intro r member
    exact context.endpointSigns f hz h1 ha hs hm hnat hsign hn hi r b


/-- Every stored reduction step has a total coefficient interpretation. -/
theorem Context.reductionDomain (context : Context E Ctx coeffSign parent)
    (s : Hex.SignDet.ReductionStep (Element context)) :
    Transport.ReductionDomain (fun _ : Element context => True) s := by
  constructor <;> intros <;> trivial

include hn hi in
/-- The two literal reduction scales retain their selected signs. -/
theorem Context.reductionSigns (context : Context E Ctx coeffSign parent)
    (s : Hex.SignDet.ReductionStep (Element context)) :
    Transport.ReductionSigns
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int)) s := by
  constructor <;> exact Element.readSign f hz h1 ha hs hm hnat hsign hn hi _

include hn hi in
/-- Actual algebraic values interpret every query preprocessing witness. -/
theorem Context.preparationData (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (qs : List (DensePoly (Element context)))
    (ss : List (Hex.SignDet.ReductionStep (Element context))) :
    Transport.PreparationData
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int)) p qs ss := by
  apply Transport.PreparationData.of_closed
    (S := fun _ => True)
    (data := context.closed f hz h1 ha hs hm hnat hsign hn hi)
  · exact context.leading f hz h1 ha hs hm hnat hsign hn hi p
  · intros; trivial
  · intros; trivial
  · intro s _; exact context.reductionDomain s
  · intro s _; exact context.reductionSigns f hz h1 ha hs hm hnat hsign hn hi s

include hn hi in
/-- Every literal repeated-factor reduction has an interpreted witness. -/
theorem Context.reductionData (context : Context E Ctx coeffSign parent)
    (p prev : DensePoly (Element context))
    (fs : List (Nat × DensePoly (Element context)))
    (ss : List (Hex.SignDet.ReductionStep (Element context)))
    (result : DensePoly (Element context)) :
    Transport.ReductionData
      (fun a : Element context => a.denote f hz h1 ha hs hm hnat hsign)
      Element.sign (fun x : K => (SignType.sign x : Int))
      p prev fs ss result := by
  apply Transport.ReductionData.of_closed
    (S := fun _ => True)
    (data := context.closed f hz h1 ha hs hm hnat hsign hn hi)
  · exact context.leading f hz h1 ha hs hm hnat hsign hn hi p
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro s _; exact context.reductionDomain s
  · intro s _; exact context.reductionSigns f hz h1 ha hs hm hnat hsign hn hi s
  · intros; trivial

include hn hi in
/-- A native node over actual algebraic values carries all finite replay
interpretation facts for its original coefficient positions. -/
theorem Context.nodeData {NextCtx : Type z} [DecidableEq NextCtx]
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context))
    (a b : Hex.Endpoint (Element context))
    (qs : List (DensePoly (Element context)))
    (n : Hex.SignDet.Node (Element context) NextCtx) :
    Transport.NodeData
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (fun _ => True)
      Element.sign (fun x : K => (SignType.sign x : Int)) p a b qs n := by
  refine ⟨context.leading f hz h1 ha hs hm hnat hsign hn hi p, ?_, ?_, ?_, ?_⟩
  · intros; trivial
  · intro r _
    exact context.preparationData f hz h1 ha hs hm hnat hsign hn hi p qs r.steps
  · intro i r _
    exact context.reductionData f hz h1 ha hs hm hnat hsign hn hi p 1
      (Hex.SignDet.factors (Hex.SignDet.QueryReduction.operands qs n.preparation)
        n.system.rows[i]) r.steps r.result
  · intro i
    exact context.queryData f hz h1 ha hs hm hnat hsign hn hi p
      (Hex.SignDet.queryPoly (Hex.SignDet.QueryReduction.operands qs n.preparation)
        n.system.rows[i] n.reductions[i]) a b n.moments[i]

include hn hi in
/-- Every node of an actual algebraic replay retains its finite interpretation
data, including the positional query slices at recursive edges. -/
theorem Context.replayData {NextCtx : Type z} [DecidableEq NextCtx]
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (DensePoly (Element context)))
    (t : Hex.SignDet.Replay (Element context) NextCtx) :
    Transport.ReplayData
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (fun _ => True)
      Element.sign (fun x : K => (SignType.sign x : Int)) p a b qs t := by
  induction t generalizing qs with
  | leaf n => exact context.nodeData f hz h1 ha hs hm hnat hsign hn hi p a b qs n
  | split n l r ihl ihr =>
    exact ⟨context.nodeData f hz h1 ha hs hm hnat hsign hn hi p a b qs n,
      ihl (qs.take (qs.length / 2)), ihr (qs.drop (qs.length / 2))⟩

include hn hi in
/-- An accepted native replay over one algebraic tower level counts the
ambient roots realizing each exact sign condition. -/
theorem Context.count_roots {NextCtx : Type z} [DecidableEq NextCtx]
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (DensePoly (Element context)))
    (t : Hex.SignDet.Replay (Element context) NextCtx) (certificateContext : NextCtx)
    (accepted : t.check Element.sign certificateContext p a b qs = true)
    (condition : List Int) :
    (t.table accepted).count condition =
      (Transport.roots
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        p a b qs condition).card := by
  exact Transport.count_roots
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (fun _ => True)
    (context.closed f hz h1 ha hs hm hnat hsign hn hi)
    Element.sign certificateContext p a b qs t
    (context.replayData f hz h1 ha hs hm hnat hsign hn hi p a b qs t)
    accepted condition


include hn hi in
/-- A positive native count supplies a simultaneous ambient realization. -/
theorem Context.exists_root {NextCtx : Type z} [DecidableEq NextCtx]
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (DensePoly (Element context)))
    (t : Hex.SignDet.Replay (Element context) NextCtx) (certificateContext : NextCtx)
    (accepted : t.check Element.sign certificateContext p a b qs = true)
    (condition : List Int) (positive : 0 < (t.table accepted).count condition) :
    ∃ x, x ∈ Transport.roots
      (fun y : Element context => y.denote f hz h1 ha hs hm hnat hsign)
      p a b qs condition := by
  exact Transport.exists_root
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (fun _ => True)
    (context.closed f hz h1 ha hs hm hnat hsign hn hi)
    Element.sign certificateContext p a b qs t
    (context.replayData f hz h1 ha hs hm hnat hsign hn hi p a b qs t)
    accepted condition positive

include hn hi in
/-- A native count of one selects exactly one ambient root with the full sign
condition, including the condition's original query order. -/
theorem Context.unique_root {NextCtx : Type z} [DecidableEq NextCtx]
    (context : Context E Ctx coeffSign parent)
    (p : DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (DensePoly (Element context)))
    (t : Hex.SignDet.Replay (Element context) NextCtx) (certificateContext : NextCtx)
    (accepted : t.check Element.sign certificateContext p a b qs = true)
    (condition : List Int) (one : (t.table accepted).count condition = 1) :
    ∃! x, x ∈ Transport.roots
      (fun y : Element context => y.denote f hz h1 ha hs hm hnat hsign)
      p a b qs condition := by
  exact Transport.unique_root
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (fun _ => True)
    (context.closed f hz h1 ha hs hm hnat hsign hn hi)
    Element.sign certificateContext p a b qs t
    (context.replayData f hz h1 ha hs hm hnat hsign hn hi p a b qs t)
    accepted condition one


include hn hi in
/-- The actual next-level descriptor needs no separately supplied finite
interpretation package: its accepted replay and the current level's semantic
operation proofs provide one. -/
theorem Context.descriptorData {NextCtx : Type z} [DecidableEq NextCtx]
    {key : NextCtx} (context : Context E Ctx coeffSign parent)
    (d : Hex.SignDet.Descriptor (Element context) NextCtx Element.sign key) :
    Transport.DescriptorData
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (fun _ => True)
      Element.sign (fun x : K => (SignType.sign x : Int)) d.raw d.evidence := by
  refine ⟨?_, context.leading f hz h1 ha hs hm hnat hsign hn hi d.raw.head, ?_⟩
  · intros; trivial
  · exact context.replayData f hz h1 ha hs hm hnat hsign hn hi
      d.raw.head d.raw.lower d.raw.upper d.raw.queries d.evidence


/-- Recheck the same literal next-level replay over the ambient field, using
the current level's selected-value interpretation. -/
noncomputable def Context.interpretDescriptor {NextCtx : Type z} [DecidableEq NextCtx]
    {key : NextCtx} (context : Context E Ctx coeffSign parent)
    (d : Hex.SignDet.Descriptor (Element context) NextCtx Element.sign key) :
    Hex.SignDet.Descriptor K NextCtx (fun x : K => (SignType.sign x : Int)) key :=
  Transport.checkedDescriptor
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (fun _ => True)
    (context.closed f hz h1 ha hs hm hnat hsign hn hi)
    (fun x : NextCtx => x)
    Element.sign (fun x : K => (SignType.sign x : Int)) key d
    (context.descriptorData f hz h1 ha hs hm hnat hsign hn hi d)


include hn hi in
/-- The root used by the next algebraic level realizes every additional query
sign in the ambient field, in the exact query order. -/
theorem Context.selectedSigns {NextCtx : Type z} [DecidableEq NextCtx]
    {key : NextCtx} (context : Context E Ctx coeffSign parent)
    (d : Hex.SignDet.Descriptor (Element context) NextCtx Element.sign key)
    (qs : List (DensePoly (Element context)))
    (s : Hex.SignDet.SelectedSigns d qs) :
    Hex.SignDet.signsAt
      (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
      (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
      qs
      (d.root
        (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
        (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
        (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
        (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi)) =
      s.values.toList := by
  exact (s.values_at_root
    (fun x : Element context => x.denote f hz h1 ha hs hm hnat hsign)
    (Element.denote_eq_zero f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_one f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_add f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_sub f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_mul f hz h1 ha hs hm hnat hsign hn hi)
    (Element.denote_nat f hz h1 ha hs hm hnat hsign hn hi)
    (Element.sign_spec f hz h1 ha hs hm hnat hsign hn hi)).symm

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.closed
/-- info: 'Hex.RealClosure.Algebraic.Context.queryData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.queryData
/-- info: 'Hex.RealClosure.Algebraic.Context.replayData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.replayData
/-- info: 'Hex.RealClosure.Algebraic.Context.count_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.count_roots
/-- info: 'Hex.RealClosure.Algebraic.Context.unique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.unique_root
/-- info: 'Hex.RealClosure.Algebraic.Context.descriptorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.descriptorData
/-- info: 'Hex.RealClosure.Algebraic.Context.interpretDescriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.interpretDescriptor
/-- info: 'Hex.RealClosure.Algebraic.Context.selectedSigns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.selectedSigns
