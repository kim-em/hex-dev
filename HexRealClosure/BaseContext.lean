/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFn.Extension
public import HexOrderedFn.Infinitesimal
public import HexRealClosure.BaseMap

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

/-- An immutable registry entry identifies one caller-supplied approximation provider. -/
structure ConstantKey where
  name : String
  version : Nat
  deriving DecidableEq, Repr

/-- Readers are relative to one fixed registry. A key is never rebound within it. -/
abbrev Registry := ConstantKey → Option (Rat → Bounds)

/-- Literal identity of a base context within its registry. -/
structure Signature where
  constants : List ConstantKey
  infinitesimals : Nat
  deriving DecidableEq, Repr

/-- A real-constant prefix. Each search uses the exact predecessor bounds.
Only termination premises are stored; interpretation is a companion obligation. -/
inductive RealChain (registry : Registry) : (K : Type) → [Lean.Grind.Field K] → [DecidableEq K] →
    (K → Rat → Bounds) → (K → Int) → Type 1
  | base : RealChain registry Rat (fun a _ => .singleton a) orderSign
  | step {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → Bounds} {sign : K → Int}
      (parent : RealChain registry K approx sign) (key : ConstantKey)
      (bounds : Rat → Bounds) (registered : registry key = some bounds)
      (signProgress : ∀ f : RationalFn K,
        Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
      (approxProgress : ∀ (f : RationalFn K) (δ : Rat),
        Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0) :
      RealChain registry (RationalFn K)
        (fun f δ => Real.approx ⟨approx, bounds⟩ f δ (approxProgress f δ))
        (fun f => Real.sign ⟨approx, bounds⟩ f (signProgress f))

/-- Immutable handle for a registry-bound real prefix. -/
structure RealContext (registry : Registry) (K : Type) [Lean.Grind.Field K] [DecidableEq K]
    (approx : K → Rat → Bounds) (sign : K → Int) where
  private mk ::
  chain : RealChain registry K approx sign

/-- Pack an actual native real chain without rebuilding its providers or
replacing progress for any predecessor. -/
def RealContext.ofChain {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) : RealContext registry K approx sign :=
  ⟨chain⟩

private theorem RealContext.ofChain_chain_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) : (RealContext.ofChain chain).chain = chain := rfl

theorem RealContext.ofChain_chain {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) : (RealContext.ofChain chain).chain = chain :=
  RealContext.ofChain_chain_proof chain

/-- Start the real prefix at the rational field. -/
def RealContext.rational (registry : Registry) :
    RealContext registry Rat (fun a _ => .singleton a) orderSign := ⟨.base⟩

@[expose] def RealContext.approx {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {baseApprox : K → Rat → Bounds} {sign : K → Int}
    (_context : RealContext registry K baseApprox sign) : K → Rat → Bounds := baseApprox

/-- The registered provider paired with this predecessor's own coefficient bounds. -/
@[expose] def RealContext.source {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (_parent : RealContext registry K approx sign) (key : ConstantKey)
    (present : (registry key).isSome = true) : Approximation K :=
  ⟨approx, (registry key).get present⟩

/-- Add one real provider found in the immutable registry. Search progress refers
to the exact computed source; a caller cannot substitute predecessor bounds. -/
def RealContext.constant {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0) :
    RealContext registry (RationalFn K)
      (fun f δ => Real.approx (parent.source key present) f δ (ap f δ))
      (fun f => Real.sign (parent.source key present) f (sp f)) :=
  ⟨.step parent.chain key ((registry key).get present)
    (Option.eq_some_of_isSome present) sp ap⟩

/-- A real prefix followed by zero or more positive infinitesimals.
There is no constructor adding a real constant after an infinitesimal. -/
inductive Chain (registry : Registry) : (K : Type) → [Lean.Grind.Field K] → [DecidableEq K] →
    (K → Int) → Type 1
  | real {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → Bounds} {sign : K → Int}
      (parent : RealChain registry K approx sign) : Chain registry K sign
  | infinitesimal {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int} (parent : Chain registry K sign) :
      Chain registry (RationalFn K) (Infinitesimal.sign sign)

/-- Immutable handle for a staged real and infinitesimal base. -/
structure Context (registry : Registry) (K : Type) [Lean.Grind.Field K] [DecidableEq K]
    (sign : K → Int) where
  private mk ::
  chain : Chain registry K sign

/-- Retain an actual native staged chain with its original field dictionary. -/
def Context.ofChain {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) : Context registry K sign := ⟨chain⟩

private theorem Context.ofChain_chain_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) : (Context.ofChain chain).chain = chain := rfl

theorem Context.ofChain_chain {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) : (Context.ofChain chain).chain = chain :=
  Context.ofChain_chain_proof chain

/-- Finish the real prefix before adjoining infinitesimals. -/
def Context.real {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) : Context registry K sign := ⟨.real parent.chain⟩

/-- Adjoin a positive infinitesimal after the complete predecessor field. -/
def Context.infinitesimal {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (parent : Context registry K sign) :
    Context registry (RationalFn K) (Infinitesimal.sign sign) := ⟨.infinitesimal parent.chain⟩

/-- The rational base, before either kind of transcendental extension. -/
@[expose] def rational (registry : Registry) : Context registry Rat orderSign := .real (.rational registry)

/-- Registry keys of the real prefix, in predecessor order. -/
@[expose] def RealChain.keys {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealChain registry K approx sign) : List ConstantKey := by
  cases context with
  | base => exact []
  | step parent key bounds registered sp ap => exact parent.keys ++ [key]

/-- All constant keys and the number of successive infinitesimals are checked
literally. No hash or caller-chosen version number replaces this binding. -/
@[expose] def Chain.signature {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Chain registry K sign) : Signature := by
  cases context with
  | real parent => exact ⟨parent.keys, 0⟩
  | infinitesimal parent =>
    let previous := parent.signature
    exact { previous with infinitesimals := previous.infinitesimals + 1 }

@[expose] def RealContext.keys {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealContext registry K approx sign) : List ConstantKey := context.chain.keys

/-- Every recorded key resolves in the exact immutable registry. -/
theorem RealChain.registered {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealChain registry K approx sign) (key : ConstantKey) (h : key ∈ context.keys) :
    ∃ bounds, registry key = some bounds := by
  induction context with
  | base => change key ∈ [] at h; cases h
  | step parent last bounds registered sp ap ih =>
    change key ∈ parent.keys ++ [last] at h
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact ih h
    · subst key
      exact ⟨bounds, registered⟩

@[expose] def Context.signature {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : Signature := context.chain.signature

private theorem RealContext.keys_rational_proof (registry : Registry) :
    (RealContext.rational registry).chain.keys = [] := rfl

private theorem RealContext.keys_constant_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (OrderedFn.Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (OrderedFn.Real.approxAttempt (parent.source key present) f
        (OrderedFn.Real.requestWidth δ))) 0) :
    (parent.constant key present sp ap).chain.keys = parent.chain.keys ++ [key] := rfl

private theorem Context.signature_real_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) :
    (Context.real parent).signature = ⟨parent.chain.keys, 0⟩ := rfl

theorem RealContext.keys_rational (registry : Registry) :
    (RealContext.rational registry).chain.keys = [] := RealContext.keys_rational_proof registry

theorem RealContext.keys_constant {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (OrderedFn.Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (OrderedFn.Real.approxAttempt (parent.source key present) f
        (OrderedFn.Real.requestWidth δ))) 0) :
    (parent.constant key present sp ap).chain.keys = parent.chain.keys ++ [key] := RealContext.keys_constant_proof parent key present sp ap

theorem Context.signature_real {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) :
    (Context.real parent).signature = ⟨parent.chain.keys, 0⟩ := Context.signature_real_proof parent

private theorem Context.signature_infinitesimal_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) :
    context.infinitesimal.signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + 1 } := rfl

theorem Context.signature_infinitesimal {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) :
    context.infinitesimal.signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + 1 } :=
  Context.signature_infinitesimal_proof context

/-- An existing real prefix, including the progress proofs already supplied
when its providers were registered. Packing does not construct a new field. -/
inductive RealPrefix (registry : Registry) : Type 1
  | pack {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
      (context : RealContext registry K approx sign)

/-- An existing staged base context with its native carrier hidden. -/
inductive PackedContext (registry : Registry) : Type 1
  | pack {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
      (context : Context registry K sign)

namespace RealPrefix

@[expose] def keys {registry : Registry} (entry : RealPrefix registry) : List ConstantKey := by
  cases entry with
  | pack context => exact context.keys

@[expose] def finish {registry : Registry} (entry : RealPrefix registry) : PackedContext registry := by
  cases entry with
  | pack context => exact .pack (.real context)

theorem keys_rational (registry : Registry) :
    (pack (.rational registry)).keys = [] := RealContext.keys_rational registry

theorem keys_pack {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealContext registry K approx sign) : (pack context).keys = context.keys := rfl

private theorem keys_injective {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (left : RealChain registry K approx sign) (right : RealPrefix registry)
    (same : left.keys = right.keys) : RealPrefix.pack ⟨left⟩ = right := by
  induction left generalizing right with
  | base =>
    rcases right with ⟨⟨right⟩⟩
    cases right with
    | base => rfl
    | step parent key bounds registered sp ap =>
      change [] = parent.keys ++ [key] at same
      have lengths := congrArg List.length same
      simp at lengths
  | step parent key bounds registered sp ap ih =>
    rcases right with ⟨⟨right⟩⟩
    cases right with
    | base =>
      change parent.keys ++ [key] = [] at same
      have lengths := congrArg List.length same
      simp at lengths
    | step other last otherBounds otherRegistered otherSp otherAp =>
      change parent.keys ++ [key] = other.keys ++ [last] at same
      have parts : parent.keys = other.keys ∧ key = last := by
        have split := List.append_inj' same (by simp)
        exact ⟨split.1, by simpa using split.2⟩
      have previous := ih (RealPrefix.pack ⟨other⟩) parts.1
      cases previous
      cases parts.2
      have equal : bounds = otherBounds := Option.some.inj (registered.symm.trans otherRegistered)
      cases equal
      rfl

/-- Within one immutable registry, the complete ordered key path identifies
its validated real prefix, including the exact predecessor bounds. -/
theorem keys_inj {registry : Registry} {left right : RealPrefix registry}
    (same : left.keys = right.keys) : left = right := by
  cases left with
  | pack context => exact keys_injective context.chain right same

end RealPrefix

namespace PackedContext

@[expose] def signature {registry : Registry} (entry : PackedContext registry) : Signature := by
  cases entry with
  | pack context => exact context.signature

@[expose] def infinitesimal {registry : Registry} (entry : PackedContext registry) : PackedContext registry := by
  cases entry with
  | pack context => exact .pack context.infinitesimal

/-- Reconstruct finitely many infinitesimal stages using the native constructor. -/
@[expose] def extend {registry : Registry} (context : PackedContext registry) :
    Nat → PackedContext registry
  | 0 => context
  | n + 1 => (context.extend n).infinitesimal

theorem infinitesimal_signature {registry : Registry} (context : PackedContext registry) :
    context.infinitesimal.signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + 1 } := by
  cases context with
  | pack context => exact Context.signature_infinitesimal context

theorem extend_signature {registry : Registry} (context : PackedContext registry) (n : Nat) :
    (context.extend n).signature =
      { context.signature with infinitesimals := context.signature.infinitesimals + n } := by
  induction n with
  | zero => simp [extend]
  | succ n ih => simp [extend, infinitesimal_signature, ih, Nat.add_assoc]

/-- Accumulate native stages without retaining a recursive call on the stack. -/
@[expose] def extendImpl {registry : Registry} (context : PackedContext registry) :
    Nat → PackedContext registry
  | 0 => context
  | n + 1 => extendImpl context.infinitesimal n

/-- Native base extension commutes with one additional infinitesimal stage. -/
theorem extend_infinitesimal {registry : Registry}
    (context : PackedContext registry) (n : Nat) :
    context.infinitesimal.extend n = (context.extend n).infinitesimal := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg PackedContext.infinitesimal ih

private theorem extendImpl_eq {registry : Registry} (context : PackedContext registry)
    (n : Nat) : context.extendImpl n = context.extend n := by
  induction n generalizing context with
  | zero => rfl
  | succ n ih =>
    rw [extendImpl, ih, extend_infinitesimal]
    rfl

@[csimp] theorem extend_eq_impl : @extend = @extendImpl := by
  funext registry context n
  exact (extendImpl_eq context n).symm

end PackedContext

theorem RealPrefix.finish_signature {registry : Registry} (entry : RealPrefix registry) :
    entry.finish.signature = ⟨entry.keys, 0⟩ := by
  cases entry with
  | pack context => exact Context.signature_real context

private def Chain.realPrefix {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) : RealPrefix registry := by
  cases chain with
  | real parent => exact .pack ⟨parent⟩
  | infinitesimal parent => exact parent.realPrefix

/-- Retrieve the actual real prefix, retaining its registered progress premises. -/
def Context.realPrefix {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : RealPrefix registry := context.chain.realPrefix

private theorem Context.realPrefix_real_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealContext registry K approx sign) :
    (Context.real context).realPrefix = .pack context := rfl

theorem Context.realPrefix_real {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealContext registry K approx sign) :
    (Context.real context).realPrefix = .pack context := Context.realPrefix_real_proof context

private theorem Context.realPrefix_infinitesimal_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) :
    context.infinitesimal.realPrefix = context.realPrefix := rfl

theorem Context.realPrefix_infinitesimal {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) :
    context.infinitesimal.realPrefix = context.realPrefix :=
  Context.realPrefix_infinitesimal_proof context

namespace PackedContext

@[expose] def realPrefix {registry : Registry} (context : PackedContext registry) :
    RealPrefix registry := by
  cases context with
  | pack context => exact context.realPrefix

@[expose] def depth {registry : Registry} (context : PackedContext registry) : Nat :=
  context.signature.infinitesimals

private theorem reconstruct_proof {registry : Registry} (context : PackedContext registry) :
    context.realPrefix.finish.extend context.depth = context := by
  cases context with
  | pack context =>
    rcases context with ⟨chain⟩
    induction chain with
    | real parent => rfl
    | infinitesimal parent ih =>
      exact congrArg PackedContext.infinitesimal ih

/-- Every native staged context decomposes into its actual prefix and depth. -/
theorem reconstruct {registry : Registry} (context : PackedContext registry) :
    context.realPrefix.finish.extend context.depth = context := reconstruct_proof context

/-- The real-prefix path is the constants component of the whole binding. -/
theorem prefix_keys {registry : Registry} (context : PackedContext registry) :
    context.realPrefix.keys = context.signature.constants := by
  have same := congrArg PackedContext.signature context.reconstruct
  rw [extend_signature, RealPrefix.finish_signature] at same
  exact congrArg Signature.constants same

/-- Full base bindings identify the actual native context, rather than only
its serialized description. Registry providers and predecessor progress are
fixed by the validated ordered real prefix. -/
theorem signature_inj {registry : Registry} {left right : PackedContext registry}
    (same : left.signature = right.signature) : left = right := by
  have prefixes : left.realPrefix = right.realPrefix := RealPrefix.keys_inj (by
    rw [prefix_keys, prefix_keys, same])
  have depths : left.depth = right.depth := congrArg Signature.infinitesimals same
  rw [← left.reconstruct, ← right.reconstruct, prefixes, depths]

instance {registry : Registry} : DecidableEq (PackedContext registry) := fun left right =>
  decidable_of_iff (left.signature = right.signature) ⟨signature_inj, congrArg signature⟩

end PackedContext

/-- Integral rational coefficients, recursively denominator-one polynomials
at real stages. This is a storage predicate, not a test of transcendence. -/
@[expose] def RealChain.isClean {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (context : RealChain registry K approx sign) : K → Bool := by
  cases context with
  | base => exact fun q => q.den == 1
  | step parent _ _ _ _ =>
    exact fun f => (f.den == 1) && f.num.toArray.all parent.isClean

/-- Cleanliness descends through every real and infinitesimal predecessor. -/
@[expose] def Chain.isClean {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Chain registry K sign) : K → Bool := by
  cases context with
  | real parent => exact parent.isClean
  | infinitesimal parent =>
    exact fun f => (f.den == 1) && f.num.toArray.all parent.isClean

@[expose] def Context.isClean {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : K → Bool := context.chain.isClean

/-- Values are nominally bound to their entire immutable context, even when
two contexts have definitionally equal carriers and sign operations. -/
structure Element {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int} (context : Context registry K sign) where
  stored : K

namespace Element

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K] {baseSign : K → Int}
variable {context : Context registry K baseSign}

@[ext] theorem ext {a b : Element context} (h : a.stored = b.stored) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (Element context) := fun a b =>
  decidable_of_iff (a.stored = b.stored) ⟨ext, congrArg stored⟩

instance : Zero (Element context) := ⟨⟨0⟩⟩
instance : One (Element context) := ⟨⟨1⟩⟩
instance : NatCast (Element context) :=
  ⟨fun k => ⟨@NatCast.natCast K Lean.Grind.Semiring.natCast k⟩⟩
instance (k : Nat) : OfNat (Element context) (k + 2) :=
  ⟨NatCast.natCast (k + 2)⟩
instance : Add (Element context) := ⟨fun a b => ⟨a.stored + b.stored⟩⟩
instance : Neg (Element context) := ⟨fun a => ⟨-a.stored⟩⟩
instance : Sub (Element context) := ⟨fun a b => ⟨a.stored - b.stored⟩⟩
instance : Mul (Element context) := ⟨fun a b => ⟨a.stored * b.stored⟩⟩
instance : Inv (Element context) := ⟨fun a => ⟨a.stored⁻¹⟩⟩
instance : Div (Element context) := ⟨fun a b => ⟨a.stored / b.stored⟩⟩

/-- Total sign belonging to this context. -/
@[expose] def sign (a : Element context) : Int := baseSign a.stored

/-- The recursively denominator-one storage predicate of the whole base. -/
@[expose] def isClean (a : Element context) : Bool := context.isClean a.stored

/-- Compare within one immutable context. -/
@[expose] def compare (a b : Element context) : Ordering :=
  let s := (a - b).sign
  if s < 0 then .lt else if s = 0 then .eq else .gt

/-- Equality of canonical base-field values within one context. -/
@[expose] def equal (a b : Element context) : Bool := decide (a.stored = b.stored)

/-- Optional nonzero inverse; the ordinary inverse still maps zero to zero. -/
@[expose] def inv? (a : Element context) : Option (Element context) :=
  if a = 0 then none else some a⁻¹

theorem inv?_isNone (a : Element context) : a.inv?.isNone = true ↔ a = 0 := by
  simp [inv?]

theorem stored_eq_zero (a : Element context) : a.stored = 0 ↔ a = 0 :=
  ⟨fun h => ext h, fun h => congrArg stored h⟩

/-- Explicit inclusion in the newly adjoined positive infinitesimal level. -/
@[expose] def embed (a : Element context) : Element (.infinitesimal context) :=
  ⟨RationalFn.C a.stored⟩

@[simp] theorem stored_embed (a : Element context) :
    a.embed.stored = RationalFn.C a.stored := rfl

theorem embed_zero : (0 : Element context).embed = 0 := ext RationalFn.C_zero

theorem embed_one : (1 : Element context).embed = 1 := ext RationalFn.C_one

theorem embed_add (a b : Element context) : (a + b).embed = a.embed + b.embed :=
  ext (RationalFn.C_add a.stored b.stored)

theorem embed_sub (a b : Element context) : (a - b).embed = a.embed - b.embed :=
  ext (RationalFn.C_sub a.stored b.stored)

theorem embed_equal (a b : Element context) : a.embed.equal b.embed = a.equal b := by
  simp only [equal, stored_embed, RationalFn.C_injective.eq_iff]

theorem embed_mul (a b : Element context) : (a * b).embed = a.embed * b.embed :=
  ext (RationalFn.C_mul a.stored b.stored)

theorem embed_inv (a : Element context) : a⁻¹.embed = a.embed⁻¹ :=
  ext (RationalFn.C_inv a.stored)

/-- The new infinitesimal itself; predecessor values use the explicit embedding. -/
@[expose] def infinitesimal (context : Context registry K baseSign) :
    Element (.infinitesimal context) := ⟨RationalFn.X⟩

/-- Include a value from the real prefix into its next registered constant. -/
@[expose] def embedConstant {approx : K → Rat → Bounds}
    (parent : RealContext registry K approx baseSign) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)
    (a : Element (.real parent)) : Element (.real (.constant parent key present sp ap)) :=
  ⟨RationalFn.C a.stored⟩

section Constant

variable {approx : K → Rat → Bounds}
variable (parent : RealContext registry K approx baseSign) (key : ConstantKey)
variable (present : (registry key).isSome = true)
variable (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
variable (ap : ∀ (f : RationalFn K) (δ : Rat),
  Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)

theorem embedConstant_zero :
    embedConstant parent key present sp ap 0 = 0 := ext RationalFn.C_zero

theorem embedConstant_one :
    embedConstant parent key present sp ap 1 = 1 := ext RationalFn.C_one

theorem embedConstant_add (a b : Element (.real parent)) :
    embedConstant parent key present sp ap (a + b) =
      embedConstant parent key present sp ap a + embedConstant parent key present sp ap b :=
  ext (RationalFn.C_add a.stored b.stored)

theorem embedConstant_sub (a b : Element (.real parent)) :
    embedConstant parent key present sp ap (a - b) =
      embedConstant parent key present sp ap a - embedConstant parent key present sp ap b :=
  ext (RationalFn.C_sub a.stored b.stored)

theorem embedConstant_equal (a b : Element (.real parent)) :
    (embedConstant parent key present sp ap a).equal
      (embedConstant parent key present sp ap b) = a.equal b := by
  simp only [equal, embedConstant, RationalFn.C_injective.eq_iff]

theorem embedConstant_mul (a b : Element (.real parent)) :
    embedConstant parent key present sp ap (a * b) =
      embedConstant parent key present sp ap a * embedConstant parent key present sp ap b :=
  ext (RationalFn.C_mul a.stored b.stored)

theorem embedConstant_inv (a : Element (.real parent)) :
    embedConstant parent key present sp ap a⁻¹ = (embedConstant parent key present sp ap a)⁻¹ :=
  ext (RationalFn.C_inv a.stored)

end Constant

end Element
variable {registry : Registry}

@[expose, reducible] def RealPrefix.Carrier (entry : RealPrefix registry) : Type := by
  cases entry with
  | @pack K => exact K

@[instance_reducible] instance (entry : RealPrefix registry) : Lean.Grind.Field entry.Carrier := by
  cases entry with
  | @pack K => change Lean.Grind.Field K; infer_instance

@[instance_reducible] instance (entry : RealPrefix registry) : DecidableEq entry.Carrier := by
  cases entry with
  | @pack K => change DecidableEq K; infer_instance

/-- Include an existing real prefix in an actual later native real chain.
Complete ordered paths are checked before any coefficient type is aligned. -/
def RealChain.embedding? {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (target : RealChain registry K approx sign) (source : RealPrefix registry) :
    Option (FieldEmbedding source.Carrier K) :=
  if keys : source.keys = target.keys then
    let same : source = RealPrefix.pack (RealContext.ofChain target) :=
      RealPrefix.keys_inj (by
        simpa only [RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using keys)
    some (same.symm ▸ FieldEmbedding.identity K)
  else
    match target with
    | .base => none
    | @RealChain.step _ B field eq approx sign parent _ _ _ _ _ =>
      (parent.embedding? source).map fun previous =>
        previous.comp (FieldEmbedding.constants B)

/-- The checked producer retains the exact prefix as the identity map. -/
theorem RealChain.embedding?_self {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (target : RealChain registry K approx sign) :
    target.embedding? (.pack (RealContext.ofChain target)) =
      some (FieldEmbedding.identity K) := by
  rw [RealChain.embedding?]
  simp only [RealPrefix.keys_pack, RealContext.keys, RealContext.ofChain_chain,
    ↓reduceDIte]

/-- A nonempty predecessor cannot enter the rational base. -/
theorem RealChain.embedding?_base (source : RealPrefix registry)
    (different : source.keys ≠ (RealChain.base (registry := registry)).keys) :
    RealChain.base.embedding? source = none := by
  rw [RealChain.embedding?]
  simp only [different, ↓reduceDIte]

/-- A proper real-prefix map follows the actual stored predecessor. -/
theorem RealChain.embedding?_step {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (parent : RealChain registry K approx sign)
    (key : ConstantKey) (bounds : Rat → Bounds) (registered : registry key = some bounds)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0)
    (source : RealPrefix registry)
    (different : source.keys ≠ (parent.step key bounds registered sp ap).keys) :
    (parent.step key bounds registered sp ap).embedding? source =
      (parent.embedding? source).map (fun previous =>
        previous.comp (FieldEmbedding.constants K)) := by
  rw [RealChain.embedding?]
  simp only [different, ↓reduceDIte]

/-- Check real-prefix ancestry using the target's existing providers and
progress proofs. No provider is looked up again or approximated here. -/
def RealPrefix.embedding? (source target : RealPrefix registry) :
    Option (FieldEmbedding source.Carrier target.Carrier) := by
  cases target with
  | pack context => exact context.chain.embedding? source

private theorem RealPrefix.embedding?_ofChain_proof {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (source : RealPrefix registry) (target : RealChain registry K approx sign) :
    source.embedding? (.pack (RealContext.ofChain target)) = target.embedding? source := rfl

/-- Packing an actual real chain retains its checked coefficient map. -/
theorem RealPrefix.embedding?_ofChain {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → Bounds} {sign : K → Int}
    (source : RealPrefix registry) (target : RealChain registry K approx sign) :
    source.embedding? (.pack (RealContext.ofChain target)) = target.embedding? source :=
  RealPrefix.embedding?_ofChain_proof source target

private theorem prefix_snoc {A : Type} (source target : List A) (last : A)
    (different : source ≠ target ++ [last]) :
    source <+: target ++ [last] ↔ source <+: target := by
  constructor
  · intro included
    have lengths := included.length_le
    have unequal : source.length ≠ (target ++ [last]).length := by
      intro same
      exact different (included.eq_of_length same)
    exact List.prefix_of_prefix_length_le included (List.prefix_append target [last]) (by
      simp only [List.length_append, List.length_singleton] at lengths unequal
      omega)
  · exact List.prefix_append_of_prefix

/-- Real-prefix inclusion succeeds exactly for an ordered predecessor path. -/
theorem RealChain.embedding?_isSome {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (target : RealChain registry K approx sign) (source : RealPrefix registry) :
    (target.embedding? source).isSome = true ↔ source.keys <+: target.keys := by
  induction target with
  | base =>
    by_cases same : source.keys = []
    · simp only [RealChain.embedding?, RealChain.keys, same, ↓reduceDIte,
        Option.isSome_some, List.prefix_refl]
    · simp only [RealChain.embedding?, RealChain.keys, same, ↓reduceDIte,
        Option.isSome_none, Bool.false_eq_true, List.prefix_nil]
  | step parent key bounds registered sp ap ih =>
    have step_keys : (parent.step key bounds registered sp ap).keys =
        parent.keys ++ [key] := by rw [RealChain.keys]
    by_cases same : source.keys = parent.keys ++ [key]
    · rw [RealChain.embedding?]
      simp only [step_keys, same, ↓reduceDIte, Option.isSome_some]
      exact iff_of_true trivial (List.prefix_refl _)
    · rw [RealChain.embedding?]
      simp only [step_keys, same, ↓reduceDIte, Option.isSome_map]
      change (parent.embedding? source).isSome = true ↔
        source.keys <+: parent.keys ++ [key]
      exact ih.trans (prefix_snoc source.keys parent.keys key same).symm

/-- Checked packed real-prefix inclusion succeeds exactly for an ordered path. -/
theorem RealPrefix.embedding?_isSome (source target : RealPrefix registry) :
    (source.embedding? target).isSome = true ↔ source.keys <+: target.keys := by
  cases target with
  | pack context => exact context.chain.embedding?_isSome source

@[expose, reducible] def PackedContext.Carrier (entry : PackedContext registry) : Type := by
  cases entry with
  | @pack K => exact K

@[instance_reducible] instance (entry : PackedContext registry) : Lean.Grind.Field entry.Carrier := by
  cases entry with
  | @pack K => change Lean.Grind.Field K; infer_instance

@[instance_reducible] instance (entry : PackedContext registry) : DecidableEq entry.Carrier := by
  cases entry with
  | @pack K => change DecidableEq K; infer_instance

/-- Include an actual staged predecessor in a later staged chain. Equal
infinitesimal depths preserve each formal variable through coefficient maps;
additional target infinitesimals use constant inclusions, retaining the
original order and identity of every earlier variable. -/
def Chain.embedding? {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (target : Chain registry K sign)
    (source : PackedContext registry) : Option (FieldEmbedding source.Carrier K) :=
  match target with
  | @Chain.real _ B field eq approx sign targetReal =>
    match source with
    | @PackedContext.pack _ S sf se ss (@Context.mk registry S sf se ss sourceChain) =>
      match sourceChain with
      | @Chain.real _ S sf se approx sign sourceReal =>
        targetReal.embedding? (.pack (RealContext.ofChain sourceReal))
      | @Chain.infinitesimal _ T tf te ts sourceParent => none
  | @Chain.infinitesimal _ B field eq sign parent =>
    if source.signature.infinitesimals < parent.signature.infinitesimals + 1 then
      (parent.embedding? source).map fun previous =>
        previous.comp (FieldEmbedding.constants B)
    else
      match source with
      | @PackedContext.pack _ S sf se ss (@Context.mk registry S sf se ss sourceChain) =>
        match sourceChain with
        | @Chain.real _ T tf te approx ts sourceReal => none
        | @Chain.infinitesimal _ S sf se ss sourceParent =>
          (parent.embedding? (.pack (Context.ofChain sourceParent))).map fun previous =>
            previous.rationalFunctions

/-- Real-stage transport uses the actual real-prefix producer. -/
private theorem Chain.embedding?_real_proof {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    (target : RealChain registry K approx sign)
    (source : RealChain registry S sourceApprox sourceSign) :
    (Chain.real target).embedding? (.pack (Context.ofChain (.real source))) =
      target.embedding? (.pack (RealContext.ofChain source)) := rfl

theorem Chain.embedding?_real {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    (target : RealChain registry K approx sign)
    (source : RealChain registry S sourceApprox sourceSign) :
    (Chain.real target).embedding? (.pack (Context.ofChain (.real source))) =
      target.embedding? (.pack (RealContext.ofChain source)) := Chain.embedding?_real_proof target source

/-- A staged infinitesimal cannot be included into a real-only target. -/
private theorem Chain.embedding?_real_inf_proof {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int} {sourceSign : S → Int}
    (target : RealChain registry K approx sign) (source : Chain registry S sourceSign) :
    (Chain.real target).embedding? (.pack (Context.ofChain (.infinitesimal source))) = none := rfl

theorem Chain.embedding?_real_inf {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int} {sourceSign : S → Int}
    (target : RealChain registry K approx sign) (source : Chain registry S sourceSign) :
    (Chain.real target).embedding? (.pack (Context.ofChain (.infinitesimal source))) = none := Chain.embedding?_real_inf_proof target source

/-- An additional target infinitesimal is a constant inclusion of the entire
previous native map. -/
theorem Chain.embedding?_extra {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (target : Chain registry K sign) (source : PackedContext registry)
    (deeper : source.signature.infinitesimals < target.signature.infinitesimals + 1) :
    target.infinitesimal.embedding? source =
      (target.embedding? source).map (fun previous =>
        previous.comp (FieldEmbedding.constants K)) := by
  rw [Chain.embedding?.eq_def]
  simp only [deeper, ↓reduceIte]

/-- Aligned infinitesimal levels retain their formal variables while embedding
the actual predecessor coefficients. -/
theorem Chain.embedding?_aligned {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {sign : K → Int} {sourceSign : S → Int}
    (target : Chain registry K sign) (source : Chain registry S sourceSign)
    (aligned : ¬ (PackedContext.pack (Context.ofChain source.infinitesimal)).signature.infinitesimals <
      target.signature.infinitesimals + 1) :
    target.infinitesimal.embedding? (.pack (Context.ofChain source.infinitesimal)) =
      (target.embedding? (.pack (Context.ofChain source))).map
        (fun previous => previous.rationalFunctions) := by
  rw [Chain.embedding?.eq_def]
  simp only [aligned, ↓reduceIte]
  rfl

private theorem signature_real {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    (Chain.real chain).signature = ⟨chain.keys, 0⟩ := rfl

private theorem signature_infinitesimal {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (chain : Chain registry K sign) :
    chain.infinitesimal.signature =
      { chain.signature with infinitesimals := chain.signature.infinitesimals + 1 } := rfl

private theorem signature_pack {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (chain : Chain registry K sign) :
    (PackedContext.pack (Context.mk chain)).signature = chain.signature := rfl

private theorem signature_ofChain {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (chain : Chain registry K sign) :
    (PackedContext.pack (Context.ofChain chain)).signature = chain.signature := rfl

/-- Staged inclusion succeeds exactly for real-prefix ancestry and
nondecreasing infinitesimal depth. The depth branch retains earlier variables. -/
theorem Chain.embedding?_isSome {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (target : Chain registry K sign)
    (source : PackedContext registry) :
    (target.embedding? source).isSome = true ↔
      source.signature.constants <+: target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  induction target generalizing source with
  | real targetReal =>
    cases source with
    | pack sourceContext =>
      rcases sourceContext with ⟨sourceChain⟩
      cases sourceChain with
      | real sourceReal =>
        rw [Chain.embedding?]
        simpa only [signature_pack, signature_real, RealPrefix.keys_pack,
          RealContext.keys, RealContext.ofChain_chain, Nat.le_refl, and_true] using
            targetReal.embedding?_isSome (.pack (RealContext.ofChain sourceReal))
      | infinitesimal sourceParent =>
        rw [Chain.embedding?]
        simp only [Option.isSome_none, Bool.false_eq_true, signature_pack,
          signature_infinitesimal, signature_real]
        constructor
        · intro impossible; exact impossible.elim
        · rintro ⟨_, depths⟩; omega
  | infinitesimal parent ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.embedding?.eq_def]
      simp only [ite_eq_left deeper, Option.isSome_map]
      rw [ih, signature_infinitesimal]
      change (source.signature.constants <+: parent.signature.constants ∧
        source.signature.infinitesimals ≤ parent.signature.infinitesimals) ↔
        (source.signature.constants <+: parent.signature.constants ∧
          source.signature.infinitesimals ≤ parent.signature.infinitesimals + 1)
      constructor
      · rintro ⟨keys, depths⟩
        exact ⟨keys, by omega⟩
      · rintro ⟨keys, depths⟩
        exact ⟨keys, by omega⟩
    · cases source with
      | pack sourceContext =>
        rcases sourceContext with ⟨sourceChain⟩
        cases sourceChain with
        | real sourceReal =>
          simp only [signature_pack, signature_real] at deeper
          omega
        | infinitesimal sourceParent =>
          rw [Chain.embedding?]
          simp only [ite_eq_right deeper, Option.isSome_map]
          rw [ih]
          simp only [signature_ofChain, signature_pack, signature_infinitesimal,
            Nat.add_le_add_iff_right]

/-- Transport the native coefficient field after checking real-prefix ancestry
and retaining the declared order of all source infinitesimals. -/
def PackedContext.embedding? {registry : Registry} (source target : PackedContext registry) :
    Option (FieldEmbedding source.Carrier target.Carrier) := by
  cases target with
  | pack context => exact context.chain.embedding? source

private theorem PackedContext.embedding?_ofChain_proof {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (source : PackedContext registry) (target : Chain registry K sign) :
    source.embedding? (.pack (Context.ofChain target)) = target.embedding? source := rfl

/-- Packing an actual chain retains the coefficient map returned by its producer. -/
theorem PackedContext.embedding?_ofChain {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (source : PackedContext registry) (target : Chain registry K sign) :
    source.embedding? (.pack (Context.ofChain target)) = target.embedding? source :=
  PackedContext.embedding?_ofChain_proof source target

/-- Native packed inclusion has exactly the staged-chain compatibility boundary. -/
theorem PackedContext.embedding?_isSome {registry : Registry}
    (source target : PackedContext registry) :
    (source.embedding? target).isSome = true ↔
      source.signature.constants <+: target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  cases target with
  | pack target => exact target.chain.embedding?_isSome source

end Hex.RealClosure.BaseContext
