/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Provider
public import Std.Data.HashMap

public section

/-!
The invocation-local session state.

The state stores the growing or sealed atom environment, the selected
`Lean.Meta.Sym.Arith` classification identity of each active view, the
reflected-view and converted-value caches, provider selections, conditions,
budgets, and the structured declines and failures raised so far. It does not
copy `Lean.Meta.Sym.Arith.State`: a view records the classification identity,
and the cached operation expressions stay authoritative in `SymM`.

A session belongs to one tactic invocation or one programmatic batch. It may
contain free variables valid only in the current local context and is never
stored in a process-global cache.
-/

namespace Hex.Reflect

open Lean Meta Sym

/-- Canonical-expression identity to atom index. -/
abbrev AtomMap := Std.HashMap ExprPtr Nat

/-- The atom environment: growing while a batch is reified, sealed at a fixed
size afterwards. Allocation is available only in the growing form, so illegal
post-sealing allocation is not represented by an unchecked Boolean. -/
inductive Vars where
  | growing (atoms : Array Expr) (index : AtomMap)
  | sealed (n : Nat) (atoms : Array Expr) (size_eq : atoms.size = n)

namespace Vars

/-- The ordered atom array of either form. -/
def atoms : Vars → Array Expr
  | .growing atoms _ => atoms
  | .sealed _ atoms _ => atoms

/-- Whether the environment is sealed. -/
def isSealed : Vars → Bool
  | .growing .. => false
  | .sealed .. => true

end Vars

/-- A sealed environment: the fixed size, the ordered atom array, and a
session-unique identity used by conversion cache keys. Values are produced
only by sealing a session; a conversion checks that the value it receives is
the session's own. -/
structure Sealed where private mk ::
  n : Nat
  atoms : Array Expr
  size_eq : atoms.size = n
  epoch : Nat

/-- The atom at a sealed index. -/
def Sealed.atom (s : Sealed) (i : Fin s.n) : Expr :=
  s.atoms[i.val]'(by rw [s.size_eq]; exact i.isLt)

/-- The identity of a reflected view: canonical source, canonical carrier,
requested view, classification identity, and the exact structure
instances. -/
structure ViewKey where
  source : Expr
  carrier : Expr
  view : RequestedView
  structureId : Nat
  instances : Array Expr

namespace ViewKey

/-- Semantic fields are compared first, then canonical expression identity of
the carrier and instances, then of the source. -/
def agrees (a b : ViewKey) : Bool :=
  a.view == b.view && a.structureId == b.structureId &&
    a.instances.size == b.instances.size && isSameExpr a.carrier b.carrier &&
    (a.instances.zip b.instances).all (fun (x, y) => isSameExpr x y) &&
    isSameExpr a.source b.source

end ViewKey

/-- A reified commutative-ring input. -/
structure ReifiedRing where
  key : ViewKey
  /-- The canonical source expression. -/
  source : Expr
  /-- The canonical carrier. -/
  carrier : Expr
  /-- The `Lean.Meta.Sym.Arith` classification identity. -/
  ringId : Nat
  /-- The exact `IsCharP` evidence and characteristic, when Lean found them. -/
  charInst? : Option (Expr × Nat)
  expr : RingExpr

/-- A reified commutative-semiring input. It retains its reflected expression
for future consumers and claims no polynomial conversion. -/
structure ReifiedSemiring where
  key : ViewKey
  source : Expr
  carrier : Expr
  semiringId : Nat
  expr : Lean.Meta.Sym.Arith.SemiringExpr

/-- A sealed semiring input: the reflected expression against a sealed atom
array. -/
structure SealedSemiring where
  reflected : ReifiedSemiring
  sealed : Sealed

/-- A requested target monomial order together with its quotation. -/
structure MonoOrder where
  name : Name
  cmp : (n : Nat) → Mono n → Mono n → Ordering
  transCmp : ∀ n, Std.TransCmp (cmp n)
  lawfulEqCmp : ∀ n, Std.LawfulEqCmp (cmp n)
  quoteCmp : Nat → Expr
  quoteTransCmp : Nat → Expr
  quoteLawfulEqCmp : Nat → Expr

attribute [instance] MonoOrder.transCmp MonoOrder.lawfulEqCmp

namespace MonoOrder

private def mkAtSize (name : Name) (n : Nat) : Expr :=
  mkApp (mkConst name) (mkNatLit n)

/-- Lexicographic order. -/
def lex : MonoOrder where
  name := ``Hex.Mono.lex
  cmp _ := Mono.lex
  transCmp _ := inferInstance
  lawfulEqCmp _ := inferInstance
  quoteCmp := mkAtSize ``Hex.Mono.lex
  quoteTransCmp := mkAtSize ``Hex.Mono.instLexTransCmp
  quoteLawfulEqCmp := mkAtSize ``Hex.Mono.instLexLawfulEqCmp

/-- Graded lexicographic order. -/
def grlex : MonoOrder where
  name := ``Hex.Mono.grlex
  cmp _ := Mono.grlex
  transCmp _ := inferInstance
  lawfulEqCmp _ := inferInstance
  quoteCmp := mkAtSize ``Hex.Mono.grlex
  quoteTransCmp := mkAtSize ``Hex.Mono.instGrlexTransCmp
  quoteLawfulEqCmp := mkAtSize ``Hex.Mono.instGrlexLawfulEqCmp

/-- Graded reverse lexicographic order. -/
def grevlex : MonoOrder where
  name := ``Hex.Mono.grevlex
  cmp _ := Mono.grevlex
  transCmp _ := inferInstance
  lawfulEqCmp _ := inferInstance
  quoteCmp := mkAtSize ``Hex.Mono.grevlex
  quoteTransCmp := mkAtSize ``Hex.Mono.instGrevlexTransCmp
  quoteLawfulEqCmp := mkAtSize ``Hex.Mono.instGrevlexLawfulEqCmp

end MonoOrder

/-- The identity of a conversion: the reflected view, the sealed environment
and its size, the characteristic and its exact evidence, the coefficient
provider with its quoted coefficient type, instances, coefficient map, and
interpretation, and the quoted target comparator at the sealed size. -/
structure ConversionKey where
  reflected : ViewKey
  epoch : Nat
  n : Nat
  char? : Option Nat
  charInst? : Option Expr
  provider : ProviderId
  coeffType : Expr
  /-- The quoted `Zero`, `Add`, `BEq`, and `LawfulBEq` instances. -/
  coeffInstances : Array Expr
  ofInt : Expr
  interp : Expr
  /-- The quoted comparator at size `n`. -/
  cmp : Expr

namespace ConversionKey

private def sameOptExpr : Option Expr → Option Expr → Bool
  | none, none => true
  | some a, some b => isSameExpr a b
  | _, _ => false

/-- Semantic fields are compared first, then canonical expression identity for
the classified fields, then structural equality for the quoted provider and
comparator data, which is not canonicalized. -/
def agrees (a b : ConversionKey) : Bool :=
  a.epoch == b.epoch && a.n == b.n && a.char? == b.char? && a.provider == b.provider &&
    a.reflected.agrees b.reflected && sameOptExpr a.charInst? b.charInst? &&
    a.coeffType == b.coeffType && a.coeffInstances == b.coeffInstances &&
    a.ofInt == b.ofInt && a.interp == b.interp && a.cmp == b.cmp

end ConversionKey

/-- A converted input: the reflected source, the sealed environment, the
characteristic choice, the coefficient provider, the target order, the
integer-coefficient term list, and the consumed budget. -/
structure Conversion where
  key : ConversionKey
  reflected : ReifiedRing
  sealed : Sealed
  provider : CoeffProvider
  order : MonoOrder
  terms : List (Mono sealed.n × Int)
  usage : BudgetUsage

/-- The executable polynomial with integer coefficients under the requested
order. -/
def Conversion.poly (c : Conversion) : MvPoly c.sealed.n Int (c.order.cmp c.sealed.n) :=
  ofIntTerms id c.terms

/-- The characteristic used by normalization, if any. -/
def Conversion.char? (c : Conversion) : Option Nat :=
  c.key.char?

/-- The identity of a provider selection. -/
structure ProviderKey where
  capability : Capability
  carrier : Expr
  structureId : Nat
  instances : Array Expr

/-- Semantic fields are compared first, then canonical expression identity. -/
def ProviderKey.agrees (a b : ProviderKey) : Bool :=
  a.capability == b.capability && a.structureId == b.structureId &&
    a.instances.size == b.instances.size && isSameExpr a.carrier b.carrier &&
    (a.instances.zip b.instances).all fun (x, y) => isSameExpr x y

/-- Reflected-view caches, one per requested view. -/
structure ViewCache where
  ring : Array ReifiedRing := #[]
  semiring : Array ReifiedSemiring := #[]

/-- Converted-value cache. -/
abbrev ConversionCache := Array Conversion

/-- Provider-selection cache. -/
abbrev ProviderCache := Array (ProviderKey × ProviderOutcome Evidence)

/-- The session state. -/
structure State where
  vars : Vars := .growing #[] {}
  views : ViewCache := {}
  converted : ConversionCache := #[]
  providers : ProviderCache := #[]
  conditions : Array Condition := #[]
  budget : BudgetState
  declines : Array Decline := #[]
  failures : Array Failure := #[]
  /-- Number of seal operations so far; the next sealed identity. -/
  sealEpoch : Nat := 0
  /-- The decline that caused the exception currently propagating. -/
  pendingDecline : Option Decline := none
  /-- The failure that caused the exception currently propagating. -/
  pendingFailure : Option Failure := none

/-- A fresh state against the given limits. -/
def State.init (limits : Budget) : State :=
  { budget := BudgetState.ofBudget limits }

namespace State

/-- Seal the environment at its current size, or return the existing sealed
identity. -/
def sealVars (s : State) : State × Sealed :=
  match s.vars with
  | .growing atoms _ =>
    let epoch := s.sealEpoch + 1
    ({ s with vars := .sealed atoms.size atoms rfl, sealEpoch := epoch },
      { n := atoms.size, atoms := atoms, size_eq := rfl, epoch := epoch })
  | .sealed n atoms h => (s, { n := n, atoms := atoms, size_eq := h, epoch := s.sealEpoch })

/-- The sealed environment, if sealing has happened. -/
def sealed? (s : State) : Option Sealed :=
  match s.vars with
  | .growing .. => none
  | .sealed n atoms h => some { n := n, atoms := atoms, size_eq := h, epoch := s.sealEpoch }

/-- Whether a sealed value is this session's current sealed environment. -/
def owns (s : State) (sealed : Sealed) : Bool :=
  match s.vars with
  | .growing .. => false
  | .sealed n atoms _ =>
    sealed.epoch == s.sealEpoch && sealed.n == n && sealed.atoms.size == atoms.size &&
      (sealed.atoms.zip atoms).all fun (x, y) => isSameExpr x y

end State

end Hex.Reflect
