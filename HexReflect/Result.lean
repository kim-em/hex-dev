/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Budget
public import Lean.Meta.Sym.ExprPtr
public import Lean.Message

public section

/-!
Provider outcomes, declines, failures, conditions, and result records shared
by every symbolic Hex frontend.

An unconditional result is a separate record from a conditional result whose
condition list happens to be empty. Search exhaustion is a decline, never a
proof that a mathematical object does not exist, and malformed evidence is a
failure rather than an ordinary decline.
-/

namespace Hex.Reflect

open Lean

/-- The capabilities a provider can supply. Algorithms request only the
capabilities they need. -/
inductive Capability where
  | scalarEval
  | commRingNormalize
  | decidableZero
  | fieldOps
  | exactQuotient
  | euclideanDivision
  | gcd
  | extendedGcd
  | univariateFactor
  | multivariateFactor
  | sourceTranslation
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- The source views a frontend can request. -/
inductive RequestedView where
  | commRing
  | commSemiring
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Stable provider identity: declaration name plus a configuration version. -/
structure ProviderId where
  name : Name
  version : Nat := 0
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

/-- Why a recognized request could not be satisfied. -/
inductive Decline where
  /-- The carrier has an algebraic structure, but not the requested one. -/
  | unsupportedView (requested : RequestedView) (found : String)
  /-- The carrier has no recognized algebraic structure. -/
  | unsupportedCarrier (carrier : Expr)
  /-- A relevant metavariable remains unassigned. -/
  | unresolvedMetavariable (source : Expr)
  /-- No registered provider supplies the capability for this carrier. -/
  | missingCapability (capability : Capability) (carrier : Expr)
  /-- Several providers of equal priority recognize the request. -/
  | ambiguousProvider (capability : Capability) (candidates : Array ProviderId)
  /-- The source type is outside the supported translations. -/
  | unsupportedSourceType (type : Expr)
  /-- A budget dimension would be exceeded. -/
  | budgetExhausted (info : BudgetExhausted)
  deriving Inhabited

/-- Malformed registration, evidence, or generated data. -/
inductive Failure where
  /-- A provider's registration, quoted value, or evidence is malformed. -/
  | invalidProviderEvidence (provider : ProviderId) (message : String)
  /-- A reflected variable identifier is outside the sealed environment. -/
  | variableOutOfRange (var : Nat) (size : Nat)
  /-- A generated proof does not type-check. -/
  | illTypedProof (message : String)
  /-- An invariant of the session was violated. -/
  | internal (message : String)
  deriving Inhabited

/-- A proposition a result depends on, together with its provenance. -/
structure Condition where
  /-- The canonical proposition the result depends on. -/
  proposition : Expr
  /-- The provider that introduced the condition. -/
  provider : Name
  /-- The source subexpression the condition concerns. -/
  source : Expr
  /-- The operation that introduced the condition. -/
  operation : String
  /-- Why the operation needs the condition. -/
  reason : String
  deriving Inhabited

/-- The four outcomes of provider selection or of an expensive request. -/
inductive ProviderOutcome (α : Type) where
  /-- The provider does not recognize this request; dispatch may continue. -/
  | notApplicable
  /-- The request is recognized but a stated condition or budget cannot be
  satisfied. -/
  | declined (reason : Decline) (usage : BudgetUsage)
  /-- Checked data together with the budget it consumed. -/
  | success (value : α) (usage : BudgetUsage)
  /-- Malformed registration, quoted value, or evidence; reported
  immediately. -/
  | failure (error : Failure)
  deriving Inhabited

/-- A transformed value whose equality proof holds under the listed
conditions. -/
structure ConditionalResult where
  value : Expr
  proof : Expr
  conditions : Array Condition
  atoms : Array Expr
  deriving Inhabited

/-- An unconditional equality between a source expression and its result. -/
structure EqualityResult where
  /-- The caller's instantiated source expression. -/
  source : Expr
  /-- The quoted result value. -/
  value : Expr
  /-- The interpretation of the value in the source carrier, the left-hand
  side of `proof`. -/
  interpretation : Expr
  /-- A proof of `interpretation = source`. -/
  proof : Expr
  /-- The sealed atom environment, as presentation data and valuation. -/
  atoms : Array Expr
  deriving Inhabited

/-- How a property result is justified. -/
inductive PropertyEvidence where
  /-- A checked certificate together with the soundness theorem that reads it. -/
  | certificate (certificate : Expr) (soundness : Expr)
  /-- A direct correctness theorem. -/
  | theorem (proof : Expr)
  deriving Inhabited

/-- A computed display value together with a library-specific property and
its justification. A failed certificate is never replaced with a weaker claim
about the display value. -/
structure PropertyResult where
  value : Expr
  property : Expr
  evidence : PropertyEvidence
  conditions : Array Condition := #[]
  usage : BudgetUsage := Budget.zero
  deriving Inhabited

namespace ProviderOutcome

/-- Map the successful value. -/
def map (f : α → β) : ProviderOutcome α → ProviderOutcome β
  | .notApplicable => .notApplicable
  | .declined r u => .declined r u
  | .success v u => .success (f v) u
  | .failure e => .failure e

instance : Functor ProviderOutcome where
  map := map

/-- The successful value, if any. -/
def value? : ProviderOutcome α → Option α
  | .success v _ => some v
  | _ => none

/-- Whether the outcome is a success. -/
def isSuccess (o : ProviderOutcome α) : Bool :=
  o.value?.isSome

/-- Whether the outcome is a decline. -/
def isDeclined : ProviderOutcome α → Bool
  | .declined .. => true
  | _ => false

/-- Whether the outcome is a failure. -/
def isFailure : ProviderOutcome α → Bool
  | .failure _ => true
  | _ => false

/-- The consumed budget reported by a success or decline. -/
def usage : ProviderOutcome α → BudgetUsage
  | .declined _ u => u
  | .success _ u => u
  | _ => Budget.zero

end ProviderOutcome

namespace Condition

/-- Provenance identity: provider, source subexpression, operation, and
reason. -/
def sameProvenance (a b : Condition) : Bool :=
  a.provider == b.provider && Meta.Sym.isSameExpr a.source b.source &&
    a.operation == b.operation && a.reason == b.reason

/-- Deduplication identity: provenance together with canonical proposition
identity. -/
def sameCondition (a b : Condition) : Bool :=
  sameProvenance a b && Meta.Sym.isSameExpr a.proposition b.proposition

end Condition

/-- Append a condition unless an equal one is already present. The first
occurrence is preserved so side-goal order stays deterministic. -/
def addCondition (cs : Array Condition) (c : Condition) : Array Condition :=
  if cs.any (fun c' => c'.sameCondition c) then cs else cs.push c

/-- Deduplicate a condition list, preserving first occurrences. -/
def dedupConditions (cs : Array Condition) : Array Condition :=
  cs.foldl addCondition #[]

theorem dedupConditions_size_le (cs : Array Condition) :
    (dedupConditions cs).size ≤ cs.size := by
  unfold dedupConditions
  have aux : ∀ (l : List Condition) (acc : Array Condition),
      (l.foldl addCondition acc).size ≤ acc.size + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c l ih =>
      intro acc
      rw [List.foldl_cons]
      refine Nat.le_trans (ih _) ?_
      unfold addCondition
      split
      · simp only [List.length_cons]; omega
      · simp only [Array.size_push, List.length_cons]; omega
  rw [← Array.foldl_toList]
  simpa using aux cs.toList #[]

/-! # Diagnostics -/

/-- Human-readable name of a capability. -/
def Capability.describe : Capability → String
  | .scalarEval => "scalar evaluation"
  | .commRingNormalize => "commutative-ring normalization"
  | .decidableZero => "decidable zero"
  | .fieldOps => "field operations"
  | .exactQuotient => "exact quotient"
  | .euclideanDivision => "Euclidean division"
  | .gcd => "gcd"
  | .extendedGcd => "extended gcd"
  | .univariateFactor => "univariate factorization"
  | .multivariateFactor => "multivariate factorization"
  | .sourceTranslation => "source-type translation"

/-- Human-readable name of a requested view. -/
def RequestedView.describe : RequestedView → String
  | .commRing => "commutative ring"
  | .commSemiring => "commutative semiring"

/-- Human-readable name of a budget dimension. -/
def BudgetDimension.describe : BudgetDimension → String
  | .sourceNodes => "source nodes"
  | .atoms => "atoms"
  | .reflectedNodes => "reflected nodes"
  | .exponent => "literal exponent"
  | .terms => "polynomial terms"
  | .coefficientBits => "coefficient bits"
  | .proofNodes => "proof nodes"

/-- Diagnostic text for a budget report. -/
def BudgetExhausted.toMessageData (b : BudgetExhausted) : MessageData :=
  m!"budget exhausted in dimension {b.dimension.describe}: limit {b.limit}, \
    consumed {b.consumed}, requested {b.requested}"

/-- Diagnostic text for a decline. -/
def Decline.toMessageData : Decline → MessageData
  | .unsupportedView requested found =>
    m!"requested a {requested.describe} view but the carrier classifies as {found}"
  | .unsupportedCarrier carrier =>
    m!"no supported algebraic structure on carrier{indentExpr carrier}"
  | .unresolvedMetavariable source =>
    m!"unresolved metavariable in{indentExpr source}"
  | .missingCapability capability carrier =>
    m!"no provider supplies {capability.describe} for carrier{indentExpr carrier}"
  | .ambiguousProvider capability candidates =>
    m!"ambiguous providers for {capability.describe}: \
      {candidates.map (·.name)}"
  | .unsupportedSourceType type =>
    m!"unsupported source type{indentExpr type}"
  | .budgetExhausted info => info.toMessageData

/-- Diagnostic text for a failure. -/
def Failure.toMessageData : Failure → MessageData
  | .invalidProviderEvidence provider message =>
    m!"invalid evidence from provider {provider.name}: {message}"
  | .variableOutOfRange var size =>
    m!"reflected variable {var} is outside the sealed environment of size {size}"
  | .illTypedProof message => m!"generated proof is ill-typed: {message}"
  | .internal message => m!"internal error: {message}"

/-- Diagnostic text for an outcome, given a description of the value. -/
def ProviderOutcome.toMessageData (describe : α → MessageData) :
    ProviderOutcome α → MessageData
  | .notApplicable => m!"not applicable"
  | .declined r _ => m!"declined: {r.toMessageData}"
  | .success v _ => m!"success: {describe v}"
  | .failure e => m!"failure: {e.toMessageData}"

end Hex.Reflect
