/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.RuntimeEmit
public import HexIntervalMathlib.RuntimeRule
public meta import HexIntervalMathlib.RuntimeEmit
public meta import HexIntervalMathlib.RuntimeRule
public meta import HexIntervalMathlib.Rule
public meta import HexInterval.Canonical

@[expose] public section

/-!
# Built-in arithmetic runtime emitters

This elaborator-only companion pairs the twelve built-in arithmetic theorem
schemas with exact `RuntimeEmit` handles. The joint builder constructs the
executable assembly, theorem registry, and emitter registry in one call.
Caller-owned meanings need their own emitter packages and are intentionally
outside the convenience builder.
-/

namespace Hex.Interval.Rule.Runtime

open Lean Meta

abbrev EmitRegistry (config : Rule.Config) (Plan : Type := List Nat) :=
  RuntimeEmit.Registry Hex.Interval (Rule.semantics config) Cause Plan

inductive EmitError where
  | runtime (error : Error)
  | emit (error : RuntimeEmit.Error)
  | unsupportedMeanings
  deriving Repr

namespace Quote

def isReady (result : BuildResult) : Bool :=
  match result with
  | .ready _ => true
  | .resourceLimit _ => false

def getValue (result : BuildResult) (success : isReady result = true) :
    Hex.Interval :=
  match result with
  | .ready interval => interval
  | .resourceLimit _ => False.elim (by simp [isReady] at success)

meta def dyadicExpr (value : Dyadic) : MetaM Expr := do
  let rational := value.toRat
  let base ← mkAppM ``Dyadic.ofInt #[mkIntLit rational.num]
  if rational.den = 1 then return base
  mkAppM ``HShiftRight.hShiftRight
    #[base, mkIntLit (Int.ofNat rational.den.log2)]

meta def lowerExpr : Lower → MetaM Expr
  | .unbounded => pure (mkConst ``Lower.unbounded)
  | .finite value strict => do
      mkAppM ``Lower.finite #[← dyadicExpr value, toExpr strict]

meta def upperExpr : Upper → MetaM Expr
  | .unbounded => pure (mkConst ``Upper.unbounded)
  | .finite value strict => do
      mkAppM ``Upper.finite #[← dyadicExpr value, toExpr strict]

meta def rawExpr : Raw → MetaM Expr
  | .empty => pure (mkConst ``Raw.empty)
  | .bounds lower upper => do
      mkAppM ``Raw.bounds #[← lowerExpr lower, ← upperExpr upper]

meta def endpointExpr (limit : EndpointLimit) : MetaM Expr :=
  mkAppM ``EndpointLimit.mk
    #[mkNatLit limit.maxEndpointHeight, mkNatLit limit.maxAlignmentShift]

meta def powLimitsExpr (limits : Arithmetic.PowLimits) : MetaM Expr :=
  mkAppM ``Arithmetic.PowLimits.mk #[mkNatLit limits.maxExponent]

meta def precisionLimitsExpr (limits : Arithmetic.PrecisionLimits) : MetaM Expr := do
  mkAppM ``Arithmetic.PrecisionLimits.mk
    #[← endpointExpr limits.endpoint, mkNatLit limits.maxPrecisionMagnitude,
      mkNatLit limits.maxPrecisionBits, mkNatLit limits.maxTemporaryBits]

meta def emptyMeaningsExpr : MetaM Expr := do
  let meaningType ← mkAppM ``Program.Meaning #[mkConst ``Real]
  let emptyList := Lean.mkApp (mkConst ``List.nil [.zero]) meaningType
  pure (Lean.mkAppN (mkConst ``Array.mk [.zero]) #[meaningType, emptyList])

meta def configExpr (config : Rule.Config) : MetaM Expr := do
  unless config.extraMeanings.isEmpty do
    throwError "built-in runtime emitter cannot quote caller function meanings"
  mkAppM ``Rule.Config.mk
    #[← endpointExpr config.endpoint, ← powLimitsExpr config.powerWork,
      mkNatLit config.exponent, ← precisionLimitsExpr config.precisionLimits,
      mkIntLit config.precision, ← dyadicExpr config.constant, ← emptyMeaningsExpr]

meta def intervalExpr (limit : EndpointLimit) (interval : Hex.Interval) : MetaM Expr := do
  let raw ← rawExpr interval.view
  let build ← mkAppM ``ofRawWithin #[← endpointExpr limit, raw]
  let ready ← mkAppM ``isReady #[build]
  let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
  match ofRawWithin limit interval.view with
  | .ready rebuilt =>
      unless rebuilt == interval do
        throwError "runtime emitter changed a canonical interval"
      mkAppM ``getValue #[build, success]
  | .resourceLimit _ =>
      throwError "runtime emitter interval exceeded its endpoint envelope"

meta def schema (config : Rule.Config) (key : Proof.Key) (name : Name) :
    RuntimeEmit.Handle :=
  { key
    schema := { emit := fun _ => do mkAppM name #[← configExpr config] } }

end Quote

meta def emitPackage (config : Rule.Config) :
    RuntimeEmit.Package (Rule.semantics config) :=
  { proof := Rule.package config
    facts :=
      #[Quote.schema config (Rule.schemaKey Rule.negKey) ``Rule.negSchema,
        Quote.schema config (Rule.schemaKey Rule.addKey) ``Rule.addSchema,
        Quote.schema config (Rule.schemaKey Rule.subKey) ``Rule.subSchema,
        Quote.schema config (Rule.schemaKey Rule.mulKey) ``Rule.mulSchema,
        Quote.schema config (Rule.schemaKey Rule.powKey) ``Rule.powSchema,
        Quote.schema config (Rule.schemaKey Rule.absKey) ``Rule.absSchema,
        Quote.schema config (Rule.schemaKey Rule.minKey) ``Rule.minSchema,
        Quote.schema config (Rule.schemaKey Rule.maxKey) ``Rule.maxSchema,
        Quote.schema config (Rule.schemaKey Rule.constantKey) ``Rule.constantSchema,
        Quote.schema config (Rule.schemaKey Rule.invKey) ``Rule.invSchema,
        Quote.schema config (Rule.schemaKey Rule.divKey) ``Rule.divSchema,
        Quote.schema config (Rule.schemaKey Rule.regularizeKey) ``Rule.regularizeSchema] }

meta def quoter (config : Rule.Config) :
    RuntimeEmit.Quoter Hex.Interval (Rule.semantics config) :=
  { factType := { emit := fun _ => pure (Lean.mkConst ``Hex.Interval) }
    fact := { emit := Quote.intervalExpr config.endpoint }
    semantics := { emit := fun _ => do
      Lean.Meta.mkAppM ``Rule.semantics #[← Quote.configExpr config] }
    domain := { emit := fun _ => do
      Lean.Meta.mkAppM ``Rule.domain #[← Quote.configExpr config] }
    laws := { emit := fun _ => do
      Lean.Meta.mkAppM ``Rule.laws #[← Quote.configExpr config] } }

/-- Joint built-in executable/proof/emitter registry for the root-target Meta
bridge. -/
meta def buildEmitWithin (executableLimits : Executable.Limits)
    (emitLimits : RuntimeEmit.Limits) (key : RuntimeProof.Key)
    (config : Rule.Config) (program : Program) :
    Except EmitError (EmitRegistry config) := do
  if !config.extraMeanings.isEmpty then throw .unsupportedMeanings
  let assembly ← assemblyWithin executableLimits config program |>.mapError EmitError.runtime
  RuntimeEmit.Registry.buildWithin executableLimits emitLimits key assembly
    (quoter config) #[emitPackage config]
    |>.mapError EmitError.emit

end Hex.Interval.Rule.Runtime
