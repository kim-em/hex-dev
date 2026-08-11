/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.SineSignConformance

/-!
# Joint proof-package registry conformance

The live real-sine executable registry is assembled with its semantic replay
schemas and tactic handles from one package list.  Mutations demonstrate that
coverage is exact and package-local rather than merely global.
-/

namespace Hex.IntervalMathlib.ProofRegistryConformance

open Hex.Interval.Experiment
open Propagator PayloadArena SemanticReplay ProofEmitter ProofRegistry SineSign
open SineSignConformance

def built? : Option (ProofRegistry.Registry semantics Lean.Name) := do
  let session ← transported?
  match ProofRegistry.build session.registry proofPackages with
  | .ok registry => some registry
  | .error _ => none

#guard
  built?.any fun registry =>
    registry.emit.find? sineFactSchema.key == some ``sineFactSchema &&
      registry.emit.find? negationFactSchema.key == some ``negationFactSchema &&
      registry.emit.find? oddnessInstanceSchema.key ==
        some ``oddnessInstanceSchema &&
      registry.emit.find? oddnessEqualitySchema.key ==
        some ``oddnessEqualitySchema

private def missingSine : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, negationProof,
    { semantic := sineProof.semantic
      emit :=
        { schemas :=
            [{ key := oddnessInstanceSchema.key
               handle := ``oddnessInstanceSchema },
             { key := oddnessEqualitySchema.key
               handle := ``oddnessEqualitySchema }] } }]

#guard
  transported?.any fun session =>
    match ProofRegistry.build session.registry missingSine with
    | .error (.missingEmit 2 key) => key == sineFactSchema.key
    | _ => false

private def extraKey : ReplayKey :=
  { rule := sineRuleKey, role := .fact, schema := 99 }

private def extraSine : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, negationProof,
    { semantic := sineProof.semantic
      emit :=
        { schemas := sineEmit.schemas ++
            [{ key := extraKey, handle := ``sineFactSchema }] } }]

#guard
  transported?.any fun session =>
    match ProofRegistry.build session.registry extraSine with
    | .error (.extraEmit 2 key) => key == extraKey
    | _ => false

private def borrowed : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof,
    { semantic := negationProof.semantic
      emit :=
        { schemas := negationEmit.schemas ++
            [{ key := sineFactSchema.key, handle := ``sineFactSchema }] } },
    { semantic := sineProof.semantic
      emit :=
        { schemas :=
            [{ key := oddnessInstanceSchema.key
               handle := ``oddnessInstanceSchema },
             { key := oddnessEqualitySchema.key
               handle := ``oddnessEqualitySchema }] } }]

#guard
  transported?.any fun session =>
    match ProofRegistry.build session.registry borrowed with
    | .error (.extraEmit 1 key) => key == sineFactSchema.key
    | _ => false

private def duplicateSine : Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, negationProof,
    { semantic := sineProof.semantic
      emit :=
        { schemas := sineEmit.schemas ++
            [{ key := sineFactSchema.key, handle := ``sineFactSchema }] } }]

#guard
  transported?.any fun session =>
    match ProofRegistry.build session.registry duplicateSine with
    | .error (.duplicateEmit key) => key == sineFactSchema.key
    | _ => false

private def wrongRole : ReplayKey :=
  { sineFactSchema.key with role := .instance }

private def wrongRolePackages :
    Array (ProofRegistry.Package semantics Lean.Name) :=
  #[sourceProof, negationProof,
    { semantic := sineProof.semantic
      emit :=
        { schemas :=
            [{ key := wrongRole, handle := ``sineFactSchema },
             { key := oddnessInstanceSchema.key
               handle := ``oddnessInstanceSchema },
             { key := oddnessEqualitySchema.key
               handle := ``oddnessEqualitySchema }] } }]

#guard
  transported?.any fun session =>
    match ProofRegistry.build session.registry wrongRolePackages with
    | .error (.missingEmit 2 key) => key == sineFactSchema.key
    | _ => false

end Hex.IntervalMathlib.ProofRegistryConformance
