/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerEnlarge

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- The actual checked enlargement and its new native parameter. Both use
one rebuilt suffix; accessing the parameter performs no further validation. -/
structure Enlargement (source : Context registry) : Type 1 where
  conversion : Conversion source
  parameter : conversion.context.Value

/-- Package the cached parameter of one rebuilt suffix in its aligned source
context, with the ownership of the actual returned conversion. -/
@[expose] def Rebuilt.enlargement {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    {suffix : Suffix (Context.base base)} {source : Context registry}
    (rebuilt : Rebuilt (Conversion.infinitesimal base) suffix)
    (target_eq : suffix.context = source) : Enlargement source :=
  Enlargement.mk (rebuilt.result.cast target_eq)
    (_root_.cast (congrArg Context.Value (rebuilt.result.cast_spec target_eq).1.symm)
      (rebuilt.parameter base))

/-- Rebuild once and return both the conversion and its new parameter. -/
@[expose] def Origin.enlargeWithParameter? {source : Context registry} (origin : Origin source) :
    Option (Enlargement source) := by
  cases origin with
  | pack base suffix target_eq =>
    exact ((Conversion.infinitesimal base).rebuild? suffix).map
      (fun rebuilt => rebuilt.enlargement base target_eq)

/-- Checked native enlargement exposing the new parameter as result data. -/
@[expose] def Context.enlargeWithParameter? (source : Context registry) :
    Option (Enlargement source) := source.origin.enlargeWithParameter?

/-- The public producer packages the actual reconstructed suffix. -/
theorem Context.enlargeWithParameter?_eq {source : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) (target_eq : suffix.context = source) :
    source.enlargeWithParameter? = ((Conversion.infinitesimal base).rebuild? suffix).map
      (fun rebuilt => rebuilt.enlargement base target_eq) := by
  cases target_eq
  rw [Context.enlargeWithParameter?, Suffix.origin_exact base suffix]
  rfl

/-- Forgetting the returned parameter is exactly the existing checked
conversion API, without a second reconstruction. -/
theorem Context.enlargeWithParameter?_conversion (source : Context registry) :
    source.enlargeWithParameter?.map Enlargement.conversion = source.enlarge? := by
  cases origin_eq : source.origin with
  | pack base suffix target_eq =>
    rw [Context.enlargeWithParameter?_eq base suffix target_eq,
      Context.enlarge?_eq base suffix target_eq, ← Conversion.rebuild_result]
    simp only [Option.map_map]
    rfl

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Rebuilt.enlargement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Rebuilt.enlargement

/-- info: 'Hex.RealClosure.Tower.Context.enlargeWithParameter?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlargeWithParameter?

/-- info: 'Hex.RealClosure.Tower.Context.enlargeWithParameter?_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.enlargeWithParameter?_conversion
