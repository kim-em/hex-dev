/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ConstructedCatalog

public section
namespace Hex.RealClosure.BaseContext.HistoryTests

/-- A test reader offers progress only at its exact requested predecessor. -/
def offer {registry : Registry} (source : RealPrefix registry) (key : ConstantKey)
    (step : source.Step key) (parent : RealPrefix registry) (wanted : ConstantKey) :
    Option (parent.Step wanted) := by
  if path : parent.keys = source.keys then
    have same : parent = source := RealPrefix.keys_inj path
    subst parent
    if equal : wanted = key then
      subst wanted
      exact some step
    else exact none
  else exact none

private theorem append_ne {registry : Registry} (parent : RealPrefix registry)
    (key : ConstantKey) (step : parent.Step key) : (parent.append key step).keys ≠ parent.keys := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [RealPrefix.append_keys, List.length_append, List.length_singleton] at lengths
  exact (Nat.add_one_ne_self _ lengths)

/-- The second offered packet is bound to the newly constructed predecessor,
not to the original seed or an installed target. -/
def reader {registry : Registry} (parent : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first)
    (two : (parent.append first one).Step second)
    (current : RealPrefix registry) (wanted : ConstantKey) : Option (current.Step wanted) :=
  match offer parent first one current wanted with
  | some step => some step
  | none => offer (parent.append first one) second two current wanted

/-- The actual native constructor builds both missing provider stages. -/
theorem construct_two {registry : Registry} (parent : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first)
    (two : (parent.append first one).Step second)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    RealPrefix.extend? (reader parent first second one two) parent [first, second] =
      some ((parent.append first one).append second two) := by
  have different := append_ne parent first one
  simp [RealPrefix.extend?, freshFirst, freshSecond, reader, offer, different]

/-- Repeated keys reuse the same constructed stages without querying a new
provider at an already extended predecessor. -/
theorem duplicate_keys {registry : Registry} (parent : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first)
    (two : (parent.append first one).Step second)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    RealPrefix.extend? (reader parent first second one two) parent [first, first, second, second] =
      some ((parent.append first one).append second two) := by
  have fresh : second ∉ parent.keys ∧ second ≠ first := by
    simpa [RealPrefix.append_keys] using freshSecond
  simp [RealPrefix.extend?, freshFirst, reader, offer,
    RealPrefix.append_keys, fresh.1, fresh.2]

/-- A missing second-stage packet rejects after the first native construction. -/
theorem missing_second {registry : Registry} (parent : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    RealPrefix.extend? (offer parent first one) parent [first, second] = none := by
  have different := append_ne parent first one
  simp [RealPrefix.extend?, freshFirst, freshSecond, offer, different]

/-- No provider is queried for an empty request or an existing key. -/
theorem reuse_existing {registry : Registry} (parent : RealPrefix registry)
    (key : ConstantKey) (present : key ∈ parent.keys) :
    RealPrefix.extend? (fun _ _ => none) parent [key, key] = some parent := by
  simp [RealPrefix.extend?, present]

end Hex.RealClosure.BaseContext.HistoryTests
