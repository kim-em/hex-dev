/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ConstructedGather

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

/-- The finite two-stage reader satisfies readiness on its actual path; it
provides no progress at unrelated registry histories. -/
theorem ready_two {registry : Registry} (parent : RealPrefix registry)
    (first second : ConstantKey) (one : parent.Step first)
    (two : (parent.append first one).Step second)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    RealPrefix.Ready (reader parent first second one two) parent [first, second] := by
  have different := append_ne parent first one
  simp [RealPrefix.Ready, freshFirst, freshSecond, reader, offer, different]

/-- Native two-stage construction installs its exact output for later reads. -/
theorem install_two {registry : Registry} (catalog : Catalog registry)
    (parent : RealPrefix registry) (first second : ConstantKey) (one : parent.Step first)
    (two : (parent.append first one).Step second)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    ∃ packet : catalog.Construction (reader parent first second one two) parent [first, second],
      catalog.construct? (reader parent first second one two) parent [first, second] = some packet ∧
      packet.target = (parent.append first one).append second two ∧
      packet.next.lookup packet.target.keys = some packet.target := by
  have built := construct_two parent first second one two freshFirst freshSecond
  have success := catalog.construct?_success (reader parent first second one two)
    parent [first, second] (by rw [built]; rfl)
  obtain ⟨packet, produced⟩ := Option.isSome_iff_exists.mp success
  exact ⟨packet, produced, Option.some.inj (packet.built.symm.trans built), packet.available⟩

/-- An installed complete output returns the original catalog unchanged. -/
theorem installed_reused {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) (target : RealPrefix registry)
    (built : RealPrefix.extend? read parent keys = some target)
    (found : catalog.lookup target.keys = some target) :
    ∃ packet : catalog.Construction read parent keys,
      catalog.construct? read parent keys = some packet ∧ packet.next = catalog ∧
        packet.target = target := by
  exact catalog.construct?_reuse read parent keys target built found

/-- Missing second-stage progress rejects before modifying a catalog. -/
theorem install_missing {registry : Registry} (catalog : Catalog registry)
    (parent : RealPrefix registry) (first second : ConstantKey) (one : parent.Step first)
    (freshFirst : first ∉ parent.keys) (freshSecond : second ∉ (parent.append first one).keys) :
    catalog.construct? (offer parent first one) parent [first, second] = none := by
  exact catalog.construct?_missing (offer parent first one) parent [first, second]
    (missing_second parent first second one freshFirst freshSecond)

/-- Compiled controls cover rational construction, existing-path reuse, later
catalog reads, empty gathering and repeated gathering with a rational owner. -/
def rationalControls : Bool := Id.run do
  let registry : Registry := fun _ => none
  let catalog := Catalog.empty registry
  let parent : RealPrefix registry := .pack (.rational registry)
  let read := fun (p : RealPrefix registry) (k : ConstantKey) => (none : Option (p.Step k))
  let some packet := catalog.construct? read parent [] | return false
  unless packet.next.read parent.finish.signature |>.isSome do return false
  unless (packet.next.construct? read parent []).isSome do return false
  let empty : Tower.Live.Request registry := []
  let some ⟨emptyPacket, _⟩ := empty.gatherConstructed? packet.next read parent | return false
  unless (empty.gatherConstructed? emptyPacket.next read parent).isSome do return false
  let request : Tower.Live.Request registry := [⟨Tower.Context.ofBase parent.finish, {}⟩]
  let some ⟨gathered, _⟩ := request.gatherConstructed? emptyPacket.next read parent | return false
  unless (gathered.next.read parent.finish.signature).isSome do return false
  return (request.gatherConstructed? gathered.next read parent).isSome

/-- info: true -/
#guard_msgs in
#eval rationalControls

end Hex.RealClosure.BaseContext.HistoryTests
