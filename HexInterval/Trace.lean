/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Action

@[expose] public section

/-!
# Bounded controller traces

This module contains function-independent retained-order and diagnostic-log
contracts. Trace data is operational data, never theorem evidence. In
particular, truncating diagnostics cannot authorize a fact or remove an entry
from the proof chronology.

The byte bound below is an exact bound on retained `UInt8` payload cells. It
does not preempt construction of a callback result, a `Fact`, a `String`, or
another Lean object. Such values already exist when `Log.append` inspects
them. Callbacks therefore remain an explicitly non-preemptible envelope; a
package must enforce its own construction limits before returning. The
controller checks returned counts, retained bytes, and declared logical work
before mutating its log.
-/

namespace Hex.Interval.Trace

/-- One exact position in the authoritative interleaving of fact updates and
program-instance events. -/
inductive Ref where
  | fact (index : Nat)
  | instance (index : Nat)
  deriving DecidableEq, Repr

/-- Authoritative event order, stored separately from role-specific arrays. -/
structure Order where
  chronology : Array Ref
  deriving DecidableEq, Repr

namespace Order

/-- Separate caps for the two authoritative history roles. -/
structure Limit where
  maxFacts : Nat
  maxInstances : Nat
  deriving DecidableEq, Repr

inductive Error where
  | malformed
  | facts
  | instances
  deriving DecidableEq, Repr

/-- Check exact append order and exhaustion of both role-specific arrays. Each
index occurs once, at the only point where it becomes available. -/
def check (order : Order) (factCount instanceCount : Nat) : Bool := Id.run do
  if order.chronology.size != factCount + instanceCount then return false
  let mut nextFact := 0
  let mut nextInstance := 0
  for entry in order.chronology do
    match entry with
    | .fact index =>
        if index != nextFact then return false
        nextFact := nextFact + 1
    | .instance index =>
        if index != nextInstance then return false
        nextInstance := nextInstance + 1
  return nextFact == factCount && nextInstance == instanceCount

def empty : Order := { chronology := #[] }

def counts? (order : Order) : Option (Nat × Nat) := do
  let mut facts := 0
  let mut instances := 0
  for entry in order.chronology do
    match entry with
    | .fact index =>
        if index != facts then none
        facts := facts + 1
    | .instance index =>
        if index != instances then none
        instances := instances + 1
  pure (facts, instances)

/-- Append the exact next fact-history position after validating the retained
chronology and both independent count caps. -/
def appendFact (limit : Limit) (order : Order) (index : Nat) : Except Error Order := do
  let some (facts, instances) := order.counts? | throw .malformed
  if index != facts || limit.maxInstances < instances then throw .malformed
  if limit.maxFacts <= facts then throw .facts
  pure { chronology := order.chronology.push (.fact index) }

/-- Append the exact next instance-history position after validating the
retained chronology and both independent count caps. -/
def appendInstance (limit : Limit) (order : Order) (index : Nat) : Except Error Order := do
  let some (facts, instances) := order.counts? | throw .malformed
  if index != instances || limit.maxFacts < facts then throw .malformed
  if limit.maxInstances <= instances then throw .instances
  pure { chronology := order.chronology.push (.instance index) }

end Order

/-- Independent retained diagnostic limits. `maxBytes` counts payload bytes;
`maxWork` counts controller-declared logical work, not wall-clock time. -/
structure Limit where
  maxEvents : Nat
  maxBytes : Nat
  maxWork : Nat
  maxCode : Nat
  deriving DecidableEq, Repr

/-- One plain diagnostic event. Payload bytes have no semantic or proof
interpretation at this layer. -/
structure Event where
  code : Nat
  payload : Array UInt8 := #[]
  work : Nat := 0
  deriving DecidableEq, Repr

/-- Bounded retained diagnostics. Cached totals make admission constant-time
after inspecting the returned event's already-allocated payload size. -/
structure Log where
  events : Array Event := #[]
  bytes : Nat := 0
  work : Nat := 0
  truncated : Bool := false
  deriving DecidableEq, Repr

namespace Log

/-- Recompute and validate exact totals and every retained event limit. -/
def check (limit : Limit) (log : Log) : Bool := Id.run do
  if limit.maxEvents < log.events.size then return false
  let mut bytes := 0
  let mut work := 0
  for event in log.events do
    if limit.maxCode < event.code then return false
    if limit.maxBytes - bytes < event.payload.size then return false
    if limit.maxWork - work < event.work then return false
    bytes := bytes + event.payload.size
    work := work + event.work
  return bytes == log.bytes && work == log.work

/-- Result of retaining one diagnostic. Truncation is a successful, explicit
loss of diagnostics; malformed input means the preceding log itself was not a
valid snapshot. -/
inductive Append where
  | retained (log : Log)
  | truncated (log : Log)
  | malformed
  deriving DecidableEq, Repr

/-- Transactionally retain one event, or mark the diagnostic stream truncated
without retaining the event. No proof-state object is an argument or result. -/
def append (limit : Limit) (log : Log) (event : Event) : Append :=
  if !log.check limit then
    .malformed
  else if limit.maxEvents <= log.events.size || limit.maxCode < event.code ||
      limit.maxBytes - log.bytes < event.payload.size ||
      limit.maxWork - log.work < event.work then
    .truncated { log with truncated := true }
  else
    .retained
      { events := log.events.push event
        bytes := log.bytes + event.payload.size
        work := log.work + event.work
        truncated := log.truncated }

end Log
end Hex.Interval.Trace
