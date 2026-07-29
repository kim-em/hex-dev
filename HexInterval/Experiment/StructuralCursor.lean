/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

@[expose] public section

/-!
# Generic bounded structural cursor

This module contains only the append-stable cursor state machine.  A consumer
supplies the type and lookup function for structural inputs, so propagator
identifiers and interval facts do not enter this layer.
-/

namespace Hex.Interval.Experiment.StructuralCursor

structure Size where
  nodes : Nat := 0
  equalities : Nat := 0
  applications : Nat := 0
  deriving DecidableEq, Repr

def Size.le (left right : Size) : Bool :=
  left.nodes <= right.nodes &&
    left.equalities <= right.equalities &&
      left.applications <= right.applications

def Size.delta (base limit : Size) : Nat :=
  (limit.nodes - base.nodes) +
    (limit.equalities - base.equalities) +
      (limit.applications - base.applications)

structure View where
  programVersion : Nat
  size : Size
  deriving DecidableEq, Repr

structure Cursor where
  programVersion : Nat
  base : Size
  limit : Size
  offset : Nat := 0
  epoch : Nat := 0
  visits : Nat := 0
  deriving DecidableEq, Repr

def Cursor.start (view : View) : Cursor :=
  { programVersion := view.programVersion
    base := {}
    limit := view.size }

def Cursor.exhausted (cursor : Cursor) : Bool :=
  cursor.offset == cursor.base.delta cursor.limit

def Cursor.validFor (cursor : Cursor) (view : View) : Bool :=
  cursor.programVersion <= view.programVersion &&
    cursor.base.le cursor.limit &&
      cursor.limit.le view.size &&
        cursor.offset <= cursor.base.delta cursor.limit

structure Limits where
  maxVisits : Nat
  batchSize : Nat
  deriving DecidableEq, Repr

inductive Error where
  | staleSnapshot
  | invalidCursor
  | cursorNotExhausted
  deriving DecidableEq, Repr

inductive Step (Input : Type) where
  | yielded (inputs : Array Input) (cursor : Cursor)
  | exhausted (cursor : Cursor)
  | resourceLimit (cursor : Cursor)
  | invalidCursor
  deriving Repr

def inputsFromLoop? (inputAt? : Cursor -> Nat -> Option Input) (cursor : Cursor) :
    Nat -> Nat -> Array Input -> Option (Array Input)
  | _, 0, inputs => some inputs
  | offset, count + 1, inputs => do
      let input <- inputAt? cursor offset
      inputsFromLoop? inputAt? cursor (offset + 1) count (inputs.push input)

def inputsFrom? (inputAt? : Cursor -> Nat -> Option Input) (cursor : Cursor)
    (offset count : Nat) : Option (Array Input) :=
  inputsFromLoop? inputAt? cursor offset count #[]

/-- Take one deterministic batch from a frozen epoch.  Visit exhaustion is
checked before the first structural lookup and leaves the cursor unchanged. -/
def take (inputAt? : Cursor -> Nat -> Option Input)
    (limits : Limits) (view : View) (cursor : Cursor) : Step Input :=
  if limits.batchSize == 0 then
    .invalidCursor
  else if !cursor.validFor view then
    .invalidCursor
  else
    let total := cursor.base.delta cursor.limit
    if total == cursor.offset then
      .exhausted cursor
    else
      let available := limits.maxVisits - cursor.visits
      let count := Nat.min available (Nat.min limits.batchSize (total - cursor.offset))
      if count == 0 then
        .resourceLimit cursor
      else
        match inputsFrom? inputAt? cursor cursor.offset count with
        | none => .invalidCursor
        | some inputs =>
            .yielded inputs
              { cursor with
                offset := cursor.offset + count
                visits := cursor.visits + count }

/-- Renew an exhausted cursor over exactly the appended structural suffix. -/
def renew (view : View) (cursor : Cursor) : Except Error Cursor := do
  if view.programVersion < cursor.programVersion then
    throw .staleSnapshot
  if !cursor.validFor view then
    throw .invalidCursor
  if !cursor.exhausted then
    throw .cursorNotExhausted
  if view.size == cursor.limit then
    pure cursor
  else
    pure
      { programVersion := view.programVersion
        base := cursor.limit
        limit := view.size
        offset := 0
        epoch := cursor.epoch + 1
        visits := cursor.visits }

end Hex.Interval.Experiment.StructuralCursor
