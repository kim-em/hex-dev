/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Scale

/-!
Conformance checks for deterministic centered-checker scaling workloads.
Every accepted fixture is checked at its independently recomputed exact lookup
budget and rejected one step below it.
-/

namespace Hex.Interval.ScaleConformance

open Experiment.Scale

private def hasCounts (nodes facts result : Nat) : Option Workload → Bool
  | none => false
  | some workload =>
      workload.certificate.program.length == nodes &&
        workload.certificate.facts.length == facts &&
        workload.certificate.result == result

private def hasLookupCounts (expected : LookupCount) : Option Workload → Bool
  | none => false
  | some workload => certificateLookupCounts? workload.certificate == some expected

-- Node-only growth changes the whole-program scan but not indexed lookup work.
#guard checksSome (deadNodes? 9)
#guard checksSome (deadNodes? 500)
#guard checksSome (deadNodes? 2000)
#guard hasCounts 500 10 9 (deadNodes? 500)
#guard hasCounts 2000 10 9 (deadNodes? 2000)
#guard hasLookupCounts
  { program := 44, source := 1, edge := 1, prior := 18, result := 10 }
  (deadNodes? 2000)
#guard (deadNodes? 8).isNone

-- Adjacent transports retain every added fact and have exact linear lookup
-- work. Only a positive odd tail ends back at the caller-selected product.
#guard adjacentLookupSteps 491 == 1544
#guard checksSome (adjacent? 1)
#guard checksSome (adjacent? 41)
#guard checksSome (adjacent? 491)
#guard hasCounts 9 500 499 (adjacent? 491)
#guard hasLookupCounts
  { program := 44, source := 1, edge := 491, prior := 508, result := 500 }
  (adjacent? 491)
#guard (adjacent? 0).isNone
#guard (adjacent? 2).isNone

-- Repeated references to fact eight have the same certificate dimensions as
-- the adjacent chain but exact quadratic reverse-list lookup work.
#guard farLookupSteps 491 == 121839
#guard checksSome (far? 1)
#guard checksSome (far? 41)
#guard checksSome (far? 491)
#guard hasCounts 9 500 499 (far? 491)
#guard hasLookupCounts
  { program := 44, source := 1, edge := 491, prior := 120803, result := 500 }
  (far? 491)
#guard (far? 0).isNone

-- Irrelevant facts after the selected result are still replayed. They add one
-- source-table lookup apiece while the result index stays fixed.
#guard sourcePadLookupSteps 490 == 564
#guard (sourcePad 0).checksBoundary
#guard (sourcePad 40).checksBoundary
#guard (sourcePad 490).checksBoundary
#guard hasCounts 9 500 9 (some (sourcePad 490))
#guard hasLookupCounts
  { program := 44, source := 491, edge := 1, prior := 18, result := 10 }
  (some (sourcePad 490))

end Hex.Interval.ScaleConformance
