/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicyFrontier

/-!
Small merge-gated equivalence canaries for the two policy-frontier
representations.  The fixtures use only opaque arbitrary propagators; no test
depends on rational arithmetic.
-/

namespace Hex.Interval.PolicyFrontierConformance

open Experiment.Propagator
open Experiment.Propagator.PolicyFrontier

def fanout : Comparison := compare fanoutCanary

def dense : Comparison := compare denseCanary

def churn : Comparison := compare churnCanary

#guard comparisonValid fanoutCanary fanout

#guard comparisonValid denseCanary dense

#guard comparisonValid churnCanary churn

-- Both arms implement a maximum-priority policy rather than following the
-- engine queue cursor in FIFO order.
#guard nonFifoChoice fanoutCanary fanout.scan

#guard nonFifoChoice fanoutCanary fanout.indexed

-- The SPEC's small-fixture numbers are exact deterministic counts, not
-- remembered console output.
#guard fanout.scan.work.total == 267

#guard fanout.indexed.work.total == 242

#guard fanout.scan.work.clockSyncSlots == 112

#guard fanout.scan.work.suggestionPruneSlots == 14

-- The dense fixture changes four roots at once.  Five sink applications are
-- inserted once and the remaining fifteen watcher visits are coalesced, but
-- both kinds of dependency work remain in the accounting.
#guard dense.scan.work.dependencyVisits == 20

#guard dense.indexed.work.dependencyVisits == 20

#guard dense.scan.suppressedInsertions == 15

#guard dense.indexed.suppressedInsertions == 15

#guard dense.scan.work.total == 277

#guard dense.indexed.work.total == 250

-- Five sink events and fifteen newly retained split-suggestion events are the
-- exact suffix consumed by the maintained index in the churn fixture.
#guard churn.indexed.work.eventVisits == 20

#guard churn.scan.work.total == 1267

#guard churn.indexed.work.total == 754

#guard churn.scan.work.frontierSlots == 424

#guard churn.indexed.work.frontierSlots == 7

-- Historical tombstones remain backing slots.  Consequently the complete
-- scan does strictly more frontier traversal than the maintained adapter once
-- suggestion churn begins; the shared clock/prune cost is compared separately.
#guard churn.scan.work.frontierSlots > churn.indexed.work.frontierSlots

#guard churn.scan.work.clockSyncSlots == churn.indexed.work.clockSyncSlots

#guard churn.scan.work.suggestionPruneSlots == churn.indexed.work.suggestionPruneSlots

end Hex.Interval.PolicyFrontierConformance
