# Runtime terminal review repair

## Accomplished

- Added an early dedicated refusal for restarted children whose exact ancestor
  chain retained a runtime equality that proof replay would inherit while the
  runtime equality arena resets.
- Revalidated retained trees and exact current fact versions before refutation
  schema decoding/callbacks, and used the retained source program in the
  theorem context.
- Added conformance for hazardous parent equality, safe pre-event split
  restart, sibling/cross-lineage runtime refusal, genuine stale versions,
  decoder/callback rejection, target resource refusal, input mismatch, private
  construction forms, and exact guarded axiom reports.
- Clarified checked-token, exact-registry, controller-recheck, and assembly
  generation claims in the module and SPEC.
- Verified focused conformance, the Mathlib umbrella, `HexConformance`, DAG
  unit/static checks, trust-token scans, and whitespace checks.

## Current frontier

Target/refutation terminals and safe child restart are review-hardened.

## Next step

Reconcile the equality-arena restart contract before implementing general
split terminal integration.

## Blockers

The underlying split limitation remains: proof children inherit parent
equality identities while runtime children reset their equality arena. The
adapter now refuses this condition at sibling restart instead of allowing a
lineage that can only fail later during quotation/replay.
