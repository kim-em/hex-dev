# issue #8519 — van Hoeij L'=W lattice adequacy (session 1)

## Accomplished

- **Premise correction (posted to #8519):** the plan's "empirically reconciled"
  claim about `choosePrimeData? core` + `toMonicLiftData` was false. Compiled
  probe: for `core = (2x+1)(x²+x+1)`, `p = 5`, `lc = 2 ≢ 1 (mod 5)`, the Hensel
  seeds (mod-p factors of the *scalar* monicization) do not multiply to
  `(toMonic core).monic` (the *dilation* monicization) mod p; the lift
  invariant fails and `factorFastCoreWithBound` returns `none` on a trivially
  reducible input. In that regime the CLD lattice has no semantic content and
  neither sorry is provable as stated.
- **Executable coherence fix** (plan option (c), classical-tier precedent,
  commit 3157b3d3): lattice tier selects `ZPoly.toMonicPrimeData?`;
  `bhksRecoverClassified` / `bhksSingleAllOnesPartition` build the CLD lattice
  on `(toMonic f).monic` (matching the already-monic-keyed `cldCoeffFloor`);
  `factorFastPrecisionCap` gains `cldCoeffFloor core`, `dFCB core`, `dFCB m`
  max-components. Probe now shows the invariant holds and the fast core
  factors the previously-broken input.
- **LatticeTier re-key** (commit fb6a5002): statements on the
  `toMonicPrimeData?` witness; arm-1 descends through new
  `zpolyIrreducible_of_toMonicMonic_irreducible` +
  `squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch`.
  `HexBerlekampZassenhausMathlib` green with exactly the two known sorries.
- **Acceptance floor strengthened** (in flight): `fastCoreFloor core :=
  max (cldCoeffFloor core) (max (dFCB core) (dFCB (toMonic core).monic))`
  replaces the gate, so accepted precisions clear both the CLD column
  adequacy AND the Mignotte recovery bounds — what the partition producers
  need at the arm-2 witness precision.

## Key discovery

The sorry-free `W ⊆ L'` machinery deleted in 6bf20977 (#8411) — Klüners
Lemma 1 (`mem_prefixSubmodule_of_normSq_le`), `CutProjectionHypotheses`,
`cutProjectionHypotheses_of_shortVectors`, `supportShortVectorData_of_recoveredLift`
(monic regime — applies verbatim now that the lattice polynomial is monic),
the signature-class/RREF column theory, and the count bridges
(`supportPartitionByMinColumn_length_eq_normalizedFactors_card`,
`bhksEquivalenceClassIndicators_size_eq`) — is extracted at /tmp/deleted-bhks
and covers nearly the whole route for both sorries. Port plan being prepared
(adapt `Matrix.rref` → `Matrix.rowReduce`, instantiate the deleted
`RecoveredLift` from the current `RecoveredAtLift` + toMonic lift lemmas).
`recoveredLift_aggregate_residue` uses `recovered_eq` only to derive the
mod-p^a congruence, and Mignotte-at-k' is supplied by the new gate.

## Current frontier

Executable rebuild with `fastCoreFloor` in flight; #guards at the floor
boundary (`cldGuardF` at B=32) may need adjusting to the new floor value.

## Next step

1. Green the floor-gate change; full-target + conformance run; commit.
2. Resurrect the deleted machinery into
   `HexBerlekampZassenhausMathlib/LatticeAdequacy.lean` per the port plan.
3. Wire `hclasses` (arm-3) and the arm-2 count through it.

## Blockers

None currently; the deep work is volume, not obstruction.
