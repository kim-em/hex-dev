**Accomplished**

- Reviewed the current M1/coreLiftData migration question against the cited
  `PartitionRefinement`, `Basic`, `FactorSoundness`, `LiftBridge`, and
  `UFDPartition` source.
- Confirmed the complete coreLiftData endpoint takes a free `trueSupports`
  family and per-support mod-p data.
- Confirmed the existing `liftedTrueSupports.ncard_eq_normalizedFactors_card`
  is tied to `RepresentsIntegerFactorAtLift`, while the reusable mod-p package
  exposes `ModPSubsetPartitionHypotheses`, `modPFactor_index_cover`,
  `unique_modPFactorSubset_up_to_associated`, and lifted subset transport lemmas.

**Current frontier**

- Best path appears to be an M1-native support family defined as the image of
  representing mod-p subsets under `liftedSubsetOfModPSubset`, with a small
  mod-p support-family cardinality lemma modeled on the old lifted count proof.
- The count proof should use `unique_modPFactorSubset_up_to_associated` directly
  for well-definedness/injectivity rather than deriving association through
  disjointness.

**Next step**

- Implement local helper lemmas in `PartitionRefinement.lean` or a narrow
  non-`Basic.lean` module: mod-p image support family cover/disjoint/nonempty,
  cardinality equals normalized factor count, and support-product/index bridges
  into the coreLiftData endpoint.

**Blockers**

- External Claude second-opinion wrapper was launched but had not returned by
  the time of this source review; network/tool restrictions may prevent a
  substantive external response.
