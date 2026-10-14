I reviewed the branch through `59a81874a`, which landed while I was reviewing and moves the semantic replay tests into `adapters/`. I could not build anything, run Python, or read the PR body or CI, because those commands were denied. Everything below comes from the source and the retained artifacts.

## Verdict

The core Lean changes look correct. A few report claims and one tooling path must be fixed before merge. **HexRealAlgebraic is close to Phase 3; HexSturm does not meet it yet**, and passing CI will not change that.

## Must fix before merge

1. **The HexSturm conformance module breaks a rule that this PR's own phase bump triggers.** `SPEC/testing.md:44-63` requires every library at `done_through ≥ 2` to open its conformance module with a docstring listing Oracle, Mode, Covered operations, Covered properties and Covered edge cases. This PR raises HexSturm from 0 to 2. The docstring at `conformance/HexSturm/Conformance.lean:19-22` has none of those fields.
   - Public `Sturm.checkCached` has no check anywhere under `conformance/`; neither does the `@[expose]` `normalize`.

2. **`scripts/bench/sturm_semantics_sweep.py:30-38` is broken by the test move.**
   - It still names `HexSturmTheory.Replay.Semantics` and `…SemanticsBaseline`, with `src_dir=conformance` and target `HexConformance`.
   - Those files are now at `adapters/HexSturmTheory/Tests/Replay/` and build through `HexQuerySemantics`, so `probe_source` raises "missing measured probe source".
   - `sturm_mathlib_sweep.py` was updated correctly; this sibling script was missed.

3. **The Bench targets table in `reports/hex-real-algebraic-performance.md:23-26` names five registrations that do not exist:** `runSqrtBranches`, `runRootCases`, `runRealImag`, `runRealBranches` and `runNormBranches`. None of them appear in the source or in any artifact. The table also leaves out the real `runSqrtTotal` and `runProjections`. The count of 67 cases is correct.

4. **The Sturm report's mode-2 claim for the 10 translated `*Bits` registrations goes further than the profiles support.** The report lists "Mode 2, published bits² upper bound" as the strongest justified evidence. It says GMP's multiplication/gcd bounds "cover the phase these profiles exercise".
   - `sturm-translated-infinite.summary.json`: the top self-time leaves are single-limb or linear operations:

     | Leaf | Self % |
     | --- | --- |
     | `mod_1` | 22.3 |
     | `addmul_1` | 20.9 |
     | `divexact_1` | 10.3 |
     | `copyi` | 9.2 |
     | `mul_1` | 4.8 |
     | `toom22` | 1.9 |
     | `mul_basecase` | 1.7 |

     The Hex frames account for only 48.9% inclusive time.
   - The count, certificate, prepared-certificate, field-replay and cached-replay profiles look similar: Toom plus basecase self time is about 5% or less, and no Toom entry appears in their inclusive lists.
   - The observed slopes (β −0.65 to −0.95 against bits²) mean the measured growth is about bits^1.05–1.35. That is below any multiplication algorithm's growth at these sizes, so the measured growth is dominated by linear work.
   - `runInfiniteBits` has no finite endpoints, so the justification "endpoint Horner multiplies growing operands" does not apply to it.
   - `runFractionalBits` has no profile at all.
   - The PR's own rule in `sturm-bit-cost-models.md` says that otherwise "the upper-bound claim is not admitted". Either relabel these as unadmitted candidates, or attribute the `addmul_1` callers with a call-graph profile. The odd-cubic and odd-endpoint families do show general Toom and half-gcd work, so they hold up better.

5. **"Including four rounding timeouts" in the canonical baseline describes the old binary.** That baseline's executable SHA (`90b9693…`) is the same as the "before" arm of the ceiling pairs. The timeouts come from before the ceiling fix, and no full post-fix baseline is retained. The report should say so.

## Smaller accuracy and hygiene issues

- **Hard-arithmetic provenance.** The retained runs came from a dirty `6d78bf3` snapshot that still had the `HEX_REAL_BENCH_DEGREE`/`SHIFT` environment-variable inputs and no expected hashes (`expected_hash_check: unset`). "Current fixed cases have explicit hashes" is true of the source today, not of the runs that produced the table.
- **Phase-2 exit.** `PLAN/Phase2.md` expects follow-up issues, but the tokens say none were filed. The duplicated `a < 0` check in `sqrt?`/`sqrtRoot?` (`HexRealAlgebraic/Roots.lean:126-131`) is still there. Fix it or list it explicitly in the PR.
- **CI bench verify time.** `runHard{Add,Sub}` and their bare arms take about 6.5 s each per call on this host, so about 26 s for one verify pass. No verify wall time is retained. On GitHub runners this probably passes the 30 s soft warning and uses part of the shared 600 s hard cap. Please check it on CI.
- **Proof style.** The `some` branch of `ceil_toReal` relies on Mathlib's internal Rat definition lemmas. It would be sturdier with a named lemma.

## Verified as correct

- **Ceiling.** It is correct and proved against `⌈toReal⌉`. `toRat?` is complete (`toRat?_eq_some`), so a nonrational value's ceiling is floor plus one. `FloorRing` now supplies `ceil` directly with both Galois connections proved, and `ceil_eq` is kept in the companion. The ±1 conformance guard checks real content.
- **`rootCount_sturm`.** It is sound. Squarefreeness is derived from the query domain, and nonzero constants are handled through the empty chain with zero real roots. It needs no caller premises.
- **`query_spec`.** It is correct.
- **Test relocation (after `59a81874a`).**
  - The ordinary tests (`Tests.lean`, Accepted/Rejected/Baseline) are explicit roots of `HexSturmTheoryTests`.
  - The semantic guards build with `HexQuerySemantics`; both targets are in CI's `HEX_LIB_TARGETS`.
  - No ordinary companion test imports the adapters, and the banned `conformance/HexSturmTheory` directory is gone.
- **Oracle centering.** `center_query` shifts by the integer nearest the roots' mean, which preserves the root sum, the domain and the endpoint guards. It handles both precision signs, applies the same way to every finite row, and the certificate identities are still checked on the original inputs. The unit tests cover a 2²⁰⁴⁸ offset, rejected domains and fractional endpoints.
- **Numbers I recomputed from the artifacts all match the reports:**
  - the hard-arithmetic medians and ranges;
  - the ceiling pairs (408–589 ms before, 9.65–15.21 µs after, one hash);
  - the comparison medians (0.420/38.991, 20.814/250.732, qqbar 7.451/7.436, protocol 6.375/6.358 µs);
  - all eight arithmetic profile rows;
  - the array and sort verdicts;
  - the prepared-query degree results (−0.066/−0.077);
  - the mode-1 Sturm families: InitialWide −0.064, ClearingWide −0.094, RetargetWide −0.019, EmbedSparse +0.006.
- **One understatement.** The report says the qqbar arms were "not adjacent" to the real arm. In fact they ran inside the same alternating ABCD/DCBA blocks; they just weren't next to the smart-compare arm. This is not an overclaim.
- **Dependency eligibility is stated accurately.**
  - HexPoly is at 4, and HexRealRoots, HexNumberField and the Mathlib-side dependencies are at 7, so both cores are eligible for Phase 3.
  - The companions must wait for their cores to reach 3; for them, Phase 3 is just a green build.

## Phase 3 answer

- **HexRealAlgebraic: close.**
  - The module has the contract labels, the qqbar/FLINT oracle is wired in `run_oracles.sh`, and fixtures, `Checks` and `ReprChecks` exist.
  - Its operations list should be brought in line with the SPEC: complex `normSq`/`abs`, `re`/`im`, the `RealAlgebraicPoly` root-set API, `ZPoly.realAlgebraicRoots` and `Repr` are exercised but not declared. I did not audit "≥3 cases per operation" exhaustively.
- **HexSturm: no.** It needs the docstring contract (with "Oracle: none" if that is the intent), coverage for `checkCached`, and a check of `normalize` against the SPEC.
- **Companions:** they follow their cores.

## Remaining Phase-4 work, not blocking this PR

- No mode or budget for any HexRealAlgebraic operation, and no `phase4` block or owned-SPEC section for it.
- The compare/separation, rounding, sqrt and `ofRat` sweeps.
- Real root and leaf parameter families; `runExactifyRoots` and `runLeafChecks` are already labelled as controls.
- The `runSigns` failure (+0.465).
- The 33.8 GB peak memory on the prepared-query value path.
- The neg/inv/ofRat re-exactification cost in HexNumberField.
- Comparator reconciliation.
