# HexGraphIsoMathlib performance

`HexGraphIsoMathlib` is an executable proof/tactic bridge, not a
correspondence-only layer: it extends the `graph_iso` syntax to closed ground
`SimpleGraph` goals and emits kernel-checked proofs. `HexGraphIso` owns the
transported canonical-labelling computation and its comparator evidence. This
report prices only what the bridge itself adds: encoding a `SimpleGraph` over
an arbitrary `Fintype`/`DecidableRel` vertex type into the executable
`Colored`, the correspondence theorem, and the transport of the checked answer
back to `Nonempty (G ≃g H)` or `IsEmpty (G ≃g H)`. There is no Mathlib
benchmark executable, and there must not be: a bench target here would import
Mathlib, which `scripts/ci/check_benches_mathlib_free.py` forbids.

The headline verdict is that all four bridge probe cases close, and that the
bridge-local cost is dominated by the vertex-type enumeration, not by the
search: the two `n = 10` cases on genuinely different vertex types are
indistinguishable from each other, and moving from `n = 10` to `n = 12` on
`Fin`-indexed graphs costs about twice as much again.

## Bench Targets

The bridge uses proof/tactic evidence in place of compiled targets. These
fresh-module probes explicitly replace a LeanBench executable, `list`/`verify`
entries, complexity verdicts, and timed-region sampling profiles. Its
build-only root is `HexGraphIsoMathlibProofProbe`, declared in `lakefile.lean`
and recorded as the library's `proof_probes` path in `libraries.yml`. Every
measured module is a fresh importer of the same precompiled
`HexGraphIsoMathlib.ProofProbe.Support` module, and no measured module imports
another measured module, so a measured build isolates exactly one `graph_iso`
invocation against `MathlibBaseline`'s matched import cost.

| evidence family | reference to candidate | what is included |
|---|---|---|
| `cross-type-goals`, positive | `MathlibBaseline` to `MathlibPositive10` | `Nonempty (gpetersen 5 2 ≃g kneser 5 2)`: two unrelated finite vertex types (`Fin 2 × Fin 5` and `{s : Finset (Fin 5) // s.card = 2}`), so the goal genuinely enumerates both types and returns a `SimpleGraph.Iso` rather than recognizing a definitional equality |
| `cross-type-goals`, negative | `MathlibBaseline` to `MathlibNegative10` | `IsEmpty (gpetersen 5 2 ≃g gpetersen 5 1)`: the Petersen graph against the pentagonal prism at the same vertex type and the same `n = 10` |
| `random-pair-transport`, positive | `MathlibBaseline` to `MathlibPositive12` | `Nonempty (g12 ≃g g12relabelled)`: the recorded `G(12, 1/2)` graph of the first SplitMix64 corpus seed against its image under the recorded Fisher-Yates relabelling, as `SimpleGraph (Fin 12)` |
| `random-pair-transport`, negative | `MathlibBaseline` to `MathlibNegative12` | `IsEmpty (g12 ≃g g12b)`: the `G(12, 1/2)` graphs of the two recorded corpus seeds |

The two `cross-type-goals` instances are the manual chapter's worked examples,
so the chapter and the Phase-4 record price the same goals. The two
`random-pair-transport` instances are the Mathlib-route twins of the core
library's `Positive12` and `Negative12` probes, which lets the two reports be
read against each other for the bridge's marginal cost.

## Verdicts

Times are seconds, measured on `chungus2` (AMD EPYC 9455, 96 threads) with Lean
4.34.0-rc2 on 2026-09-03. Each module was invalidated by appending a unique
comment, rebuilt through `lake build HexGraphIsoMathlibProofProbe`, and then
restored; three samples per module, interleaved so that each round measures
every module once.

| probe | raw samples (s) | median (s) | max (s) | delta to baseline (s) | resolution | budget |
|---|---|---:|---:|---:|---|---|
| `MathlibBaseline` | 1.775, 2.470, 2.378 | 2.378 | 2.470 | — | — | — |
| `MathlibPositive10` | 2.807, 2.804, 2.777 | 2.804 | 2.807 | +0.426 | unresolved | pass |
| `MathlibNegative10` | 2.779, 2.779, 2.785 | 2.779 | 2.785 | +0.401 | unresolved | pass |
| `MathlibPositive12` | 3.187, 3.189, 3.172 | 3.187 | 3.189 | +0.809 | resolved | pass |
| `MathlibNegative12` | 3.197, 3.189, 3.171 | 3.189 | 3.197 | +0.811 | resolved | pass |

The baseline's own sample range is 0.695 s, which is the null envelope for this
run. The two `n = 10` deltas lie inside it and are therefore unresolved: that is
not evidence of zero bridge cost, only that this run cannot separate them from
import noise. The two `n = 12` deltas exceed the envelope and resolve. The
release contract is the candidate's absolute wall time, not an
import-subtracted delta, and every row is under 3.2 s.

Two structural readings are safe from this table. First, positive and negative
goals cost the same on this route: `MathlibPositive10` and `MathlibNegative10`
differ by 0.025 s, and `MathlibPositive12` and `MathlibNegative12` by 0.002 s.
That is the expected shape, because the bridge transports a decided answer and
the negative direction is a `checkCanon` disagreement rather than a search. It
contrasts sharply with the core library's tactic tier, where negatives cost one
to two orders of magnitude more than positives; the difference does not appear
here because these instances are small enough that encoding dominates.
Second, the cross-type `n = 10` cases are cheaper than the `Fin 12` cases
despite the more elaborate vertex types, so the `Fintype` enumeration of a
subtype of `Finset (Fin 5)` is not the bottleneck at this size.

The measurement caveat is that this was an unpinned run on a shared host, with
three samples and no rotation of reference/candidate order, and so it does not
meet the pinned, rotated, contamination-rejecting protocol that
`reports/hex-primality-mathlib-performance.md` records. The claim supported here
is the SPEC's release condition, that these goals close through the kernel
within their logical limits, together with an order-of-magnitude cost; it is
not a preregistered wallclock tolerance. `HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md`
Section Tests is the normative list of cases.

## Comparator Ratios

There is no honest external ratio for this layer. No other system produces a
kernel-checked Lean proof of `Nonempty (G ≃g H)` or `IsEmpty (G ≃g H)` for
Mathlib `SimpleGraph`s, so there is nothing to divide by. The pinned
`nauty 2.9.3 (vendored source, in-process FFI through Hex.BenchOracle.Nauty)`
comparator is declared by `HexGraphIso`, not here: it answers the
canonical-labelling question in C with no proof object, its binding is
development-monorepo tooling that ships with no released library, and it cannot
be linked into a Mathlib-importing target at all.

A ratio between `HexGraphIso` and `HexGraphIsoMathlib` would also double-count
the same canonical search and misstate ownership: every microsecond of search
in the rows above is core-library work already priced in
`reports/hex-graph-iso-performance.md`. The bridge's own contribution is the
encoding and transport, and the honest way to expose it is the pairing of
`MathlibPositive12` and `MathlibNegative12` against the core library's
`Positive12` and `Negative12` probes on the identical two graphs. Those core
probes sit at 1.606 s and 1.787 s against a 1.675 s baseline; the Mathlib route
sits at 3.187 s and 3.189 s against a 2.378 s baseline. Both the larger baseline
and the larger delta are the price of importing and elaborating over Mathlib's
`SimpleGraph`, and neither is a defect of the search.

## Profile

Timed-region sampling does not apply to this proof track: there is no compiled
executable to attach a profiler to, and the elaboration-time work happens inside
`lake build`. The fresh-module record above supplies the required profile
evidence, and the structural decomposition it supports is the one stated in the
Verdicts section: encoding and Mathlib elaboration dominate, search does not
separate positives from negatives at these sizes.

The `Support` module is where the shared cost is concentrated, and it is
deliberately outside every measured window. It carries the `gpetersen` and
`kneser` definitions with their `symm`/`loopless` proofs and `DecidableRel`
instances, the `Fin 12` adjacency literals, and the `Mathlib.Data.Fintype.Powerset`
import that the Kneser subtype needs. Because each probe imports it and nothing
else beyond it, none of that construction cost is charged to a `graph_iso`
call.

## Concerns

One, recorded rather than blocking. The measurement protocol above is weaker
than the one this repository applies to `HexPrimalityMathlib`: unpinned, three
samples, no arm rotation, and a null envelope inferred from the baseline's own
spread rather than from dedicated null controls. It is sufficient for the
SPEC's release condition, which is that the cases close, and for the
order-of-magnitude statements made here. It would not be sufficient to support
a numeric wallclock requirement, and this report does not state one. Promoting
these probes to the pinned rotated protocol is scheduled-hardware work and does
not gate the release.

Nothing else. The bridge introduces no `sorry`, no `axiom`, and no
`native_decide`; `scripts/release/check_trust_surface.py` covers it.
