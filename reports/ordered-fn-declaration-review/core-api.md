# OrderedFn computational API decisions

The five production computational modules are byte-identical to their individual
[source assessment](computational.md) and [manifest](manifest.json), at
`79b991882a486a8c8d05fd26aaf1656358834b7e`. This adopts their proof/API judgments
for the computational library, including the public interfaces and private
termination instance discussed below. It does not complete Phase 6: the four
flagged regressions in the [retained comparison](../bench-results/ordered-fn-regression-followup/README.md)
remain unresolved, and no further unchanged comparison is permitted.

## Retention decisions and the two reference environments

The [original 49-row table](zero-references.md) contains ten computational rows
and 39 companion rows. The companion's later 33-row zero-reference set is not
the complement of the computational set: six companion declarations gained
named users in the larger environment. Subtracting 33 from 49 would therefore
miscount the core's share. The decisions below cover the actual ten core rows.
The wider [v7 capture](current/README.md) retains its own source, environment,
coverage and exclusion boundaries; its named-user counts are observations of
that environment, not claims about the current repository or runtime use.

| Declaration | Named users in retained v7 | Decision and API reason |
| --- | ---: | --- |
| `Real.Extension.ext_iff` | 0 | Retain the bidirectional storage equality interface. Clients can reduce extension equality to equality of canonical fractions without comparing the registration's erased proof fields or unfolding its constructor. |
| `Real.Extension.val_C` | 0 | Retain the simp projection for the coefficient constructor; it exposes the native representation needed by normalization and semantic constructor proofs. Definitional reduction can eliminate the named reference. |
| `Real.Extension.val_X` | 0 | Retain the matching simp projection for the formal generator. It states a different constructor equation from `val_C`, rather than duplicating its domain. |
| `Real.Extension.transport_val` | 0 | Retain the literal-fraction preservation law for changing registrations. Its deliberately weak conclusion avoids inventing same-subject or order-preservation evidence. |
| `orderSign_range` | 0 | Retain trichotomy of the executable integer result under minimal decidable comparison assumptions. It exposes a representation invariant without pretending those assumptions supply a linear order. |
| `Infinitesimal.sign_range` | 0 | Retain range preservation from a three-valued predecessor sign. This is useful independently of the companion's stronger order-correctness theorem and keeps its premise explicit. |
| `Oracle.Bounds.width_neg` | 0 | Retain exact width preservation as simp normalization for negated enclosures. External error-bound proofs should not need to unfold both rational endpoints. |
| `Oracle.Bounds.width_add` | 1 | Retain width additivity for composed enclosure estimates. The retained named user is `Oracle.Contains.add_converges`; this is a proof client, not a runtime performance result. |
| `Real.requestWidth_of_nonpos` | 0 | Retain the nonpositive-request normalization to width one. Users must be able to explain coarse requests without claiming a zero-width approximation succeeds. |
| `accessibleWf` | 0 | Keep private. The search termination elaborator uses its accessible-subtype well-founded relation; the reference model may unfold it rather than retain a named edge. Making it public adds no useful search contract, and deleting it breaks the declared recursion interface. |

The companion separately adopts its own [33 public decisions](theory-acceptance.md).
No discovered caller is claimed for a zero-user row. An exported characterization,
simp rule or elaboration instance can have a justified purpose without a named
term edge. Conversely a reference supplied by evidence does not establish
production use. The computational assessment already treats every handwritten
nontrivial declaration, derived instances and fields at its pinned source;
these retention decisions supplement that assessment rather than replacing it
with reference counts.

## Imports, automation and semantic hypotheses

The actual public umbrella exports `Search`, `Oracle`, `Real`, `Infinitesimal`
and `Extension`. Their direct imports are:

| Module | Direct imports and purpose |
| --- | --- |
| `Search` | `Init`, for accessible recursion and the actual trial search. No interval, polynomial or semantic theory input is required. |
| `Oracle` | `Init.Data.Rat.Lemmas` and `Init.Data.Dyadic.Basic`, for rational bound arithmetic and exact dyadic conversion. The dyadic constructor is a public adapter; it does not import HexInterval. |
| `Real` | `Search`, `Oracle` and `HexRationalFn`, for exact Horner bounds and search on canonical fractions. |
| `Infinitesimal` | `HexRationalFn`, for canonical fraction storage and the first nonzero coefficient computation. It does not import real-provider refinement. |
| `Extension` | `Real`, for fixed-provider registration and the actual native field operations. |

This accepts the computational import structure as appropriate to the declared
API. The shared sign split described in [quality.md](quality.md) resolves a
companion import concern; it does not add a computational dependency. The core
imports neither its Theory companion nor Mathlib/Tau Ceti. The independent
import-DAG checks remain required for later source changes.

The [automation assessment](quality.md) applies to these unchanged source bytes.
Exact endpoint/storage/request normalizations use simp or ext. Search equations
and semantic transfers stay explicit: rewriting recursive search globally would
expose accessibility evidence, and automation cannot supply the missing provider
laws. Core intervals establish endpoint order and rational width, not semantic
containment or convergence. Registration supplies executable providers and erased
progress evidence, not a transcendence proof. The companion's `Valid`/`OrderValid`
interfaces supply the corresponding semantic hypotheses. Scoped infinitesimal
relations do not install an unproved global ordered field.

## Verification scope and remaining acceptance

The source review and both compiler captures remain immutable. The five module
hashes agree with the original manifest, and the retained v7 rows match every
declaration and count in the table above. The v7 archive checker verifies its
source/complete tags, graph data, declared client coverage and axiom inventory.
No fresh capture or timing collection is needed to adopt judgments about these
unchanged computational sources. Current-source mode can correctly refuse a
later dependency/import environment without invalidating the retained archive.

This settles the computational API-retention and direct-import judgments stated
here. It is not a new whole-environment lint or native performance pass. Existing
lint, manual and kernel checks retain their recorded scopes. The computational
library remains at Phase 5 until its applicable regression and remaining final
phase checks are satisfied. In particular, the four median-rule regressions are
not erased by proof erasure, source identity, comparison improvements elsewhere,
or the companion's independent Phase 7.
