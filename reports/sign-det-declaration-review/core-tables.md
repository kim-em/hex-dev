# Sign-determination support induction and sparse tables

This assessment covers 42 named declarations in four computational modules,
the two reduction equality instances and source structure fields. It is a
partial core review. Root-set coverage and interpreted ordering for supplied
root-list extraction remain the separate owner exports requested through
[#10331](https://github.com/kim-em/hex-dev/issues/10331#issuecomment-6126809036).
These table representation lemmas do not replace those exports.

The [source bindings](core-tables-manifest.json) identify exact reviewed bytes.
The runtime producer/checker definitions are unchanged. Named replay acceptance
facts replace Boolean unfolding in the support induction, and positive sparse
lookup has a full membership characterization used by the existing public
positive-membership theorem.

## Induction

| Declaration | Assessment |
| --- | --- |
| `Observations` | Finite sign words retain width and ternary coordinates; repeated observations preserve their multiplicities. |
| `Observations.take` | Prefix restriction preserves coordinates and truncates width with min, including empty prefixes and overlong requests. |
| `Observations.drop` | Suffix restriction preserves coordinates and subtracts the requested width, including empty suffixes. |
| `leaf_covers` | The private case split proves coverage of the fixed empty/singleton supports; it uses actual width and ternary premises, not root semantics. |
| `Replay.Interprets` | Every node interprets the same finite observations restricted by the actual balanced query split. Neither correct support nor recovered counts is assumed. |
| `Replay.support_counts` | Child coverage precedes the parent count recovery. The supplied recovery theorem must require checked systems, candidate coverage and exact moments. The leaf proof consumes check_leaf instead of Boolean checker associativity. |
| `Replay.support_complete` | Specializes the same induction to the computational count-recovery proof; semantic consumers separately derive its moment interpretation. |
| `Replay.support_iff` | Combines coverage and absence of spurious positive columns to characterize support exactly. Repeated observations affect counts, not membership. |

## Table

| Declaration | Assessment |
| --- | --- |
| `SignTable` | Private construction retains ordered rows, positive counts, ternary width and distinct conditions. These representation invariants alone establish no root-set coverage. |
| `SignTable.empty` | The empty sparse representation gives zero lookup everywhere. It describes a root-free domain only with a separate semantic proof. |
| `SignTable.count` | Literal lookup returns the unique stored natural count or zero for an omitted condition; no negative-count cast occurs. |
| `SignTable.empty_count` | The empty lookup equation is a terminating simp normalization for arbitrary conditions, including wrong widths. |
| `System.tableRows` | Filters strictly positive coordinates in existing index order before the exact natural cast. Checked nonnegativity and distinctness justify the table adapter. |
| `System.count` | Exposes the same sparse lookup without constructing an opaque validated table. Its definition alone carries no acceptance guarantee. |
| `System.tableRows_valid` | Uses the named checked-column projection and strict-positive pruning to preserve widths/sign codes and positive natural counts. |
| `System.tableRows_distinct` | Literal column distinctness and distinct selected indices prevent duplicate sparse keys. It does not deduplicate malformed supplied systems silently. |
| `SignTable.ofSystem` | Constructs the private representation from arbitrary accepted integer-system guards. Root meaning still requires complete recursive replay and interpreted moments. |
| `lookup_member` | The private recursive lookup proof needs distinct first coordinates, preventing an earlier duplicate key from shadowing the supplied row. |
| `SignTable.count_mem` | Returns each literal stored count using the structural distinctness proof. It imposes no coefficient or root hypotheses. |
| `SignTable.count_omitted` | Absent keys return zero. This handles conditions of any supplied shape without a sentinel or saturation conversion. |
| `SignTable.count_pos` | Full equivalence between positive lookup and literal stored membership uses positive rows and unique lookup. It remains explicit rather than a global existential simp rewrite. |
| `SignTable.mem_of_count_pos` | Preserves the existing public conclusion as the forward direction of count_pos; current selected-root clients keep their statements. |
| `Replay.table` | Extracts an opaque sparse table only from full accepted replay. Its arity is tied to the original query length; semantic interpretation remains separate. |
| `Replay.table_rows` | Characterizes exact row preservation at the private table boundary without making users unfold extraction. |
| `Replay.table_lookup` | Connects validated table lookup to literal local-system lookup for every condition. |
| `Replay.count_table` | Exact counts and complete interpreted support establish every lookup, including omitted conditions. It deliberately retains both hypotheses. |
| `Replay.table_count` | Uses the actual finite support induction to derive those hypotheses from accepted replay, well-formed observations and moment interpretation. |

## TableProducer

| Declaration | Assessment |
| --- | --- |
| `buildTablePrepared` | Runs the existing checked replay producer and preserves its diagnostic errors; successful output is the exact table extracted from accepted replay. |
| `buildTablePrepared_ofReplay` | Characterizes that successful extraction without replacing the actual producer equation or replay witness. |
| `determinePrepared` | The total wrapper preserves successful tables. Its diagnostic panic/default branch is proved unreachable under the companion lawful-interpretation hypotheses; arbitrary supplied operations need the Except API. |
| `determinePrepared_ofBuild` | The success characterization keeps the actual build equation and every stored count; it does not prove that arbitrary operations succeed. |
| `determine` | Preparation rejection alone returns none. Valid preparation selects the total prepared API with original query order and exact sparse counts; producer totality needs the stated companion laws. |

## Reduction

| Declaration | Assessment |
| --- | --- |
| `ReductionStep` | The original positional index, next accumulator and literal quotient/scales are all retained and independently replayed; equality is literal certificate equality. |
| `Reduction` | An ordered step chain declares one final query polynomial. Literal equality includes both steps and result; it does not quotient equivalent witnesses. |
| `factors` | Repeats each indexed query according to its exponent, preserving original positions. Zip truncation and arbitrary exponents are safe only with the outer shape/range checks. |
| `ReductionStep.check` | Checks the exact index, both positive scale signs, zero-or-smaller degree and the zero-difference identity. Noncanonical representatives are supported; no inverse or division is executed by replay. |
| `Reduction.checkFrom` | Pairs every repeated factor with a step; missing/extra lists reject. The terminal zero-difference check allows distinct valid stored representatives of the same interpreted polynomial. |
| `Reduction.check` | Positive head degree, original query/exponent length and exponents at most two precede every reduction step. Constant heads take the separate zero-root producer path. |
| `ReductionStep.check_eq` | Extracts all actual guards from arbitrary accepted steps. This existing implication is not a producer-provenance assumption or a new semantic identity proof. |
| `ReductionStep.build` | Uses positive pseudo-division and normalizes nonzero remainders; zero remainder keeps scale one. Acceptance requires the companion arithmetic/sign laws and valid head. |
| `Reduction.buildFrom` | Recurses on the literal factor list, retaining actual accumulators and the final result. It introduces no full-product fallback or external arithmetic. |
| `Reduction.build` | Starts at one with the actual indexed factors. Its internal shape preconditions are established by buildNode and accepted query preprocessing; the operation alone cannot imply those checks. |

## Semantic and phase boundaries

Occurrence counts on repeated observations are distinct from polynomial root
multiplicity. Sparse-table positivity and distinctness establish representation
facts; the existing companion proves root observations and full query meaning.
Original candidate coverage and moment interpretation remain explicit.

The existing conformance target guards count_pos with the standard three
logical axioms. All public imports remain available through HexSignDet.
Source assessment, kernel checks and diagnostic build durations are not
computational scaling evidence or whole-pair Phase-6 acceptance.
