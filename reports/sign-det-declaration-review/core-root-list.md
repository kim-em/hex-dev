# Full root-list assembly assessment

This assessment covers the 30 named declarations in `HexSignDet/RootList.lean`
and all ten finite comparison laws in `HexSignDet/ThomOrder.lean`.
It is partial computational core review. Finite acceptance and actual successful
producer execution are distinguished from root interpretation and producer
totality, which use the companion's explicit lawful semantic hypotheses.
No phase promotion or performance verdict follows from this assessment.

| Declaration | Assessment |
| --- | --- |
| `Thom.insert` | Uses the actual full-word comparator; duplicate words, undefined comparison and equality reject with an internal system error. Inserts before a strictly larger head or recurses past a smaller one. |
| `Thom.insert_nil` | Normalizes empty-list insertion to the singleton supplied descriptor, without a comparator or arithmetic premise; used by the literal replay consumer. |
| `Thom.insert_success` | Actual insertion succeeds if every input comparison is strictly less or greater. It does not assume that arbitrary comparison results have root semantics. |
| `Thom.insert_perm` | Successful insertion preserves exactly the supplied descriptors; proof follows the executed comparison and recursive branches. |
| `Thom.insert_sorted` | Preserves strict finite comparator order using the existing transitivity and reversal laws, without adding caller-supplied order axioms. |
| `Descriptor.ofFullRow` | Constructs a full descriptor from a member of an accepted full table with positive degree, literal context identity and count one. The table supplies word width, ternary entries and exact lookup. |
| `Descriptor.ofFullRow_raw` | Identifies the complete raw descriptor as the caller's full descriptor with the row's literal sign word. |
| `Descriptor.ofReplay_ofFullRow` | Rechecking the same checked row returns precisely the constructed full descriptor; allows reuse of the tree-level interface. |
| `Descriptor.rootsFromTable` | Shares accepted table/domain/query evidence across rows. Checks count one for every row and orders each descriptor by actual Thom insertion. The supplied membership proof need not claim every table row was passed. |
| `Descriptor.rootsFromTable_nil` | Empty supplied row list yields an empty result without applying insertion or an arithmetic checker. |
| `Descriptor.rootsFromTable_cons` | Exposes the actual count-one recursive branch; retains the exact table membership and constructed descriptor. |
| `Descriptor.rootsFrom` | Literal reference path rechecks each full descriptor against the same replay. Rejects nonunit counts, failed descriptor replay, recursive failure and invalid insertion separately. |
| `Descriptor.rootsFromTable_eq` | Shared extraction agrees exactly with literal per-descriptor checking for supplied members of the checked table, including errors and ordering. It does not silently extend a partial row list to full coverage. |
| `Descriptor.rootsFrom_perm` | Successful extraction preserves precisely the supplied encoding words up to permutation. It neither introduces nor drops a supplied row. |
| `Descriptor.rootsFrom_length` | Derives exact output length from the existing permutation law, without unfolding recursion downstream. This is an assembly count, not a theorem about polynomial multiplicity. |
| `Descriptor.rootsFrom_counts` | Arbitrary successful extraction implies count one for every supplied row. The proof follows each count guard and actual recursive result; no producer provenance is assumed. |
| `Descriptor.rootsFrom_raw` | Every output retains the original literal head, interval and context and canonical full derivative slots. Sorting changes only positions. |
| `Descriptor.rootsFrom_sorted` | Success gives strict pairwise order by the actual finite comparator. Mathematical order is established separately in the companion. |
| `Descriptor.rootsFromTable_perm` | Transfers exact supplied-word preservation through the proved shared/reference-path agreement. |
| `Descriptor.rootsFromTable_sorted` | Transfers strict finite order through that same agreement. |
| `Descriptor.buildRoots` | Prepares the requested domain and builds its full derivative table. Positive-degree heads use shared extraction; constants use the literal reference path. Internal errors are retained; invalid domains return absence. |
| `Descriptor.buildRoots_none` | Public absence is equivalent to failed actual preparation. Internal errors and successful extraction cannot be mistaken for absence. |
| `Descriptor.buildRoots_ofTable` | Given actual preparation, table production and extraction equations, returns the actual positive-degree producer result. It is an assembly theorem, not an unconditional success assertion. |
| `Descriptor.buildRoots_ofEmpty` | An actual empty produced full table yields successful empty output in both degree branches, without an ordering assumption. |
| `Descriptor.buildRoots_ofSingle` | Actual single-row production with count one and positive degree gives success; insertion into an empty list needs no comparator result. |
| `Descriptor.buildRoots_spec` | Every successful public output arises from its actual preparation and full table, with literal extraction agreeing in both degree branches. |
| `Descriptor.buildRoots_raw` | All returned descriptors retain the requested subject and full indices, including singleton lists. |
| `Descriptor.buildRoots_constant` | A successful constant-head result is empty by the positive-degree shape requirement on every possible descriptor; this alone does not claim all constant inputs prepare successfully. |
| `Descriptor.buildRoots_perm` | Successful public output preserves every full word of the actual produced table, including the constant/empty case. |
| `Descriptor.buildRoots_sorted` | Successful output is strictly pairwise ordered by the actual comparator; companion root-order interpretation remains explicit. |

The module introduces no structures or instances. Its two previously undocumented
full-row correspondence theorems now have docstrings. The new length and count-one
laws characterize arbitrary successful row extraction, rather than relying on
successful sample output. Root multiplicities for nonsquarefree polynomials are
outside this shared squarefree-domain interface and remain in the real-closure
layer. Semantic completeness of an arbitrary accepted full root table is supplied
by `Descriptor.rootsFrom_coverage`; `rootsFrom_ordered` interprets successful
finite sorting, including partial row extraction.

## Finite comparison laws

The first seven names below live in `Hex.SignDet.Thom`; the descriptor laws
live in `Hex.SignDet`. These statements prove finite comparison behavior,
without interpreting any vector as a polynomial root.

| Declaration | Assessment |
| --- | --- |
| `compareFrom_cons_lt` | Strict comparison either comes from a strictly ordered tail or from equal tails whose next sign is 1 or -1 and orients the current entries. Zero or absent next signs do not furnish the second branch. |
| `compareFrom_drop` | A strict result on equally long suffixes determines the full result; equality is excluded explicitly because earlier entries can change it. |
| `compareFrom_at_lt` | Equal suffixes after a valid last differing coordinate and a correctly oriented nonzero next sign imply the actual strict result. Equal lengths ensure both indexed lookups exist. |
| `compareFrom_trans` | Proves strict transitivity of the executed recursive comparator, including arbitrary integer entries. It uses accepted strict premises rather than assuming every pair is comparable. |
| `compareFrom_swap` | Swapping words swaps the entire optional result, preserving failure and equality as well as strict order. |
| `compareSigns_trans` | Retains both shape/ternary checks when composing strict comparisons, then applies finite recursive transitivity. |
| `compareSigns_swap` | Symmetric shape guards and recursive reversal establish exact optional-result reversal. |
| `Descriptor.fullOrder_trans` | Composes literal head and canonical full-slot bindings through `fullOrder_iff` with strict sign-word transitivity, without unfolding the checker. It requires no equal endpoints or interpreted-field axioms. |
| `Descriptor.fullOrder_swap` | Reverses both the literal binding guards and the finite word result, including rejected pairs. |
| `Descriptor.fullOrder_reverse` | Converts a successful greater-than comparison into the reverse less-than result via the full swap law. |

Insertion's strict sortedness proof uses `fullOrder_trans` and
`fullOrder_reverse` directly. These comparator laws do not assert mathematical
root order or replace the companion's lawful ordered real-closed interpretation.
All ten declarations already have useful docstrings; recursive laws remain
explicit rather than being installed as uncontrolled global simplifications.

The existing literal `fullReplay` is used directly by
`RootSemantics.literal_extraction` and `literal_roots`. Public extraction
and empty-insertion equations establish successful finite extraction; the
supplied-replay exports then establish real coverage, no duplicate values
and strict order. Neither example evaluates a prepared-domain or root producer.
Both consumer proofs and all five new public lemmas have ordinary-kernel
axiom guards in the existing diagnostics/conformance targets.

Adoption by the frozen RCF reader and its manual/report availability text
remains with [#10358](https://github.com/kim-em/hex-dev/issues/10358). Its
`RootTable.Result` supplies the accepted replay and complete-table extraction
premises required here; this assessment adds no second adapter implementation.
