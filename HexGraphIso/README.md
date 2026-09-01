# HexGraphIso

Coloured graph canonical labelling per
[SPEC/Libraries/hex-graph-iso.md](../SPEC/Libraries/hex-graph-iso.md).

## Layers and their trust status

- `Perm`, `Colored`, `Iso` — executable permutations, ordered onto
  colourings, `IsIso`/`Isomorphic`, and the proven Boolean `checkIso`.
- `Reference` — the factorially expensive reference canonical form with
  the full proof suite: `relabel_label`, `canon_iso`, `canon_invariant`,
  `iso_iff_canon_eq`. The public operations in `Canon` are currently
  backed by it, so the public theorems are inherited.
- `Nauty` — an exact executable transcription of the pinned nauty 2.9.3
  dense canonical search. Unverified; its evidence is the conformance
  oracle (`scripts/oracle/graphiso_nauty.py`), which pins canonical
  labels, canonical bits, and visited-node counts against the real nauty
  on the committed fixture, and differential sweeps during development
  (all labelled graphs to `n = 6`, structured and random cases to
  `n = 30`).
- `Pairwise` (+ `PairwiseSound`) — a fully verified
  individualization-refinement isomorphism decision, structurally
  recursive so the kernel replays it. `decideIso?_isomorphic` and
  `decideIso?_not_isomorphic` are proven; the `graph_iso` negative path
  replays it under `maxNodes`.
- `Tactic` — `graph_iso`. Positive goals: untrusted nauty search
  produces the transporter, the kernel replays `checkIso?`. Negative
  goals: kernel replay of the verified pairwise decision.

## The remaining verification target

The SPEC's certificate layer (`CanonCert`, `checkCanon`, `DiffCert`,
`canon?_eq_some`, `checkCanon_sound`) certifies the *nauty-semantic*
canonical form, whose representative differs from `Reference.canon`.
The planned stack, in dependency order:

1. **Port equivariance.** For a vertex renaming `σ`:
   `refine` on the `σ`-image graph with `σ ∘ lab` equals the `σ`-image
   of `refine`, with identical `ptn`, `active`, cell structure, and
   refinement codes; likewise `bestcell`/`targetcell` (position-valued)
   and `breakout`. Everything in `Nauty.Refine` reads the graph only
   through `lab`, so the statements are exact. **Status: `refine_map`
   in `Nauty/Equivariance.lean` proves this for the whole of `refine`**
   (two-pointer partition, both splitting passes, window scan, stable
   counting redistribution, active-cell loop), together with the
   `StOk` state invariant that keeps every splitter and labelling
   access in range. Remaining for this stage: the position-valued
   helpers (`cheapautom`, `bestcell`, `targetcell`, `breakout`) and
   the leaf comparison chain (`testcanlab`, `updatecan`, `isautom`)
   at the search level.
2. **`canonSpec`.** The unpruned search tree as a total function and
   its leaf-key maximum. **Status: `Nauty/CanonSpec.lean` defines the
   spec** (lexicographic keys: code chain with sentinel, then `g^lab`
   rows in nauty's row order) **and proves `specNode_map`: the maximal
   leaf key is invariant under a vertex renaming.** The recorded
   hinted-target-cell subtlety resolved cleanly: the `firsttc` hint
   applies exactly at nodes whose code chain is already dominated
   (`compCanon < 0`), and such subtrees never supply the canonical
   leaf, so the specification's target-cell rule is the plain hint-free
   `targetcell`; the sentinel convention reproduces nauty's preference
   for shallower leaves, and children are enumerated by cell position,
   making equivariance pointwise. **`refine_perm` (Nauty/CellPerm.lean)
   proves the within-cell reordering invariance: refine depends on an
   ordered partition only through the multiset of vertices in each
   cell.** One further recorded subtlety: `bestcell`'s nontrivial-join
   test reads the adjacency row of each cell's *first* vertex, so it is
   representative-dependent and well defined only on equitable
   partitions (where every representative gives the same verdict).
   Rather than formalize equitability of refine outputs, the
   specification's target-cell rule tests the cell's neighbour-count
   multiset (`countsOf`-based), which agrees with nauty's rule on every
   equitable state, is invariant under both renamings and within-cell
   reordering, and lets the certificate checker verify agreement with
   the recorded target cell on each replayed node — a decidable
   per-node check in place of a global equitability theorem. The spec
   uses the count-based rule; `specNode_map` is proved against it, the
   key order is a proven linear order (`keyCmp` equality/trichotomy/
   transitivity with `keysMax` permutation-invariance), and
   `specNode_perm` proves the spec tree invariant under
   cell-equivalent labellings (same partition, each cell holding the
   same vertex multiset), by induction on fuel through `refine_perm`,
   target-cell agreement, and per-child breakout segments.
   **`canonSpecKey_eq_of_isomorphic` (Nauty/SpecIso.lean) lifts both to
   the graph level: isomorphic coloured graphs have equal spec keys**,
   by extracting a vertex renaming from the isomorphism, transporting
   the adjacency rows (`rowsMap_of_isIso`), and showing the two initial
   labellings are cell-equivalent colour class by colour class at the
   root partition. **The stage is complete: `specCanon`
   (Nauty/SpecCanon.lean) is the total nauty-semantic canonical form
   read off the key, `specCanon_iso` (Nauty/Achieved.lean) shows every
   graph isomorphic to its form via the achieved leaf** — refine and
   breakout preserve every ancestor cell's contents
   (`refine_refInv`), boundary counting shows the search always
   reaches a discrete leaf, and the achieved labelling is a genuine
   colour-sorted relabelling — **so `iso_iff_specCanon_eq` gives the
   full spec-level equivalence.**
3. **Certificates.** `CanonCert` records the pruned tree the production
   search visited; `checkCanon` replays refinements deterministically
   and validates each pruning step — code-prefix comparisons by a lex
   dominance lemma, orbit and short-prune steps by checked automorphisms
   through the equivariance theorem — concluding
   `result.form = canonSpec G`. `certify?` instruments the `Nauty`
   search as the untrusted producer. **Status: `Nauty/Cert.lean`
   defines `CertNode` (explored leaf/node, code prune, automorphism
   prune) and the executable replay `checkNode`/`checkKey`, and proves
   `checkKey_sound`: a successful replay pins `canonSpecKey G = B` for
   the claimed best key `B`.** Each pruned sibling is justified either
   by its recomputed refinement code falling below the best code at
   that depth (`specNode_keyLe_of_code_lt`), or by a checked
   automorphism (`checkAutom`/`checkCellsPerm`) mapping it onto an
   earlier sibling (`specNode_autom`). **`certifyKey?` is the untrusted
   producer**: a branch-and-bound search finds the best key, the
   certificate is rebuilt against it, and the trusted replay validates
   the pair, so `certifyKey?_sound` needs no trust in the search
   (validated end to end against the naive `canonSpecKey` on small
   coloured graphs, and on `n = 12..16` families including Petersen
   through the checker alone). `checkCanon` (Nauty/CanonForm.lean) is
   the `CanonResult`-level wrapper: it validates the replay, checks the
   claimed labelling's leaf rows against the key and its colours
   against the vertex order, and packages the relabelled form, with
   `checkCanon_sound` tying the result to `canonSpecKey`;
   `certifyCanon?` chains the producer, the best-path labelling replay
   (`bestLab?`), and the checked wrapper. Checked forms are
   key-determined (`checkCanon_rows`, `checkCanon_sorted`,
   `checkCanon_form_eq` via the leafRows/relabel correspondence
   `rowsOf_relabel_eq_leafRows`), which closes the certificate-based
   decision in both directions: `isomorphic_of_certs` (same key, same
   colour class sizes) and `not_isomorphic_of_certs` (`checkDiff` on
   the keys). Remaining for this stage: automorphism prunes in the
   producer.
4. **Switch.** Public `canonicalize` becomes certificate-checked
   production search with the total `canonSpec` fallback, making the
   public `canon` nauty-compatible with the SPEC's theorems intact;
   `DiffCert`/`checkDiff` then give the certificate-based negative
   tactic path (two `checkCanon_sound` applications, `checkDiff`, and
   `iso_iff_canon_eq`). **Status: `canonicalizeSpec`
   (Nauty/Complete.lean) is the total certificate-checked
   canonicalization with the full theorem surface**
   (`canonicalizeSpec_relabel`, `canonicalizeSpec_iso`,
   `canonicalizeSpec_invariant`, `iso_iff_canonicalizeSpec_eq`): the
   branch-and-bound producer runs first, then the provably total
   exhaustive fallback — `certifyNode_complete`/`checkKey_complete`
   show the checker accepts the honest certificate for the true key,
   and `bruteCanon?_isSome` finds the achieved leaf among all
   labellings. **The public surface has switched**:
   `HexGraphIso/Ops.lean` defines `canonicalize`/`canon`/`label`/
   `findIso`/`isIso` and the bounded operations backed by
   `canonicalizeSpec`, reproving the whole theorem surface
   (including `colorSorted_canon`); `Canon.lean` keeps the limit
   structures and the replay-bounded `checkIso?`. The conformance
   guards pass unchanged against the new backing.

The public surface is now backed by the certificate-checked
nauty-semantic canonicalization. `Reference` remains as an independent
exhaustive cross-check.
