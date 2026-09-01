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
   through `lab`, so the statements are exact; the work is commuting
   lemmas for each imperative loop. The `PairwiseSound` development is
   the proof-of-method: `Compat` transport there is the same argument
   for a refinement chosen to make those inductions clean.
2. **`canonSpec`.** The unpruned search tree as a total function
   (well-founded on remaining cell count), and its leaf-key maximum
   `(code sequence with sentinel, colour values, adjacency bits)`.
   Equivariance makes the unordered tree and hence the maximum
   isomorphism-invariant, giving `iso_iff_canon_eq` for the
   nauty-semantic form; colour-sortedness and `relabel_label` come from
   the partition-nest invariants. One recorded subtlety: nauty's target
   cell is history-dependent — `othernode` accepts the first path's
   `firsttc[level]` as a hint while the refinement-code prefix matches,
   and only falls back to `bestcell` otherwise — so the tree is not a
   function of local node state alone. `canonSpec` must model the
   hinted rule (target cell as a function of the node *and* the
   first-path data), and the invariance proof must show that rule is
   equivariant across isomorphic runs; pretending the rule is plain
   `bestcell` would verify a different tree than the one the port
   searches.
3. **Certificates.** `CanonCert` records the pruned tree the production
   search visited; `checkCanon` replays refinements deterministically
   and validates each pruning step — code-prefix comparisons by a lex
   dominance lemma, orbit and short-prune steps by checked automorphisms
   through the equivariance theorem — concluding
   `result.form = canonSpec G`. `certify?` instruments the `Nauty`
   search as the untrusted producer.
4. **Switch.** Public `canonicalize` becomes certificate-checked
   production search with the total `canonSpec` fallback, making the
   public `canon` nauty-compatible with the SPEC's theorems intact;
   `DiffCert`/`checkDiff` then give the certificate-based negative
   tactic path (two `checkCanon_sound` applications, `checkDiff`, and
   `iso_iff_canon_eq`).

Until stage 4 lands, exact nauty compatibility of the public `canon` is
withheld (the SPEC's staged-namespace allowance), and the released
surface remains reference-backed.
