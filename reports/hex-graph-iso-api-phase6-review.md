# HexGraphIso API Phase 6 Review

## Scope

Reviewed the public API surface of the coloured graph canonical labelling
library against `HexGraphIso/SPEC/hex-graph-iso.md` and `PLAN/Phase6.md`, in
preparation for the `leanprover/hex-graph-iso` split release.

Covered:

- `HexGraphIso/Ops.lean`, the headline two-tier operation surface;
- `HexGraphIso/Tactic.lean`, the `graph_iso` frontend, its `Config`, and its
  extension mechanism;
- `HexGraphIso/{Canon,Colored,Iso,IsoLit,Lex,NodeLit,Pairwise,PairwiseSound,Perm,Random,Reference,Separator,Families}.lean`;
- `HexGraph/Basic.lean` and `HexGraph.lean`, folded into this release per
  `scripts/release/released.yml`;
- the umbrella `HexGraphIso.lean`.

Deliberately **not** covered, and recorded rather than acted on: everything
under `HexGraphIso/Nauty/`. That is 35 files, 32,746 lines, and 1,035 of the
library's 1,573 public declarations, and it is the subject of in-flight
verification work (the verified search refinement programme). Renaming or
re-documenting declarations under active proof development would conflict with
that work. Section "In-flight surface" below records what a review of it would
find, for whoever picks it up when the programme settles.

## Summary

The reviewable surface is 538 public declarations across 23 files plus three
umbrellas. Overall docstring coverage is 271/538, or 50%.

The operation surface in `Ops.lean` is well shaped and is the library's
strongest file. It sells a genuine two-tier API: a fast tier
(`canonicalize`, `canon`, `label`, `findIso`, `isIso`) and a certificate-checked
tier, joined by `canonicalize_eq_canonicalizeChecked`, so a caller can pick a
tier without the two drifting apart. `iso_iff_canonChecked_eq` is the
biconditional the library exists to prove and it is stated at the right
generality. The bounded produce-then-replay pipeline (`certify?`, `checkCanon`,
`canon?`, `checkDiff`) correctly separates the untrusted search from the
kernel-facing replay, and `canon?_eq_some` and `checkCanon_sound` have the
conclusions the SPEC's release conditions demand. Callers never need to unfold
the executable representation.

`graph_iso` is a single well-scoped tactic with a clean extension point:
importing `HexGraphIsoMathlib` extends the same tactic name rather than
introducing a second one, which is the right design and worth keeping.

Three structural findings are recorded below. Two are qualifier families that
belong in namespaces, and one is a namespace-hygiene problem where an internal
mirror layer and a test module are both part of the shipped API. None is a
correctness issue and none blocks the release.

## Fixed in this review

These were small enough to act on directly, and the library rebuilds green.

1. **`HexGraphIso.lean` had no module docstring.** It was 50 `public import`
   lines and a bare `public section`, the only one of the three umbrellas
   without one. Added a docstring that names the intended entry points
   (`canonicalize`/`canonChecked` and their tiers, the decision operations,
   the bounded certificate pipeline, `Families`, `Random`, `graph_iso`) and
   says explicitly that `Hex.GraphIso.Nauty` is the verified engine rather
   than the entry point. A reader landing on the umbrella now learns which of
   the 1,573 exported names are the twelve they want.

2. **The eight undocumented soundness theorems in `Ops.lean`.** Every `def` in
   the file was documented; the entire gap was on the theorem side, which is
   backwards, since the theorems are what a prover reaches for first.
   Documented `findIsoChecked_sound`, `findIsoChecked_isSome_iff`,
   `isIsoChecked_eq_true_iff`, `isIsoChecked_eq_false_iff`,
   `FindIso.some_sound`, `FindIso.none_sound`, `checkCanon_sound`, and
   `canon?_eq_some`. The `FindIso.none_sound` docstring in particular now
   spells out the `some none` versus outer `none` distinction, which is the
   one place in the bounded API where an inattentive reader could mistake
   exhaustion for a refutation.

3. **`Tactic.Config`'s three fields were undocumented.** These are the
   user-facing options: `maxNodes`, `maxCertNodes`, `maxCheckerSteps`. Added
   field docstrings, including the fact that `maxNodes` also gates the two
   negative separator routes (at least 4 nodes for the root separator, at
   least `2 * (n + 1)` for the two-code separator), and that
   `maxCheckerSteps` is the one to raise when the elaborator succeeds but the
   kernel cannot finish.

4. **The `graph_iso` syntax docstring did not show the limit syntax.** It said
   "See the module docstring for the limit syntax", which a hover in an editor
   cannot follow. Inlined the syntax, the three defaults, and the fact that
   importing `HexGraphIsoMathlib` extends the same tactic.

5. **The `Tactic.lean` module docstring was stale.** It claimed the positive
   path "closes through the replay-bounded `checkIso?` and its soundness
   theorem". The positive path has moved to `checkIsoLit` and
   `isomorphic_of_checkIsoLit`, which check against list-literal adjacency
   data so the kernel never unfolds the executable representation. Corrected,
   and documented `evalGraphIsoTac`, the elaborator itself.

6. **Removed `not_isomorphic_of_isIsoChecked_eq_false`.** Unreferenced
   anywhere in the repository including the SPEC and README, an exact
   restatement of `Ops.lean`'s `isIsoChecked_eq_false_iff` one `.mp` away, in
   the wrong file, and at eight name segments the worst name in the reviewable
   set. Straightforward cruft.

7. **Documented `isomorphic_of_checkIso?` rather than removing it.** A grep
   reports it dead, but that is because the tactic moved to the literal route;
   it remains the only soundness bridge for the public `checkIso?` operation,
   and removing it would leave `checkIso?` uncharacterised. The docstring now
   says exactly that.

8. **Renamed `permOfNatArray?` to `Perm.ofNatArray?`** (5 use sites). It is
   declared immediately after `end Perm`, beside `Perm.ofVector?`, and does
   the same job from a different input; the `perm` prefix restated a namespace
   it should have been inside. This is the house rule that qualifiers belong
   in namespaces, applied to a case small enough to just fix.

9. **Renamed `not_isomorphic_of_checkKeysLit` to
   `not_isomorphic_of_checkKeysFlat`** (3 sites). It differed from
   `not_isomorphic_of_checkKeysL` in `NodeLit.lean` by one trailing letter,
   and the two are genuinely different theorems over different literal
   encodings; the `NodeLit` one delegates to it. `Flat` matches the
   vocabulary of its own file, which already has `checkKeyFlat` and
   `flatRows`. A one-letter distinction between two live theorems is a bug
   waiting to happen in a `mkAppM` call.

## Findings

### 1. The `Checked` suffix is a namespace, not a name

Sixteen public names in `Ops.lean` encode the tier in the identifier:
`canonicalizeChecked`, `canonChecked`, `labelChecked`, `relabelChecked_label`,
`colorSorted_canonChecked`, `canonChecked_iso`, `canonChecked_invariant`,
`iso_iff_canonChecked_eq`, `canonicalize_eq_canonicalizeChecked`,
`findIsoChecked`, `isIsoChecked`, `findIsoChecked_sound`,
`findIsoChecked_isSome_iff`, `isIsoChecked_eq_true_iff`,
`isIsoChecked_eq_false_iff`.

This is the textbook case the house style names: a qualifier repeated across a
whole family, which should be a namespace. `Hex.GraphIso.Checked.canonicalize`,
`Checked.canon`, `Checked.findIso`, `Checked.iso_iff_canon_eq` would let the
two tiers share one vocabulary, and would make
`canonicalize_eq_canonicalizeChecked` read as `Checked.canonicalize_eq`.

**Not fixed, deliberately.** `HexGraphIso/SPEC/hex-graph-iso.md` pins these
names verbatim in 24 places, including explicit signature blocks for
`def labelChecked` and `theorem relabelChecked_label`, and
`HexGraphIso/README.md` lists them. This is a SPEC change, not a refactor, and
a SPEC change on the eve of a first release should be a deliberate decision
rather than a side effect of an API review. Recommended as a follow-up issue:
`HexGraphIso Phase 6: move the Checked tier into its own namespace`. Doing it
before the first release is much cheaper than after, since after release it is
a breaking change for downstream consumers.

### 2. `NodeLit.lean` ships 92 internal helpers, all carrying an `L` suffix

`HexGraphIso/NodeLit.lean` is 1,160 lines and declares 95 public names. Three
are consumed outside the file: `checkKeyLit`, `checkKeyLit_eq`, and
`not_isomorphic_of_checkKeysL`. The other 92 are the list-mirror layer
(`splitCellLoopL`, `refineNontrivialGoL_eq`, `specMaketargetcellL_eq`,
`checkCellsPermL_eq`, `invPermGoL_eq`, and so on) and are used only within the
file.

Two problems compound here. The `L` is a use-site qualifier repeated 92 times,
so by the house rule it should be a namespace: `Nauty.L.splitCellLoop`,
`Nauty.L.refineNontrivialGo_eq`. And more importantly, 92 internal helpers
should not be public at all. They are neither `private` nor confined to a
clearly-internal namespace, so they land in the shipped `Hex.GraphIso.Nauty`
namespace where a consumer can autocomplete into them and come to depend on
them.

Marking them `private` is the larger win and makes the rename moot. It is also
the safer change, because it cannot break a caller who was not supposed to be
calling them. This file's docstring coverage is 6/95, or 6%, which is the
library's worst, and is much less alarming once the 92 are private: the rule
is public declarations plus non-obvious private helpers, not every helper.

Recommended follow-up: `HexGraphIso Phase 6: make the NodeLit list mirror
private`.

### 3. The umbrella re-exports a test module

`HexGraphIso.lean` `public import`s `HexGraphIso.ModuleBoundaryTests`, whose
`kdecide` elaborator therefore becomes part of the released `HexGraphIso`
tactic namespace. `kdecide` is a test instrument for checking module-boundary
behaviour, not API, and it has no namespace guard.

**Not fixed.** Removing the import changes what the published mirror builds,
and the shipping shape of released repositories (specifically whether test and
conformance sidecars ship at all) is under active reconsideration. Acting on
this now risks colliding with that decision. The finding is real and small;
it should be picked up together with, or immediately after, whatever the
shipping-shape decision concludes. Recommended follow-up:
`HexGraphIso Phase 6: keep ModuleBoundaryTests out of the umbrella`.

### 4. Docstring coverage below the Phase 6 rule

Coverage on the reviewable files, worst first, after the fixes above:

| file | public | documented | % |
|---|---:|---:|---:|
| `HexGraphIso/NodeLit.lean` | 95 | 6 | 6 |
| `HexGraphIso/PairwiseSound.lean` | 40 | 7 | 18 |
| `HexGraphIso/Lex.lean` | 18 | 6 | 33 |
| `HexGraphIso/Iso.lean` | 20 | 7 | 35 |
| `HexGraphIso/Perm.lean` | 55 | 24 | 44 |
| `HexGraphIso/Colored.lean` | 16 | 8 | 50 |
| `HexGraphIso/Reference.lean` | 31 | 18 | 58 |
| `HexGraph/Basic.lean` | 32 | 24 | 75 |

`NodeLit.lean` is finding 2 and should be fixed by making the file private
rather than by writing 89 docstrings. The rest is genuine work, and it is not
uniform in value:

- **`Iso.lean` (13 undocumented) is the highest-value gap.** `IsIso.refl`,
  `.symm`, `.trans` and the `Isomorphic` counterparts are the equivalence
  structure every downstream proof uses, and `checkIso_iff` is the decision
  bridge. These are small lemmas with obvious statements, but they are the
  first thing a new caller meets.
- **`PairwiseSound.lean` (33 undocumented)** ends in
  `decideIso?_isomorphic` and `decideIso?_not_isomorphic`, which are the
  tactic's entry points into the verified pairwise route and are both
  undocumented. Those two matter; the 31 internal transport lemmas above them
  matter much less, and several would be better `private`.
- **`Perm.lean` (31 undocumented)** is mostly the group laws (`comp_assoc`,
  `inv_comp`, `get_inv_get`), whose names carry their statements. Low value.
- **`Lex.lean` (12 undocumented)** is likewise the order laws.

Recommended follow-up, scoped to the two that matter:
`HexGraphIso Phase 6: document the isomorphism equivalence API and the
pairwise decision entry points`.

### 5. Dead declarations

Beyond the two handled above, the following have no reference anywhere in the
repository and are not `@[simp]`:

- `Hex.Graph.ne_of_adj`, `isSome_ofEdges?`, `adj_ofEdges?`, `mem_nbrs`
  (`HexGraph/Basic.lean`);
- `Hex.GraphIso.colorSorted_canonChecked` (`Ops.lean:51`);
- `Hex.GraphIso.checkDiff_not_isomorphic` (`Ops.lean:394`);
- `Perm.vec_of_ofVector?`, `Perm.comp_assoc`, `Perm.inv_comp`
  (`Perm.lean`).

`checkDiff_not_isomorphic` deserves a specific note: it is the terminal
theorem of the whole `DiffCert` surface, and nothing calls it. The same is
true of the surface it terminates. `CanonCert`, `DiffCert`, `certify?`,
`checkCanon`, `canon?`, `checkDiff`, `labelChecked` and `findIsoChecked` are
referenced only inside `Ops.lean` and in prose in the SPEC and README; no
bench, conformance, tactic or Mathlib-layer consumer exercises the bounded
certificate API. That is not dead code, because it is the API the SPEC
promises and the release conditions name, but it is unexercised API, and a
conformance case that runs one bounded produce-then-replay round trip would be
cheap insurance against it rotting. Recommended follow-up:
`HexGraphIso Phase 6: exercise the bounded certificate API in conformance`.

The four `HexGraph/Basic.lean` lemmas are the folded one-file library's
unused corners and are pure deletion candidates.

### 6. Opaque single-letter suffixes in `Separator.lean`

`sepRootG` and `sepDiffG` (`Separator.lean:365`, `:373`) carry a bare `G`
suffix distinguishing them from `sepRootLit` and `sepDiffLit`. The `Lit`
half reads; the `G` half does not. Three use sites each. `Sep.root?` and
`Sep.diff?`, or a `Sep` namespace holding both the graph-valued and
literal-valued variants, would read better. Left alone because getting the
distinction right needs the same design pass as findings 1 and 2 rather than
a mechanical rename.

## In-flight surface

Recorded, not acted on: `HexGraphIso/Nauty/`, 35 files, 1,035 public
declarations, 599 documented (58%).

Naming under `Nauty/` is in good shape and needs no intervention. Only 24 of
1,035 names reach six or more segments, and every one is an idiomatic
`conclusion_of_hypothesis` form such as `eq_of_submask_of_popCount_eq`,
`checkAutom_scatter_of_leafRows_eq`, or `active_eq_zero_of_pickSplit_none`.
None reads like a use-site sentence and none has the defensive-disambiguation
shape the house rule targets. The one small qualifier family, the four `Fast`
suffixes (`lowBit_eq_lowBitFast`, `popCount_eq_popCountFast`,
`toList_eq_toListFast`, `rowOf_eq_rowOfFast`), is small enough to leave.

The documentation gap is real and concentrated. `Nauty/SpecIso.lean` is 983
lines with 51 public declarations and 7 documented (14%), the library's single
largest documentation gap. `Nauty/Complete.lean` (30%),
`Nauty/CellPermLoop.lean` (30%), `Nauty/Achieved.lean` (32%) and
`Nauty/CanonSpec.lean` (38%) follow. Eight files are at 100%.

The scale point is worth stating plainly for whoever inherits this: `Nauty/`
is 85% of the library's lines and 66% of its public declarations, all
re-exported by the umbrella. Whatever the reviewable surface concludes, the
shipped namespace is dominated by the in-flight engine, and a Phase 6 pass
over `Nauty/` after the verified search refinement programme settles is a
much larger job than this review was.

## No Follow-Up Needed

No follow-up is needed for the two-tier operation design in `Ops.lean`. The
fast and checked tiers are genuinely parallel, `canonicalize_eq_canonicalizeChecked`
pins them together, and `iso_iff_canonChecked_eq` is stated as the
biconditional rather than as two one-sided lemmas. Only the naming of the tier
is at issue, not its shape.

No follow-up is needed for the tactic's extension mechanism. One tactic name,
one `Extension` structure, a hardcoded `extensionNames` list, and a Mathlib
layer that registers against it: this is the right amount of machinery, and
extending `graph_iso` rather than introducing `graph_iso_mathlib` is the
correct call for users.

No follow-up is needed for `Families.lean`, `Pairwise.lean` or `Random.lean`,
which are at 100% docstring coverage with short verb-noun names throughout.
`Families` in particular is a model of what the rest of the library should
look like: `path`, `cycle`, `circulant`, `grid`, `hypercube`, `johnson`,
`kneser`, `paley`, `latinSquare`, each with its parameter validation and
vertex-numbering rule in its docstring.

No follow-up is needed for the separation of untrusted search from kernel
replay. It is the library's central design decision, it is visible in the
types (`certify?` produces, `checkCanon` replays, and the soundness theorem
cites only the replay), and it is what makes the tactic's proofs trustworthy
without trusting the search.

## Verdict

`HexGraphIso` meets Phase 6 for its reviewable surface. The operation API is
well designed, the tactic frontend is well scoped, the automation-critical
files are fully documented, and the fixes in this review close the gaps that
would have been visible to a first-time caller: the undocumented umbrella,
the undocumented soundness theorems, the undocumented tactic options, a stale
module docstring, one piece of cruft, and two names that were actively
misleading.

The three recorded findings are real and should become issues, but none is a
correctness problem and none should hold the release. Two of them, the
`Checked` namespace and the `NodeLit` privacy pass, are meaningfully cheaper
before the first release than after it, and that is the argument for doing
them soon rather than the argument for blocking on them now.

The honest qualification on this verdict: it covers 34% of the library's
public declarations. The other 66% is `Nauty/`, and its Phase 6 pass is owed
once the verified search refinement programme settles.
