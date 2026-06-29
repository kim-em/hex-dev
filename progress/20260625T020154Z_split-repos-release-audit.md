# Public-release audit — the six split-off hex repos

Audit of the six repositories split out of the hex monorepo (`hex-dev`),
assessed for public-release readiness across: dead code, AI slop, missing
README/LICENSE/CI, excessive/missing documentation, performance footguns,
spaghetti code, and unmaintainable proofs.

Repos audited (all on GitHub under `kim-em/`, all **public** and pushed):

| executable (Mathlib-free) | correspondence proofs |
| --- | --- |
| `hex-matrix` | `hex-matrix-mathlib` |
| `hex-gram-schmidt` | `hex-gram-schmidt-mathlib` |
| `hex-lll` | `hex-lll-mathlib` |

Every claim below is backed by a command you can re-run; the commands are
collected at the end.

---

## Executive summary

The repos are in **good shape**. The skeleton is already correct everywhere:
README, Apache `LICENSE`, `.gitignore`, and a single-job `ci.yml` are present
and consistent in all six; inter-repo `require` pins use real revs; and the
proof hygiene is clean — **no `axiom`, no `native_decide`, no `sorry`, no
`set_option maxHeartbeats` overrides, no `TODO/FIXME/HACK`, no leftover
`.pod/` or `progress/` directories, no commented-out code.**

There is exactly **one release blocker**, and it is documentation, not code:
the SPEC files reference sibling files (`SPEC/benchmarking.md`,
`PLAN/Conventions.md`, `libraries.yml`) that were **not** carried across the
split, so those links 404 for any public reader. Everything else is
recommendation-grade polish or opt-in refactoring.

### Per-repo go / no-go

| repo | blocker | notes |
| --- | --- | --- |
| `hex-matrix` | broken SPEC links (5) | one 10.6k-line file; otherwise clean |
| `hex-matrix-mathlib` | none | clean; smallest proof layer |
| `hex-gram-schmidt` | broken SPEC links (1) | two 8.3k/4.2k-line files; dup row-swap lemmas; docstring gaps |
| `hex-gram-schmidt-mathlib` | none | dup row-swap lemmas (shared with base) |
| `hex-lll` | broken SPEC links (12) | FFI undocumented for users; bench file larger than the lib |
| `hex-lll-mathlib` | none | clean; one ~310-line proof, well structured |

**Recommendation:** fix the SPEC links in the three executable repos, then
ship. The rest can land incrementally after release.

---

## 0. Baseline hygiene — all green

Verified across all six repos:

- `README.md`, `LICENSE` (Apache 2.0), `.gitignore`, `.github/workflows/ci.yml`
  all present.
- `grep -rn 'axiom|native_decide|sorry'` over `*.lean`: **no real hits.** The
  single `sorry` match is the word inside a docstring explaining a theorem is
  *not* sorry-bound (`hex-matrix-mathlib/HexMatrixMathlib/Determinant.lean:25`).
- `grep -rn 'set_option maxHeartbeats'`: **none.**
- `grep -rn 'TODO|FIXME|HACK'`: **none.**
- No `.pod/`, no `progress/`, no `.bak`/swap files committed.
- The CI job is a single ubuntu job per repo (matches project CI doctrine),
  builds the lib, smoke-builds conformance + bench, and asserts Mathlib-free
  for the executable repos.

The READMEs are short, accurate, consistent in structure, and correctly
cross-link each executable repo to its `*-mathlib` partner and to the
`hex-dev` development monorepo.

---

## 1. RELEASE BLOCKER — broken SPEC cross-references

The split copied each repo's own `SPEC/hex-<name>.md`, but the documents
those files link to live elsewhere in the monorepo and were **not** copied.
Confirmed absent in every executable repo:

```
SPEC/benchmarking.md   MISSING   (referenced as ../benchmarking.md and "SPEC/benchmarking.md §…")
PLAN/Conventions.md    MISSING   (referenced as ../../PLAN/Conventions.md)
libraries.yml          MISSING   (referenced as ../../libraries.yml)
```

Dangling reference counts (`grep -rnE 'benchmarking\.md|/PLAN/|libraries\.yml|\.\./\.\.|testing\.md|CI\.md' <repo>/SPEC/`):

| repo | dangling refs |
| --- | --- |
| `hex-lll` | 12 |
| `hex-matrix` | 5 |
| `hex-gram-schmidt` | 1 |
| all three `*-mathlib` | 0 |

Representative offenders:
- `hex-matrix/SPEC/hex-matrix.md:135,156` → `../../PLAN/Conventions.md`
- `hex-lll/SPEC/hex-lll.md:349,386` → `../../libraries.yml`
- `hex-lll/SPEC/hex-lll.md:373,394,397,437,459` → `../benchmarking.md#…`
- `hex-gram-schmidt/SPEC/hex-gram-schmidt.md:336` → `SPEC/benchmarking.md §…`

**Fix options (pick one, per link):**
1. **Prune** — drop the reference if it was only meaningful inside the
   monorepo (most `benchmarking.md §…` mentions are internal process notes).
2. **Inline** — paste the one or two sentences the SPEC actually relies on.
3. **Absolute URL** — rewrite as a link into the public `hex-dev` repo,
   e.g. `https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md`.

This is the only thing that visibly breaks for an outside reader.

---

## 2. Dead code

**Low severity.** No computational dead code found in any executable repo —
every `def` reachable from the public API is used. Two items worth a glance:

- **`scaledCoeffRows` is a proof-only parallel formulation, not live code.**
  `hex-gram-schmidt/HexGramSchmidt/Int.lean:1063` defines `scaledCoeffRows`
  (an array-loop formulation), while the algorithm actually runs
  `scaledCoeffRowsSchur` (`:1096`, wired into `gramDetVec`). Every reference
  to `scaledCoeffRows` (lines 4988, 5031–5038, 5723–7014, 7864–7874, …) sits
  **inside theorem statements and proofs** — it is never called from a `def`
  body. It is therefore not dead in the "unused symbol" sense, but it is a
  second formulation maintained only to support bridge lemmas. Worth checking
  whether those bridge lemmas are still load-bearing; if not, dropping the
  whole `scaledCoeffRows` family would remove a meaningful chunk of `Int.lean`.

- **No unused private helpers** were found in the matrix or LLL repos — the
  private lemma blocks are all consumed by the proofs immediately following.

---

## 3. AI slop

**Low–medium severity.** No "research completed" timestamps, no `_v2`/`_alt`
defensive suffixes, no progress-note comments in code. The one real instance
of the pattern the project's own `.claude/CLAUDE.md` calls out ("qualifiers
in the name instead of a namespace; 5+ qualifying words is a smell") is
**over-long lemma names**. Longest offenders (chars):

```
70  bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
62  scaledCoeffRows_lower_eq_noPivotLoop_gramMatrix_of_no_singular
61  getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
60  noPivotLoop_initial_gram_prevPivot_ne_zero_of_regular_prefix
59  det_setRow_setRow_nMatrix_r2_r0_r3_r1_eq_pow_mul_nDet_r2_r3
58  det_gramMatrix_leadingRows_pos_of_upperTriangular_pos_diag
56  projectionCoeff_reduceAgainstBasis_eq_of_forall_dot_zero
```

These are overwhelmingly `private` proof lemmas, so the blast radius is
internal. They are not a release blocker, but they are exactly the tech debt
the naming doctrine warns about, and a rename pass (push qualifiers into
namespaces, name the noun) would pay off for whoever maintains these proofs
next. The `det_setRow_setRow_nMatrix_r2_r0_r3_r1_…` family in
`hex-matrix/HexMatrix/Determinant.lean` is the most egregious — the index
permutation is encoded in the name.

### Duplicated row-swap lemma family

`rowSwap_row_eq_of_ne_int`, `rowSwap_row_left_int`, `rowSwap_row_right_int`,
and the `rowSwap_getRow_*_val_int` variants are `private` in
`hex-gram-schmidt/HexGramSchmidt/Int.lean:8053+` **and** appear
near-identically in `hex-gram-schmidt-mathlib/HexGramSchmidtMathlib/Update.lean:91+`.
Recommend promoting the base-repo versions to public and deleting the mathlib
copies, so the proof layer imports rather than restates them.

---

## 4. Documentation — missing and excessive

**Medium severity, all minor individually.**

**Missing:**
- Several public defs in `hex-gram-schmidt/HexGramSchmidt/Int.lean` lack
  docstrings: `scaledCoeffMatrix` (:49), `memLattice` (:67), `gramDet` (:72),
  `independent` (:78), `gramDetVecEntry` (:100), `rowsToMatrix` (:164); and
  `sizeReduce` in `Update.lean:28`.
- `hex-lll`: the fpLLL FFI is **under-documented for outside users.** The
  README mentions an "optional FFI provider (fpLLL)" exists (lines 3–4, 14)
  but never says how to enable it — no mention of the `HEX_FPLLL_FFI_LIB`
  environment variable, the `dlopen` symbol protocol, or (importantly) that
  absence of the provider falls back gracefully to the native reducer
  (`HexLLL/Basic.lean:~2487`). The `LLLProvider` namespace also has no module
  docstring. An outside user cannot turn fpLLL on from the README alone.

**Excessive:**
- A handful of multi-line comment blocks restate proof *strategy* rather than
  the theorem (e.g. `hex-gram-schmidt/HexGramSchmidt/Int.lean:7697–7715`, an
  18-line narrative above one lemma). Fine for an internal proof; for a
  public release, trimming to the statement (or moving the prose into a
  module-level note) reads cleaner. This is stylistic, not a defect.

Module docstrings are otherwise present and good on `Basic`/`Int`/`Update`
in each repo.

---

## 5. Performance footguns

**None found.** The executable hot paths are deliberately optimized:

- **Bareiss / RREF** (`hex-matrix`): array-based, fraction-free exact
  division — no rational blowup, no hidden quadratic beyond the inherent
  O(n³) of elimination; array conversions are one-shot, not per-element.
- **Gram-Schmidt** (`hex-gram-schmidt`): `gramRows` is computed once per
  `scaledCoeffRowsSchur`; the `schurSigma` σ-chain
  (`Int.lean:1072`) grows only as the exact-divisibility guarantee allows
  (fraction-free by design). Worth a one-line comment stating that invariant,
  since the multiply-then-`exactDiv` pattern looks alarming without it.
- **LLL** (`hex-lll`): bounded fuel (`lllFuel = (potential+1)*(n+1)`), cached
  Gram data in `LLLState`, `Array` in hot paths, and a fixed 128-bit interval
  pre-check (`intervalPrec`) independent of input size. The 128-bit choice
  deserves a one-line rationale comment, but is not a footgun.

The only proof-side `List`-where-`Array` patterns are in `noncomputable`
definitions, so they have zero runtime impact.

---

## 6. Spaghetti / structure

**Medium severity — concentrated in a few oversized files.** Nothing is a
tangled god-function; the issue is sheer file size, which raises reviewer and
maintainer load:

| file | lines | note |
| --- | --- | --- |
| `hex-matrix/HexMatrix/Determinant.lean` | 10,591 | ~200+ lemmas: Leibniz, cofactor, bordered-minor, Desnanot–Jacobi |
| `hex-gram-schmidt/HexGramSchmidt/Int.lean` | 8,318 | entry points + array ops + Schur recurrence + canonical-coeff machinery + lattice + reconstruction |
| `hex-gram-schmidt/HexGramSchmidt/Basic.lean` | 4,245 | rational kernel + span/orthogonality + Int-cast layer |
| `hex-matrix-mathlib/.../Determinant/Core.lean` | 2,894 | |
| `hex-lll/bench/HexLLL/Bench.lean` | 2,921 | **bench file larger than the 2,532-line library** |
| `hex-lll-mathlib/.../Independent.lean` | 2,606 | longest single proof `swapStep_valid` ~310 lines, but cleanly decomposed with named `have`s |

Suggested (opt-in) splits:
- `Int.lean` → `Int/DetVec.lean`, `Int/ScaledCoeffs.lean`,
  `Int/Lattice.lean`, `Int/Reconstruction.lean` (the canonical-coeff
  sub-namespace around lines 3154–5693 is the natural seam).
- `Determinant.lean` could split the bordered-minor lemma library
  (~lines 4800–10500) into its own file.
- `Bench.lean`: the comparator/Isabelle/fpLLL protocol code (~lines 739–1017)
  could move to a bench helper module, but this is cosmetic — bench files
  don't gate anything.

None of these block release; they are maintainability investments.

---

## 7. Unmaintainable proofs

**Low severity — the proof layers are healthy.** No `sorry`, no
`maxHeartbeats` overrides, no brittle giant `simp only [...]` lists (longest
observed is ~8 lemmas), no deeply nested tactic forests. The longest proof,
`swapStep_valid` in `hex-lll-mathlib/.../Independent.lean` (~310 lines), is
long because it touches every affected matrix entry, but is readable: it uses
explicit case analysis and named intermediate `have`s rather than a wall of
tactics. The main *future* maintenance risk is the over-long lemma names
(§3) and the proof-only `scaledCoeffRows` parallel formulation (§2), both of
which make the `hex-gram-schmidt` proofs harder to navigate than they need
to be.

---

## 8. Packaging note for maintainers (not a code defect)

The `*-mathlib` lakefiles pin the full transitive Hex closure explicitly
(e.g. `hex-lll-mathlib` pins `HexLLL@ff9729a`, `HexMatrix@20e4c73`, …)
because Lake will not reconcile mismatched diamond pins. Those pins already
drift from current HEADs (`hex-lll` HEAD is `be903fe`, not the pinned
`ff9729a`). This is expected churn, but worth a one-line note in each
`*-mathlib` README/lakefile: **bump the executable repo and its `*-mathlib`
partner in sync, or the diamond will fail to resolve.**

---

## Recommended remediation order

1. **[BLOCKER] Fix the SPEC cross-references** in `hex-lll` (12),
   `hex-matrix` (5), `hex-gram-schmidt` (1) — prune, inline, or absolute-URL.
2. **README polish** — add an fpLLL enable/fallback paragraph to `hex-lll`;
   add the "bump in sync" note to the three `*-mathlib` repos.
3. **Cheap code hygiene** — promote the duplicated `rowSwap_*_int` lemmas to
   public and delete the mathlib copies; add docstrings to the ~7 undocumented
   public `hex-gram-schmidt` defs; add the σ-chain and `intervalPrec` rationale
   comments.
4. **Optional: dead-code trim** — confirm whether the `scaledCoeffRows`
   bridge lemmas are still needed; if not, remove the family.
5. **Optional: rename pass** — shorten the 50–70-char lemma names, pushing
   qualifiers into namespaces.
6. **Optional: file splits** — `Int.lean` and `Determinant.lean`, if/when the
   proofs need further work.

Items 1–3 are an afternoon; 4–6 are incremental and can land post-release.

---

## Appendix — sizes and metrics

```
repo                       lean files   total LOC   CI   sorry/axiom/native_decide
hex-matrix                  9            18,227      yes  0/0/0
hex-matrix-mathlib          7             5,384      yes  0/0/0   (1 "sorry" = docstring word)
hex-gram-schmidt            7            13,674      yes  0/0/0
hex-gram-schmidt-mathlib    4             5,862      yes  0/0/0
hex-lll                     7             6,203      yes  0/0/0
hex-lll-mathlib             4             4,468      yes  0/0/0
```

Largest files: `Determinant.lean` 10,591 · `Int.lean` (gs) 8,318 ·
`Bench.lean` (lll) 2,921 · `Core.lean` (matrix-mathlib) 2,894 ·
`Independent.lean` (lll-mathlib) 2,606.

## Appendix — commands used (re-runnable)

```bash
cd /Users/kim/projects/lean
# hygiene sweeps (per repo)
grep -rn '\bsorry\b\|axiom\|native_decide' <repo> --include='*.lean'
grep -rn 'set_option maxHeartbeats\|TODO\|FIXME\|HACK' <repo> --include='*.lean'
# missing SPEC targets
for d in hex-matrix hex-gram-schmidt hex-lll; do
  test -f $d/SPEC/benchmarking.md; test -f $d/PLAN/Conventions.md; test -f $d/libraries.yml
done
# dangling SPEC refs
grep -rnE 'benchmarking\.md|/PLAN/|libraries\.yml|\.\./\.\.' <repo>/SPEC/
# long names
grep -rhoE '\b[A-Za-z][A-Za-z0-9_]*(_[A-Za-z0-9]+){6,}\b' <repo> --include='*.lean' \
  | awk '{print length, $0}' | sort -rn | uniq | head
# scaledCoeffRows usage
grep -rn '\bscaledCoeffRows\b' hex-gram-schmidt --include='*.lean'
# file sizes
find <repo> -name '*.lean' -not -path '*/.lake/*' -exec wc -l {} + | sort -rn | head
```
