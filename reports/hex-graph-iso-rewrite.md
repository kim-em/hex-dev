# HexGraphIso rewrite plan

This note records the phases of the hex-graph-iso rewrite and is the design
note the directive issues cite. The SPEC is revised in the last Phase A PR.

## Context

`HexGraphIso` (85k lines, 114 files, written in 45 commits over four days in
September 2026) implements nauty 2.9.3's dense basic mode, proves the pruned
search computes the declarative canonical form, and provides `graph_iso`.
It works: no sorries, no axioms, conformant with nauty on 6k fixtures plus a
33k-case campaign, 3 to 4 times slower than nauty at n = 8..16.

It is the residue of its development. The audit found:

| problem | size |
|---|---|
| Pruning-correctness proof: one induction over the four imperative search functions split across 35 `SearchOutcome*` files in a linear import chain, 68 invariant record types | 28k lines |
| `cheapautom` theory: seven near-identical 200 to 400 line case analyses for cell shapes 2, 3, 4, 5, {3,3}, {4,2} | 10k lines |
| Two abandoned attempts at the same theorem (model ladder `searchNode`/`searchNodeA`/`searchNodeG`, and the `Quartet*` induction) plus `FirstPath`, most of `Complete`, `TargetCell` | about 4k lines dead |
| Tactic checker at four representations (`checkKey`, `checkKeyFlat`, `checkKeyLit`, `checkKeyP`); separators mirror this | about 4k lines |
| Six parallel encodings of the algorithm (`Reference`, spec, executable, model ladder, checker, kernel checker) | |

Plus: the bounded certificate API in `Ops` is documented as the user surface
and used by nothing; two of four negative tactic routes are unreachable at
default limits; `ModuleBoundaryTests` is imported by the library umbrella;
`run`/`runTraced` duplicate 40 lines; `Perm.inv` is quadratic; `maxNodes`
means five different things; about 25 module docstrings narrate chronology or
cite a SPEC section that no longer exists.

Two faithfulness findings from reading the port against `nauty.c`:

- The code-1 leaf admission test deviates. `Search.lean:144-148` requires
  `firstcode[level+1] == codeSentinel` and always runs `isautom`;
  `nauty.c:934-940` requires only `eqlev_first == level` and admits on
  `gca_first >= noncheaplevel || isautom(..)`. The original port had nauty's
  test; PR #9985 changed it to simplify the proof. The difference is
  observable only on a 15-bit refinement-code collision, which the campaign
  cannot exercise, and it costs an `isautom` scan per code-1 leaf inside
  cheap subtrees.
- `processnode` allocates `workperm` on every off-path node
  (`Search.lean:139`); nauty uses a global scratch.

What is good and must survive in shape: the declarative spec and its
invariance/achievement proofs (`Nauty/CanonSpec`, `SpecIso`, `Achieved`,
`SpecCanon`, about 6k lines), the single trusted certificate checker
(`Nauty/Cert`, `CanonForm`, about 3.4k), the executable port (`Nauty/Search`,
`Refine`, `VSet`, about 5k), and the public surface (`Ops`, `Uncolored`).

## Requirements (unchanged)

1. Faithful nauty 2.9.3 basic mode: observable agreement (forms, labels,
   visited-node counts) pinned by the oracle and campaign. No line-by-line
   requirement; faithfulness is made easy to check by a correspondence table
   in the search's module docstring mapping each `nauty.c` decision point
   (with line references into `vendor/nauty-2.9.3`) to the Lean declaration.
2. A proof that the search's pruning is correct (`canon G = specCanon G`).
3. The `graph_iso` tactic (coloured, uncoloured, Mathlib extension).
4. Performance at least as good as today (cactus sweep, per-node fit).

No users, no backward-compatibility constraints: names, modules, SPEC, and
the manual chapters may all change.

## Decisions (2026-09-05)

- Phase A first: cleanup with no change to the search's behaviour, including
  reorganizing the `SearchOutcome` chain and the `SmallCell` family by
  concept now.
- Spike S in parallel with A: a structured second executable, no proofs,
  measured for conformance and speed. Go/no-go for Phase B.
- Phase B (if the spike passes): prove the structured search and delete the
  chain. Otherwise Phase C: keep the literal port and prove it the same way.
- Tactic collapses to witness + certificate + root separator; drop the
  pairwise and two-code routes, `Pairwise`, `PairwiseSound`, `Reference`,
  `Lex`.
- The literal port is not kept after the spike; correspondence table instead.
- Delivery: revised SPEC and this plan in the repo, a directive-issue series
  for pod agents, and the first PR opened now.

## Constraints every PR must respect

- Any non-comment change under `HexGraphIso/`, `HexGraph/`,
  `bench/HexGraphIso/Cactus.lean` or `scripts/plots/hexgraphiso-cactus.py`
  requires `scripts/bench/graphiso_cactus_sweep.sh` on chungus2 and the
  data, manifest and figures committed with it
  (`scripts/bench/check_graphiso_sweep_freshness.py`, `ci.yml:103`). A file
  move is a delete plus an add, so move PRs need a sweep; batch them.
- `HexManual/Chapters/NautyAlgorithm.lean` cites about 40 `Nauty` names by
  Verso role and `HexManual/Chapters/HexGraphIso.lean` cites
  `Pairwise.search`; `lake build HexManual` is a required check on every
  rename or deletion.
- `scripts/release/released.yml` lists `HexGraphIso.TacticTests` as the
  test module; the manifest must follow any test-target change.
- Style: `SPEC/writing-style.md` and `.claude/CLAUDE.md` (short verb-noun
  names, no process narration, no `axiom`, no `native_decide`).
- A peer session `hex-graph-iso-perf-fix` is active; any change it lands
  under `HexGraphIso/` moves the sweep baseline and must be rebased onto.

## Phase A: cleanup, behaviour-neutral

### A1. Target layout

Top level of `HexGraphIso/`:

| module | from | purpose |
|---|---|---|
| `Perm` | same, `inv` by one scatter pass | permutations and labels |
| `Colored` | same + `CanonResult`, `ColorSorted`, `colorSortedCheck` from `Reference.lean:34-73` | coloured graphs, relabelling |
| `Iso` | same | `IsIso`, `Isomorphic`, `checkIso` |
| `Limits` | `Canon.lean` minus `SearchLimits`, `searchCost` | `ReplayLimits`, `checkCost`, `checkIso?` (the Mathlib positive route uses these) |
| `Ops` | same minus lines 182-338 | `canonicalize`, `canon`, `label`, `findIso`, `isIso` and theorems |
| `Uncolored`, `Families`, `Random` | same | |
| `Kernel/IsoLit` | `IsoLit.lean:1-110` | positive-route kernel checker `Kernel.checkIso` |
| `Kernel/Packed` | `Nauty/Packed` + `IsoLit.lean:152-210` + `NodePacked.lean:1593-1740` | packing, `Kernel.packRows` |
| `Kernel/CheckKey` | `NodeLit` (internal, unexposed) + `NodePacked` | `Kernel.checkKey`, `Kernel.checkKey_eq`, `Kernel.not_isomorphic_of_checkKeys` |
| `Kernel/RootCode` | root parts of `Separator`, `SeparatorPacked` | `Kernel.rootCode`, `Kernel.not_isomorphic_of_rootCode` |
| `Tactic` | collapsed | `graph_iso` |
| `TacticTests`, `ModuleBoundaryTests` | test target only | |

Deleted: `Reference`, `Lex`, `Pairwise`, `PairwiseSound`, the two-code
separator halves of `Separator`/`SeparatorPacked`, `NodeLit`/`NodePacked`/
`IsoLit` as files.

`Nauty/` by concept:

| dir | modules | purpose |
|---|---|---|
| `Nauty/Search/` | `Bits`, `VSet/{Basic,Card,Nat}`, `Refine`, `Search` (the literal port until Phase B replaces it) | the executable port (hot path) |
| `Nauty/Spec/` | `CanonSpec` (+ `incMax`), `Equivariance`, `CellPerm`, `CellPermLoop`, `SpecIso`, `Achieved`, `SpecCanon` | declarative form, invariance, achievement |
| `Nauty/Cert/` | `Cert` (+ `keyLe_cons_tail`; minus `searchNode`, `certifyNode`), `CertAutom` (one budgeted `certifyKey?`), `CanonForm`, `Translator`, `TraceAgree`, `CertTotal`, `CertReplay`, `CertStore` | checker, producer, replay spine |
| `Nauty/Equitable/` | `Basic` (= `Equitable`), `Step`, `Fix`, `Root` | `refine` yields equitable partitions |
| `Nauty/SmallCell/` | `Guard` (= `SmallCell`), `Descent` (`Branch` + `Iter`), `Flips` (`Triple` + `Pair`), `Exotic` (`Exotic` + `Exotic2` + `Exotic3`), `Transitive` (`Leaves` + `All` + `Tie`, headline `stabilizer_transitive` = today's `flipData_of_subtreeOk`, and the all-leaves theorem `descPath_leafRows_all`) | the `cheapautom` theory |
| `Nauty/Invariant/` | `Refine` (= `SearchInv`), `Reach` (`TranscriptionInv` + `SearchReach`), `Codes` (= `CodeFaithful`), `Leaves` (= `LeafFaithful`), `Domination` (live 76 decls), `Orbits` (`OrbJoin` + `SearchOrbit.lean:563-830` + `QuartetLoop`), `Stabilize`, `Autos` (= `AutosLedger`), `Store` (= `StoreValid` + `SmallCellTie.lean:137-368`), `Coverage` (= `LoopCoverage`), `Incumbent` (`QuartetStmt.lean:1-170` + `QuartetNode`), `TargetCell` (closure of `maketargetcell_eq_spec` only) | per-event facts about the search state |
| `Nauty/Model/` | `Node` (`Cert.searchNode` + `SearchModel`), `Autom` (= `SearchAutom`), `Store` (`SearchOrbit.lean:1-562`) | the pruned-evaluator ladder, kept as lemma source for Phase B; no live consumer |
| `Nauty/Correct/` | `Outcome` (= `SearchOutcome`), `Base` (= `SearchOutcomeProof`), `Unwind` (`Target`, `Return`, `Located`, `LocatedProof`, `Trail`), `State` (`Induction`, `Ledger`), `Frames` (`First`, `Loop`), `RunInv` (`History`, `Event`, `Result`, `Mutual`, `SearchCoset`), `Exit` (`Final`, `Prune`, `Exit`), `Sweep` (`Sweep`, `Total`, `Carry`, `Gate`, `Step`, `Complete`), `OffPath` (`OtherLoop`, `Leaf`, `GateFail`, `OtherNode`, `OtherTotal`), `FirstPath` (`FirstLoop`, `FirstHyp`, `FirstSweep`, `FirstNode`), `Certify` (`Root`, `Certify`) | the induction proving `canonSpecKey = tracedKey`; import order is linear so consecutive merges are safe |

### A2. Deletions and salvage

| delete | salvage |
|---|---|
| `Nauty/FirstPath.lean` | none |
| `Nauty/Complete.lean` | `keyLe_cons_tail` to `Cert` |
| `Nauty/TargetCell.lean` outside the closure of `maketargetcell_eq_spec` (:284) | closure to `Invariant/TargetCell` |
| `Nauty/QuartetStmt.lean:171-591` (`dominated_of_root` :566, `certifyCanon?_isSome_of_root` :580) | `nodeKey` :50, `stInc` :82, `stInc_eq_ghost` :115 to `Invariant/Incumbent` |
| `Nauty/SearchOutcome.lean:1884-1931` (`dominated_of_result`, `certifyCanon?_isSome_of_result`) | none |
| `Nauty/Domination.lean`: the 97 declarations outside the closure of the live names, including `FirstDescOk` (2260-2425) | live set to `Invariant/Domination` |
| `SmallCellBranch.lean` `hOdd_of_defect_le` | none. The all-leaves theorem `descPath_leafRows_all` (`SmallCellAll.lean:95`) and its chain are dead in the literal-port proof only because that port always runs `isautom`; the spike restores nauty's admission test and Phase B consumes them. Keep, reorganized. |
| `Ops.lean:182-338`, `Canon.lean` `SearchLimits`/`searchCost`, `Tactic.lean:61-69` | none |
| `Nauty/Cert.lean:1408-1437` `certifyNode` | `validateKey?` stays |
| `CertAutom.lean:306-336` three producer wrappers | one `certifyKey? (budget : Option Nat)` with one soundness theorem |
| `Search.lean:457-513` `run` | `run := (runTraced ..).result`; `TraceAgree` becomes `rfl` or is deleted |
| `Perm.preimage` linear scan | `inv` by scatter; `get_preimage`/`preimage_get` restated |
| `HexGraphIsoMathlib/TacticSupport.lean:107-145`, `Encode.lean:172` `canon_encode_indep`, `Basic.lean:100` `Colored.singleColor` | none |
| Conformance `#guard`s on the deleted API (`conformance/HexGraphIso/Conformance.lean:123-147, 225-244`), `bench/HexGraphIso/Bench.lean:143, 213`, `Profile.lean:76, 95-98` | rewritten against the surviving API |
| Duplicated private counting lemmas (`sum_range_*` in four files, `sum_excess_ge_countP` in three, `countP_*` in four, `getElem!_append_left` variants in four) | one copy each in `HexBasic/List.lean` or `Equitable/Basic` |

### A3. Tactic collapse

`NodePacked`'s `_eq` chain is stated entirely against `NodeLit`'s list clones
(`CtxRep`/`RepSt`), so re-proving the packed layer directly against the
`Array` originals is about 1.8k lines of new proof: not Phase A. Instead:
`Kernel/CheckKey.lean` keeps the list layer as unexposed internal
scaffolding, exposes only `Kernel.checkKey` (= `checkKeyP`), and proves
`Kernel.checkKey_eq` once by chaining the three existing `_eq`s. Same for
`Kernel.rootCode`, whose `not_isomorphic_of_rootCode` is proved from the
spec key's head-code lemma plus `canonSpecKey` invariance, dropping the
`sepCodes_eq_of_isomorphic`/`specNode_codes_two` detour.

Dispatch after collapse: positive = relabel shortcut then witness
(`Kernel.checkIso`); negative = root separator (always run, no `maxNodes`
check) then certificates, then a precise error naming the exhausted option.
`evalColored` and `tiePackedRows` computed once per side and shared across
routes. Trace routes: `relabel|witness|root|certs`;
`scripts/bench/graphiso_kernel_cost.py` and `scripts/plots/hexgraphiso-cactus.py`
read these and change in the same PR.

Options (`Tactic.Config`, `Hex.GraphIso.Tactic`):

| option | meaning | default |
|---|---|---|
| `maxSearchNodes` | nodes the compiled search may visit per graph, both the witness search and the certificate producer | 100000 |
| `maxCertRecords` | certificate records per graph the kernel replays | 100000 |
| `maxKernelSteps` | estimated kernel work (`checkCost n` per witness; `(records + autom + 2) * checkCost n` per certificate) | 5000000 |

Parse with a proper config elaborator, not string dispatch. The Mathlib
layer's positive route switches from `mkDecideProof` (double evaluation)
to the core witness route and emits `trace[graph_iso]`. The `Extension`
list stays but is registered by an attribute rather than a hardcoded name.

### A4. Naming

- `Nauty.canonicalize?` (untrusted label-check wrapper) renamed
  `Nauty.searchResult?`; `certifyCanon?_isSome_of_*` variants collapse to
  `certifyCanon?_isSome_of_keyEq` and `certifyCanon?_isSome`;
  `canonicalize?_eq_of_*` to `searchResult?_eq_of_checkCanon`.
- Kernel names into the `Kernel` namespace instead of `L`/`Lit`/`P`
  suffixes (`checkKeyP` to `Kernel.checkKey`, `KeyL` to `Kernel.Key`,
  `checkIsoLit` to `Kernel.checkIso`, `sepRootLitP` to `Kernel.rootCode`,
  `packRowsK` to `Kernel.packRows`).
- `flipData_of_subtreeOk` renamed `stabilizer_transitive` and made the
  `SmallCell` headline; `labInj_surj` moves out of `SmallCellTriple`.
- Not in Phase A (they alter the hot path or its proofs): `Label` wrapper,
  `Ctx` wrapper, `Int` levels, the `(lab, ptn)` two-array partition.

### A5. Docs

- Module docstrings rewritten to content only. Worst offenders:
  `Domination`, `Translator`, `Tactic`, `SmallCell*`, `CanonForm`,
  `NodeLit`, `NodePacked`, `IsoLit`, `Equitable`, `SearchOutcomeExit`,
  `SearchOutcomeMutual`; 71 files match the narration patterns
  (`obligation`, `sweep`, `B2`, `landed`, `the old`, `the fix`, `probe
  showed`, embedded numbered plans, "SPEC § Verified search refinement").
  Written once, for the final modules, after the moves.
- `HexGraphIso/SPEC/hex-graph-iso.md`: drop "Trace-driven production"
  (482-526) and the manual-chapter brief (761-929); rewrite "Verified search
  refinement" (527-634) as a description of `Nauty/Correct/`; rewrite the
  tactic section (635-721) and "Canonical certificates" (431-481) for the
  surviving API and options; fix the positive-route description (it
  describes the Mathlib layer today); record the code-1 admission deviation as
  a known divergence until the spike lands. README and umbrella docstring
  follow.
- `bench/HexGraphIso/ProofProbe/Support.lean` duplicates `TacticTests`
  fixtures; `conformance/HexGraphIso/EmitCampaign.lean:36-72` duplicates
  `EmitFixtures.lean:41-77`: one shared module each (the spike needs the
  shared case generator too, see S2).

### A6. PR sequence

| # | PR | sweep |
|---|---|---|
| 1 | `chore(graph-iso): move tests out of the umbrella`: `ModuleBoundaryTests` into `HexReleaseTests` (`lakefile.lean:889`), drop it and the duplicate `Nauty.Domination` import from `HexGraphIso.lean` | no |
| 2 | `refactor(graph-iso): delete dead proof code`: A2 rows 1-7; ladder to `Nauty/Model/`, `incMax` to `CanonSpec` | yes |
| 3 | `refactor(graph-iso): delete the bounded API and producer wrappers`: A2 rows 8-13, conformance/bench call sites | yes |
| 4 | `refactor(graph-iso): drop Reference, Lex and the pairwise decision`: `CanonResult`/`ColorSorted` to `Colored`; manual chapter citation replaced | yes |
| 5 | `refactor(graph-iso): one packed kernel checker`: `Kernel/`, new dispatch, new options, Mathlib positive route, scripts, tests | yes |
| 6 | `refactor(graph-iso): reorganize the search-correctness proof by concept`: 36 files to `Nauty/Correct/` | yes |
| 7 | `refactor(graph-iso): reorganize the remaining Nauty modules`: `Search/`, `Spec/`, `Cert/`, `Equitable/`, `SmallCell/`, `Invariant/`; dedupe counting lemmas; shared conformance case module | yes |
| 8 | `refactor(graph-iso): API names`: A4, manual updated | yes |
| 9a-c | `docs(graph-iso): content-only docstrings`: `Correct/`; `SmallCell/` + `Equitable/`; the rest | no |
| 10 | `docs(graph-iso): SPEC, README, umbrella` | no |

PRs 2+3 and 6+7 may be combined to save sweeps. Verification per PR: `lake
build HexGraphIso HexGraphIsoMathlib HexReleaseTests HexManual`,
`lake build HexGraphIso.Conformance`, the oracle
(`scripts/ci/run_oracles.sh` tuple for graphiso, pinning node counts), no
`sorry`; sweep PRs add the sweep, `check_graphiso_sweep_freshness.py` and
`graphiso_pernode_fit.py --check 0.2`; PRs 2, 6, 7 verify declaration-set
equality before/after (modulo the listed deletions); PR 5 checks
`trace.graph_iso` on the test corpus shows only the four routes.

## Spike S: the structured search (parallel with A)

Goal: a second executable, `Nauty.Engine`, with the same traversal as
nauty and a shape the Phase B proof can follow, measured before any proof
is written. No proofs. Every `nauty.c` line in 468-513 and 559-1086 is
either in its correspondence table or in the "pinned-out options" row.

### S1. Design

- One flat record `Search n` (nauty's globals, threaded linearly with
  `let mut st` so `Array.set!` mutates in place; nested sub-records would
  bump refcounts through two constructor levels). Proof-side grouping by
  views (`Search.incumbent`, `.cmp`, `.first`, `.gca`), not by layout.
  `workperm` allocated once in the record. Per-level quantities (`level`,
  `numcells`, `tc`, `tcell`, `tv1`, `index`, `refcode`) are function
  arguments.
- Two mutual functions replacing four: `node (first : Bool)` (nauty.c
  559-703 when `first`, 718-856 otherwise) and `sweep (first : Bool)`
  (650-692 / 827-853), fuel-recursive (the sweep re-reads a `tcell` that
  `shortprune`/`longprune` shrink mid-loop, so it cannot be a `for`).
  Helpers in nauty's order: `visit`, `recordFirst`, `compareCodes`
  (= `otherNodePrep`), `chooseTarget`, `firstterminal`, `classify`
  (929-973, with `testcanlab`/`updatecan` side effects), `leafExit`
  (975-1055) dispatching to `admit`, `install`, `pruneReturn`,
  `cheapCheck`, `child`, `afterChildFirst`, `afterSweep`, `recover` split
  into `recoverPtn` (the rescan) and `recoverLevels` (the four clamps).
- Exit and leaf types:
  `inductive Exit | done | unwind (target : Nat) (short : Bool) | fuel`
  with `needshortprune` carried as the `short` payload (set only at
  1003/1015/1054 in the expression that fixes the return level, consumed
  only by the loop at that level; the check at 817-821 is dead, which the
  current proof states as `NodeInv.shortClear`), and
  `inductive Leaf | internal | autoFirst | autoCanon | better (sr) | bad`
  for the five `processnode` codes.
- Restore nauty's code-1 admission test exactly (`nauty.c:938`,
  `gca_first >= noncheaplevel || isautom`), dropping the sentinel guard.
- `refine`, `breakout`, `maketargetcell`, `testcanlab`, `updatecan`,
  `orbjoin`, `fmperm`, `fmptn`, `pushAuto`, `shortprune`, `longprune`,
  `VSet` unchanged. Fuel `n + 2` for nodes, `n + 1` for sweeps.
- Output contract: `Engine.run` and `Engine.runTraced` with the same result
  types as `Search.lean:432, 504`, so `produceCand` (`CertAutom.lean:284`)
  and `certifyCanon?` re-point by one edit at go.

Behaviours the design keeps and the table names: workspace overwrite of
the last slot at 500 pairs so `shortprune` reads the pair just written;
`eqlevFirst := level-1` when `tc ≠ firsttc[level]`, only in the
`comp_canon < 0` arm; `allsamelevel` decrement only when
`tcellsize == index ∧ allsamelevel == level+1`, first path only, after
the sweep; `index` counts `orbits[tv] == tv1` for every `tv` including
skipped ones; `gcaFirst := level, stabvertex := tv1` after the first child
returns; `cosetindex := tv` for every first-path child; code 2 with
`numorbits` unchanged (pair and trace pushed, no `numgenerators`, no
`cosetindex` test, still short prune when `gca_canon ≠ gca_first`);
`orbits[cosetindex] < cosetindex` returning `gca_first` without a short
prune; `samerows` reuse; `level < canonlevel` deciding a tie before any
row comparison; `save`/`newlevel` arithmetic with `allsamelevel` limiting
and `noncheaplevel` extending the prune; `fmptn` only when
`level ≠ noncheaplevel`; `cheapautom` guarded by `noncheaplevel ≥ level`
on the first path and run after `processnode` off it; `longprune` only at
`tv == tv1` off the first path; `recover` clamps in order with
`eqlevCanon ≤ level` resetting `compCanon`; initial values (468-479, 493).

Correspondence table (module docstring, one row per decision point in
source order; columns nauty.c lines, abridged C, Lean declaration, note):

| nauty.c | C | Lean | note |
|---|---|---|---|
| 588 / 754 | `++stats->numnodes` | `visit` | before `doref`, both kinds |
| 771-787 | `eqlev_first`, canoncode trichotomy | `compareCodes` | other only |
| 794-807 | target cell iff `numcells < n && (eqlev_first == level \|\| comp_canon >= 0)`; hinted call iff `comp_canon < 0` | `chooseTarget false` | |
| 938-940 | `gca_first >= noncheaplevel \|\| isautom` | `classify`, arm `autoFirst` | restores the 2.9.3 admission test |
| 1001-1005 | `numorbits == save` | `leafExit .autoCanon` | no `++numgenerators` |
| 1051-1055 | `save`, `newlevel`, `needshortprune` | `pruneReturn` | payload on `Exit.unwind` |
| 817-821 | post-`processnode` `needshortprune` | none | dead |
| 619, 625-633, 698-701, 986-992 | user procs, `writeautoms`, schreier | none | pinned options |

### S2. Protocol

1. Module `HexGraphIso/Nauty/Search/Engine.lean` (or `Nauty/Engine.lean`
   before PR 7 lands; rebase onto the reorg), namespace
   `Hex.GraphIso.Nauty.Engine`, imported by the umbrella so `conformance/`
   and `bench/` see it; nothing on the answer path imports it.
2. Twin conformance in pure Lean: factor the case generators of
   `EmitFixtures.lean` and `EmitCampaign.lean` into
   `conformance/HexGraphIso/Cases.lean`; new executable
   `hexgraphiso_engine_twin` running `Nauty.runColoredTraced` and
   `Engine.runColoredTraced` on every fixture and campaign case, comparing
   `canonlab`, `canong`, all seven statistics, `autos` in order,
   `bestCodes`, final `orbits`; first mismatch prints the case. Also
   `--engine` modes on both emitters so `scripts/oracle/graphiso_nauty.py`
   pins the engine against real nauty (forms, labels, `numnodes`)
   independently. A few `#guard`s on the named cases in `Conformance.lean`.
3. Performance: `bench/HexGraphIso/Cactus.lean` gains a mode emitting
   `{family, name, n, lit_ns, eng_ns, nauty_ns, nodes, eng_nodes}` timing
   `Nauty.runColored` against `Engine.runColored` on the same instance; a
   small `scripts/bench/graphiso_engine_compare.py` prints per-family
   geometric-mean ratios and reuses `graphiso_pernode_fit.py`'s exponent
   fit on both columns; `bench/HexGraphIso/Profile.lean` gains an `erun`
   stage (paley61, kneser72, circulant64) for
   `graphiso_perf_side_by_side.sh`; `valgrind --tool=dhat` on
   `hexgraphiso_profile run` versus `erun` for blocks per node.
4. Pass criteria: zero twin mismatches over fixtures plus campaign; oracle
   green with `--engine`; `eng_nodes == nodes` on every sweep instance;
   per-family geometric mean `eng_ns/lit_ns ≤ 1.00` within noise, no
   instance above 1.05, kneser/johnson/hypercube expected below 0.9 from
   the restored admission test; `graphiso_pernode_fit.py --check 0.2` on the engine
   column, engine exponent ≤ literal + 0.02 per family; dhat blocks per
   node ≤ literal's; correspondence table complete; no `partial`, no
   `sorry`. Fail: a traversal difference not traceable to the literal
   port's own bug, or a slowdown two rounds of tuning do not remove.

## Phase B: proof of the structured search

Target: `canonSpecKey_eq_tracedKey` restated with `runColoredTraced` and
`tracedKey` (`CertReplay.lean:1060`) re-pointed at the engine, so
`certifyCanon?_isSome_of_keyEq`, `CertTotal`, `CanonForm`, and
`Ops.canonicalize_eq_certifyCanon` are untouched.

### B1. Architecture: one recursion, one policy

The ladder `Nauty/Model/` cannot be the target: its prunes are per-node,
while nauty's code 1 to 4 returns abort sweeps at several levels at once,
`(fix, mcr)` pairs prune far from the admitting leaf, and the engine
descends dominated subtrees when `eqlev_first == level` to harvest
generators. A rung with non-local exits has the engine's recursion shape,
so the two designs converge:

- `Generic.node`/`Generic.sweep`: the engine's recursion over a
  `Policy σ n` typeclass (`visit`, `descend?`, `leaf`, `skipChild?`,
  `afterChild`, ...). The engine is `Generic.node (σ := Search n)` at the
  nauty instance; write the engine directly first (the spike), then
  refactor and re-run the sweep to confirm the compiler specialises the
  typeclass away (`trace.compiler.ir.result`). If it regresses, keep the
  direct engine and prove `Engine.node = Generic.node` by unfolding.
- Trivial policy (`σ := Unit`, never prunes) reduces `Generic.node` to
  `specNode` (`CanonSpec.lean:155`): `generic_trivial_eq_specNode`.
- Generic soundness, in the shape of `searchNode_eq` and `searchNodeG_eq`:
  under `SoundPolicy`, `incKey σ' = keyMax (incKey σ) (prefixKey cs
  (specNode ..))`, the invariant is preserved, and `unwind t` below the
  level carries `Witness t σ'` (the current child subtree at level `t+1`
  is bounded by the incumbent), which intermediate loops transport and the
  loop at `t` turns into ordinary coverage.
- `SoundPolicy` obligations are local per decision and reuse existing
  lemmas: `skipChild?` via `childKey_of_orbPruned`, `longprune_carried`,
  `shortprune_carried`, `childKey_of_carried`; code prune via
  `codeInv_keyCmp_lt`, `specNode_keyLe_of_code_lt`; leaf verdicts via
  `tied_full_keyCmp`, `leafEvent_faithful`, `updatecan_inv`; unwinds via
  `cellStab_of_scatter`, `orbjoin_orbSound`, the frozen machine for
  `eqlevCanon`, and the small-cell subtree for `noncheaplevel - 1`
  (`descPath_leafRows_all`, `leafRows_eq_of_descPaths`, `CheapDesc`);
  store validity via the small-cell theorem for the restored admission test and
  `checkAutom_scatter_of_leafRows_eq` for code 2; invariant maintenance
  via `CodeCmpInv`, `FirstCodeInv`, `recover_machines`,
  `otherNodePrep_frames`, `firstterminal_*`, `AutosOk`/`PairOk`,
  `OrbSound`, `refine_equitable`. Keeping `recover`, `firstterminal`,
  `compareCodes`, `pushAuto` as the same functions on a record with the
  same field names makes those lemmas transfer by renaming.
- The invariant is one record of about ten clauses (sizes and reach,
  `CodeCmpInv`, `FirstCodeInv`, `CanongInv`, `CellStab` of `genTrace`,
  `GenTraceOk`, `AutosOk`, `OrbSound`, `gcaFirst/gcaCanon < level`,
  `noncheaplevel ≤ level`, `cosetindex < n`) instead of 68 types, because
  unwinding and sweep coverage live in the theorem's conclusion.
- Reach facts consumed by `CertTotal` (`canonlab_cellsReach`,
  `runColoredTraced_result`) re-proved on the generic recursion as
  policy-independent lemmas from `refine_reachAt`/`breakout_reachAt`.

### B2. cheapautom rewrite (independent of B1)

The live consumer is `pairOk_fmptn_of_subtree` (`SearchOutcomeLedger.lean:219`),
which needs: for an equitable partition with `cheapautom`, the cell
stabilizer in `Aut(G)` acts transitively on every cell
(`stabilizer_transitive`, signature kept), plus the all-leaves theorem for
the restored admission test. Uniform proof replacing the seven `*_flip_data` case
analyses:

- Lemma F (transposition sets): a set of disjoint within-cell
  transpositions is an automorphism iff every fixed vertex sees both
  members of each pair alike and pairs see each other consistently. One
  proof replaces `flip_rows`, `triple_flip_rows`, `sw1_bits`, `sw2_bits`,
  `sw3_bits`.
- Lemma D (balanced differ set): for u, v in one cell and any cell D,
  equitability balances the vertices of D distinguishing u from v between
  N(u) and N(v); if D has at most one other vertex it is empty.
- Shapes: pairs with `PairReach` closure, triple, {4} (`reg4_comp`), {5},
  {3,3}, {4,2}, each 80 to 200 lines on F and D; a dispatcher from
  `exc_sum_eq_defect`.
- All-leaves theorem by induction down the subtree from
  `stabilizer_transitive` plus refine equivariance, replacing the
  bisimulation in `Descent`.

Layout `Nauty/SmallCell/{Guard,Flip,Count,Shapes,Transitive}.lean`,
estimate 1.5k lines against 7k today.

### B3. Size, risks, deletions

New: generic recursion plus trivial instance 0.5k; generic soundness 3-4k;
nauty policy invariant and transitions 2-3k; decision justifications
2-3k; reach lemmas 1k. Total 9-12k. Deleted on completion:
`Nauty/Correct/` (27.8k), `Invariant/Incumbent`, `Coverage`,
`TraceAgree`, most of `Invariant/Reach`, the `SearchSt`-specific half of
`Domination`, the literal `Search.lean` (the engine takes its place and
name, keeping the correspondence table). Net about 20k lines fewer, plus
5.5k from B2.

Risks in order: the cheap-return witness (code equality across a cheap
subtree; confirm the reusable statement early from `SearchOutcomePrune`
and `SmallCellTie`); typeclass specialisation of the mutual recursion
(mitigated by direct-then-refactor); `Exit.fuel` unreachability (small,
the level-versus-fuel bound); reach re-proof (mechanical).

Phase C fallback (spike fails): same generic recursion and policy, with
the literal port proved equal to `Generic.node` at the nauty policy by
unfolding, then the same soundness theorem.

## Agent assignment

| work | who | when |
|---|---|---|
| Phase A, PRs 1 to 10 | Opus pod workers, from `directive` issues | now |
| Spike S2 tooling (shared case module, twin executable, cactus mode, compare script, profile stage), built first against the literal port | Opus pod workers | now |
| Spike S1, the engine and its correspondence table | Fable, dispatched by Kim | not before Tuesday 2026-09-08, 14:00 AEST |
| Phase B1, B2 and the Phase C fallback | Fable, dispatched by Kim | after the spike's decision |

The Fable items are written up now as complete, self-contained issues so
separate agents can be set on them at will. Pod runs Opus only
(`accepted_models = ["opus"]`); its queue excludes `blocked`, but
`check-blocked` clears that label unless a `depends-on: #N` line names an
open issue, and stale claims release after four hours. So the Fable items
carry `model: fable`, the `blocked` label, and `depends-on:` a release
issue (`directive: release the Fable work on hex-graph-iso`, itself
`blocked` on itself so housekeeping never clears it). To dispatch one,
remove its `blocked` label (or close the release issue to unblock them
all) and claim it by number from a Fable session; Opus workers never see
it while blocked. B items additionally depend on the S1 issue.

## Delivery artifacts

1. `reports/hex-graph-iso-rewrite.md`: this note; the SPEC revision lands in PR 10.
2. Directive issues (`directive` label; body format `libraries:`,
   `depends-on:`, `## Goal`, `## Acceptance`, `## Out of scope`): one per
   PR in A6 with `depends-on` chaining them, one for the spike (S1, S2,
   decision criteria as acceptance), one umbrella for Phase B with B1, B2
   as sub-issues blocked on the spike's decision.
3. PR 1 (`chore(graph-iso): move tests out of the umbrella`) opened from
   this session: `lakefile.lean:889` gains `HexGraphIso.ModuleBoundaryTests`,
   `HexGraphIso.lean` drops that import and the duplicate
   `Nauty.Domination` import; verify with
   `lake build HexGraphIso HexGraphIsoMathlib HexReleaseTests HexManual`.
