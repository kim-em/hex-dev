# Verified search refinement: plan

Standalone working plan for finishing the last open theorem of
`HexGraphIso`. Written for a session with no prior context.

**Work on the branch `graphiso-refinement-work` in `kim-em/hex-dev`.** It
contains everything this plan describes, builds green (`lake build`, exit
0), and is ahead of `main`: some of the material below has not merged yet
and is only on that branch. Do not start from `main`, and do not wait on
any pull request. Every file reference below resolves on that branch.

## The goal

`certifyCanon?_isSome`: certificate-checked canonicalization never fails.
It is not currently declared in code; only the intended statement appears
in the SPEC.

This programme is a release requirement: `HexGraphIso/SPEC/hex-graph-iso.md`
states it as one, and no first release happens without it. The per-prune
preservation theorems that release condition 4 names largely exist already
(see "Available proved components"); what remains is assembling them into
the totality statement above.

## Two objects, and why the theorem is hard

`HexGraphIso` reimplements dense `nauty` 2.9.3's canonical labelling.
Faithfulness to the C program is a conformance claim, not a theorem.
Correctness of the Lean implementation is a theorem, and it compares two
different things.

- **The specification.** `specNode` (`HexGraphIso/Nauty/CanonSpec.lean`) is
  a pure recursion computing the maximum over a node's whole subtree of a
  `Key`, a code list paired with leaf rows, folded by `keysMax`.
  `canonSpecKey G` is the root value. It prunes nothing.
- **The transcription.** Four mutually recursive imperative functions in
  `HexGraphIso/Nauty/Search.lean`: `firstPathNode`, `firstChildLoop`,
  `otherNode`, `otherChildLoop`, with `processnode` (leaf handling),
  `refine`, `breakout` (individualisation), `recover` (unwind) and
  `otherNodePrep`. This is what runs, and it prunes by refinement code, by
  orbits, by stored automorphisms, by `shortprune` and `longprune`, and by
  the `cheapautom` small-cell rule.

The theorem says the pruned run computes the unpruned maximum.

## The reduction

`CertTotal.lean` reduces the goal to "the produced certificate replays".
`CertReplay.lean` reduces that to `certifyCanon?_isSome_of_dominated`,
consuming two facts:

- **(a) domination**: `canonSpecKey G = tracedKey G`.
- **(c) certificate store validity**: the `hval` premise at
  `CertReplay.lean:1174`, an `AutomsOk` over the *produced certificate*.

**(b) the replay spine is closed**, and was independently reviewed as
structurally sound: `certifyNode_replays` (`CertReplay.lean:697`) with the
root strictness contradiction at `CertReplay.lean:1156`.

## Available proved components

These are proved lemmas, not completed prune correctness: their
preservation and use across a final induction remain open.

- `refine_equitable` (`EquitableFix.lean:827`). **Its precondition is not
  free**: it requires a `CertInv` hypothesis (`EquitableFix.lean:838`). The
  child seed is `certInv_breakout` (`SmallCellBranch.lean:858`); the root
  needs its own all-cells-active seed, which does not yet exist.
- `defect4_flip_data` (`SmallCellExotic3.lean:1592`), deductively
  exhaustive over the target excess split. Instrumentation found the cases;
  the theorem does not depend on it.
- `descPath_leafRows_all` (`SmallCellAll.lean:96`).
- Orbit results in `QuartetLoop.lean`: `orbitClose_of_wordConn` and
  `orbitStepSet_orbitClose_nn` (the closure saturates within `nn` rounds),
  `childKey_of_wordConn`, `childKey_of_orbitPtr`, `childKey_of_ptrIter`.
  **Closed locally, not end to end**: nothing yet proves that a pointer
  chase terminates at a child the actual loop explored.
- The `fmptn` ledger (`AutosLedger.lean`), cell stabilization
  (`Stabilize.lean`), the comparison machines (`CodeFaithful.lean`), the
  leaf event (`LeafFaithful.lean`).
- The root assembly in `QuartetStmt.lean` (`dominated_of_root`,
  `certifyCanon?_isSome_of_root`): **algebraically closed but highly
  conditional**, since it assumes the currently false `NodeConcl` and, at
  the second theorem, the certificate `AutomsOk` that nothing proves.

## What is open

### 1. Certificate store validity

`GenTraceOk` (`SmallCellTie.lean`) concerns generators the *search*
records. The reduction consumes `AutomsOk` over the *certificate*. These
are different: `produceCand` admits the traced generators, then
`certifyNodeAutom` (`CertAutom.lean`) harvests further `composeOnto`
candidates from its own leaves. No theorem derives the certificate fact.
`Translator.lean`'s inventory lists `isPerm_of_trace` and the `composeOnto`
permutation facts as open.

**This is independent of all the geometry, but only if proved directly
from permutation preservation.** It stops being independent if you try to
route it through `GenTraceOk`, whose scan-free code-one arm depends on
first-path geometry. What the proof needs:

- an `AutState` invariant that every present labelling (`firstLeaf`,
  `prevLeaf`, `refLeaf`) is a permutation of `[0, n)`;
- a mutual induction for `certifyNodeAutom` returning both `GensOk` for the
  output store and `AutomsOk` for the emitted certificate;
- a cache-validity invariant for `usableGens`: reuse is controlled by
  `st.gen` (`CertAutom.lean:214`), and `GensOk st` alone does not describe
  the cached array passed to `witness?`;
- a `composeOnto` permutation theorem under permutation and size
  assumptions on both labellings, not an unconditional claim about every
  argument `AutState.admit` accepts.

`GensOk.admit` and `GensOk.foldl_admit` (`Translator.lean:832`, `:890`) are
already parameterized for this.

### 2. The target-cell bridge

The specification selects its target through `joinTest`
(`CanonSpec.lean:89`); the transcription tests adjacency of the first
labelled vertex (`Refine.lean:1858`, `bestcellRow` at `:1864`). Comments
assert agreement on equitable partitions; no theorem proves it, and nothing
identifying an actual child sweep with `specNode`'s children is sound
without it.

**Do not try to prove the hinted forms agree.** `targetcell` gives an
admissible hint absolute priority (`Refine.lean:1906`) while
`specTargetcell` is hint-free (`CanonSpec.lean:137`), and equitability does
not make every valid hint equal to `bestcell`. Concrete counterexample: the
empty graph on four vertices with equitable cells `[0,1]` and `[2,3]`,
where `bestcell` ties and selects position 0 while the valid hint 2 gives
`targetcell … 2 = 2`. The theorem family to prove is:

- `bestcell = specBestcell` under equitability and the usual bounds;
- `targetcell … (-1) = specTargetcell`;
- `maketargetcell … (-1) = specMaketargetcell`;
- a hinted version only under the extra premise
  `hint.toNat = specTargetcell …`.

The `compCanon < 0` hinted branch (`Search.lean:362`) may instead be
discharged as already dominated, avoiding target agreement there entirely.

Correction to prose you may encounter: any comment calling `maketargetcell`
a position-level policy is **false**, since `bestcellRow` reads
`ctx.g[lab[...]]`.

### 3. The induction's statement is wrong

`QuartetStmt.lean` states `NodeConcl` for the node functions and
`LoopConcl` for the loops, over `incMax : Option Key → Key → Key` with
`none` as bottom. `QuartetNode.lean` records the counterexample and holds
the incumbent frame lemmas; read both before restating anything.

- **`NodeConcl` is false.** It splits on the returned level, with
  whole-subtree absorption at exactly `Int.ofNat level - 1` and a carried
  payload strictly below. `firstChildLoop` abandons its sweep when a child
  returns below `level` and returns that value unchanged, so a child
  returning `level - 1` makes the node return `level - 1` with later
  siblings never visited, where `full` demands whole-subtree absorption and
  `carried`'s strict guard supplies nothing. `otherNode` has the same shape
  twice. Reachable, not vacuous. The split also conflates three distinct
  outcomes: code 1, code 2, and frozen unwinds. Replace it with explicit
  outcome variants.
- **`LoopConcl` is insufficient**, carrying no coverage of skipped
  children, so the node cannot reconstruct absorption without reproving the
  loop's induction. The loop should own every skip it performs and return
  coverage.
- **Three fuels are conflated**: logical specification depth, the node's
  runtime fuel, and the loops' independent `cfuel`, whose exhaustion
  branches return `none` (`Search.lean:289`, `:400`). A general loop
  theorem must rule out exhaustion or represent it as a distinct outcome.
- **Code 2 has no payload.** `CarrierOut` (`QuartetStmt.lean:101`) is
  specifically a `firstlab → lab` carrier, built at `Search.lean:142`. Code
  2 constructs `canonlab → lab` (`Search.lean:158`) and may return either
  `gcaCanon` or `gcaFirst` (`Search.lean:182`), and `gcaCanon` plus
  `canonlab` do not reconstruct the canonical child's position history.
  Either add separate first and canonical carrier outcomes with both path
  histories, or use a generic payload storing the reference labelling, the
  ancestor node, the guiding offset, and evidence that its child is already
  covered by the loop accumulator.
- **Loop coverage must be transitive.** `longprune_carried` and
  `shortprune_carried` (`AutosLedger.lean:316`, `:352`) produce a survivor
  of the *new* filtered set, not necessarily an already explored child, and
  `tcell` is rewritten mid-loop by both filters. Carry an evolving
  invariant (a removed vertex maps to an explored child or to a still-live
  survivor) and resolve it to explored-child coverage only on completion.

### 4. Path geometry

`FirstDescOk` (`Domination.lean`) assumes the current and first descents
chose the same target-position sequence. It cannot be an invariant field:
it is false at interior nodes the search passes with the gate open. Derive
it at the code-one gate instead; its derivation needs item 2.

Its only consumer is the scan-free generator validity arm.

**Do not remove run store validity from `DomOk`.** Its `genTraceOk`
(`Domination.lean:1682`) is run-side and remains necessary for orbit skips
and generator-return transport. The rule is: do not add certificate
`AutomsOk` to `DomOk`, prove that separately per item 1; retain run-side
`GenTraceOk`. `firstKeyLe` is obsolete under wholesale absorption and can
go.

## Recommended order

1. **Certificate store validity** (item 1), including the leaf-option and
   cache invariants. Independent, and closes the (c) side of the reduction.
2. **The unhinted target-cell bridge** (item 2), explicitly refuting or
   restricting the hinted form. Small, foundational, and its counterexample
   materially affects which branches the statement must cover, so it comes
   before the statement is redesigned.
3. **Design the new conclusion in one pass**, separating logical depth,
   node runtime fuel and loop `cfuel`, with explicit outcome variants.
4. **Add the evolving loop-coverage invariant** and resolve it to
   explored-child coverage on completion.
5. **Add both first-path and canonical-path history**, including ancestor
   state and guiding offset.
6. **Close representative cases for code 1, code 2, and the non-generator
   `pruneReturn` cases** before committing to the mutual statement.
7. **Prove the mutual induction, the root result, and the `n = 0` branch.**
   The root assembly assumes `n ≠ 0`; `CertTotal.lean:233` already contains
   the direct zero case. Check the root boundary explicitly: level one
   returns zero, which is the ambiguous boundary that invalidated
   `NodeConcl` (`QuartetNode.lean:167`).

On `searchNodeG` (`SearchOrbit.lean`): keep it as a semantic endpoint, not
as the object the transcription simulates branch for branch. It uses
pairwise `autPruned` rather than orbit closure (`:76`), always uses
`specMaketargetcell` (`:103`), and has no `shortprune`, `longprune`,
`gcaFirst`, `gcaCanon`, `pruneReturn` or return-level protocol, and its
admission oracle sees only the leaf labelling and incumbent. Use
`searchNodeG_eq` (`:430`) to discharge algebra and the semantic endpoint;
a direct operational simulation would relocate the loop-coverage proof
rather than remove it.

## Facts about the code that are easy to assume wrongly

Each of these has cost real proof effort. They are stated here so they do
not have to be rediscovered.

- **The refinement code is a hash, not a determinant.** `mash` masks the
  accumulator to fifteen bits, so on a graph with more than 32768 reachable
  partition shapes, code agreement implies nothing about equal partitions,
  cell counts or discreteness.
- **`maketargetcell` depends on the labelling**, not only on positions:
  `bestcellRow` reads `ctx.g[lab[...]]` (`Refine.lean:1864`). Any bridge
  between two states' target choices needs `lab` equality or a renaming,
  not `ptn` equality alone.
- **A bare `Key` read off the state is degenerate at the root**, where
  `canonlevel = 0` gives a sentinel-only code list, and every real
  refinement code sorts below `codeSentinel`, so `keyMax` prefers the
  degenerate side. Use the `Option`-seeded `incMax` form.
- **The loops mutate their own iteration set.** `tcell` is rewritten
  mid-loop by `shortprune` and `longprune`, so the set of offsets shrinks
  as the loop runs.
- **`gcaFirst` is installed after the first-path child returns**
  (`Search.lean:305`), which is what makes "the guiding child was already
  visited" true, but it is control-flow reasoning rather than something
  read off a single state.

## Working rules

Each was learned by something going wrong.

- **Check every premise against `Search.lean` and `Refine.lean` before
  building on it.** The specification and the comments are not reliable
  guides to what the transcription does; several plausible-sounding
  properties of it are false.
- **Never commit a `sorry` or an `axiom`.** An unproven clause stays
  uncommitted. `native_decide` is banned.
- **Commit each closed piece separately**, so a sitting that stops early
  banks its work.
- **Stopping at an honest frontier with exact blocking goals is success.**
  Forcing a proof through, or weakening a statement to close it, is not.
- **Check builds by exit code**, not by grepping output.
- Techniques that repeatedly mattered: `unfold` exposes the quartet's
  `Id.run do` bodies where `rw` and `simp only` both fail, since a mutual
  definition has no equation lemmas; use `Id.run_bind` and `Id.run_pure`
  with `apply_ite` projections rather than `split`, which miscompiles
  motives on `Id.run` goals; collapse `ite` before converting `forIn` to
  `foldl`; `set` and `conv_rhs` are Mathlib-only and this library is
  Mathlib-free.

## Verification before landing

`lake build` (exit code), `scripts/check_file_line_counts.py`, and if any
executable definition moved, regenerate fixtures with
`.lake/build/bin/hexgraphiso_emit_fixtures` and check byte-identity against
`conformance-fixtures/HexGraphIso/graphiso.jsonl`. Files stay under 3000
lines, new files under 2000.
