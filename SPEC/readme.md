# Released-repo READMEs

Every released split repo carries a short `README.md` at its root, aimed
at someone who has just found the repo and wants to know what it is and
how to use it. The source of truth is `<Lib>/README.md` in this monorepo
(e.g. `HexMatrix/README.md`); the publish step copies it to the released
repo's root (see [released-repo publishing](../.claude/CLAUDE.md) and
`scripts/release/released.yml`). Never hand-edit a released repo's README;
change it here.

A README is reference documentation for the released package, distinct
from the Verso chapter in `HexManual` (which is the in-depth manual, see
[PLAN/Phase7.md](../PLAN/Phase7.md)). Keep it short: a reader should grasp
the library and copy a working snippet in under a minute.

## Required sections

Use these five level-1 headings, in this order.

1. **Intro** (no heading; the text directly under the `# <repo-name>`
   title). Two short paragraphs. The first names the library as part of
   [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
   for Lean 4, and states the project aim: fast executable code, fully
   verified, built with spec-driven development. The second says what this
   particular library provides, names its dependencies, and points at its
   Mathlib counterpart (or computational counterpart, for a `*-mathlib`
   library).

2. **`# Quickstart`**. The `lakefile.toml` `[[require]]` block for the
   released repo, followed by a single code block of at most 20 lines that
   shows off the executable surface. The code must compile; build-check it
   against the monorepo before committing. CI checks every executable Lean
   block with `lean-readme`; make each block self-contained, including its
   imports. For a `*-mathlib` library with no executable surface of its own,
   show the correspondence instead: import the bridge and state the headline
   equivalence or transfer lemma.

3. **`# Functionality`**. A brief, non-exhaustive description of the
   executable operations the library provides. Bullets, naming the real
   definitions. For a `*-mathlib` library, describe the proof-facing API
   (the equivalences and transfer lemmas) instead.

4. **`# Verification`**. A short statement of what is proven. Distinguish
   what has a complete API, what has partial coverage, and what is provided
   for executable use only. Where it helps the reader, quote the headline
   theorem for each significant result as a Lean signature (name plus
   statement, proof elided) in a `lean` code block, copied verbatim from
   the source so it stays accurate. Mark theorem blocks as `lean recall`:
   `lean-readme` then checks each displayed `theorem` statement directly against
   the declaration in the imported library, without changing the rendered
   Markdown or depending on Mathlib's `recall` command. Other quoted declaration
   kinds remain ordinary `lean` blocks. Because blocks are checked in order,
   `lean recall` blocks reuse the Quickstart block's imports and namespace
   openings rather than repeating them in the rendered theorem quotation.
   Executable examples must remain checked. Point at the sibling library where
   the rest of the theory lives.

5. **`# Contributing`**. State that development happens in the
   [`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in the
   published mirror, and that contributions are welcome as pull requests to
   the `SPEC/` directory: describe the behaviour you want and leave the
   implementation to the maintainer.

## The aggregate README

`leanprover/hex` publishes no library source, so its README has no
`<Lib>/README.md` to come from. It is generated instead: the prose lives in
`scripts/release/hex-README.md` and the library table is rendered from
`released.yml` by `scripts/release/aggregate_readme.py` during the sync.
The monorepo's own `Hex` module is test infrastructure rather than the released
aggregate, so CI checks this template with `.lean-readme/Aggregate.lean` as a
hidden prefix supplying the released APIs used by its example.

Releasing a library therefore adds it to the aggregate README with no hand
edit, provided its manifest entry carries a `component:` label naming the row
(for example `component: LLL lattice reduction`). A missing label is a
`check_released_manifest.py` failure, so the table cannot fall behind the
manifest. `*-mathlib` companions take no label; they appear in the row of the
computational library they bridge.

A library that has been announced somewhere carries an `announcements:` map
from venue (`blog`, `zulip`, `linkedin`) to https URL, and those render as an
Announcements section below the table, one line per library. That keeps the
table clean: only a couple of libraries are ever announced, so a fourth column
would be empty for almost every row.

The five required headings above do not apply to the aggregate: it documents
the collection, not a library.

## Style

Follow the project's writing conventions. In particular: no
meta-commentary or history; no run-on appositive clauses (write two
sentences, not "..., Mathlib-free"); no filler words like "core". Prefer
plain, human phrasing. Use full clickable URLs for cross-repo links, with
the repo name as the link text.
