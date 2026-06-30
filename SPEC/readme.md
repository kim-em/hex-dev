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
   against the monorepo before committing (a throwaway file run through
   `lake env lean`, or as a temporary module). For a `*-mathlib` library
   with no executable surface of its own, show the correspondence instead:
   import the bridge and state the headline equivalence or transfer lemma.

3. **`# Functionality`**. A brief, non-exhaustive description of the
   executable operations the library provides. Bullets, naming the real
   definitions. For a `*-mathlib` library, describe the proof-facing API
   (the equivalences and transfer lemmas) instead.

4. **`# Verification`**. A short statement of what is proven. Distinguish
   what has a complete API, what has partial coverage, and what is provided
   for executable use only. Where it helps the reader, quote the headline
   theorem for each significant result as a Lean signature (name plus
   statement, proof elided) in a `lean` code block, copied verbatim from
   the source so it stays accurate. Point at the sibling library where the
   rest of the theory lives.

5. **`# Contributing`**. State that development happens in the
   [`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in the
   published mirror, and that contributions are welcome as pull requests to
   the `SPEC/` directory: describe the behaviour you want and leave the
   implementation to the maintainer.

## Style

Follow the project's writing conventions. In particular: no
meta-commentary or history; no run-on appositive clauses (write two
sentences, not "..., Mathlib-free"); no filler words like "core". Prefer
plain, human phrasing. Use full clickable URLs for cross-repo links, with
the repo name as the link text.
