# Execute a Review Work Item

You are a **review** session. Your job is to claim and execute a pre-planned review
work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to review sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label review` to find work for this session type.

## Review Focus Areas

Each session should pick **one or two** focus areas and go deep, rather than
superficially covering everything. The issue body will specify what to focus on.
Rotate through these areas across sessions:

**Refactoring and code improvement** (top priority):
- Can code be simplified? Are there redundant steps?
- Would extracting a function/lemma improve readability or enable reuse?
- Are there generally useful constructions worth upstreaming?

**Slop detection**:
- Dead code, duplicated logic, verbose comments, unused imports
- Other signs of AI-generated bloat
- Dead-code caveat: a plain "grep for the name" check produces dangerous
  false positives. `instance`s are consumed by typeclass resolution and
  `@[simp]`/`@[grind]`/`@[grind =]` lemmas by tactic automation — neither
  is referenced by name, so both look unused but are live (deleting them
  breaks proofs silently or at build time). Treat instances and
  `simp`/`grind`-tagged decls as roots. The reliable check: reachability
  from roots (public/exported decls + instances + tagged lemmas + anything
  referenced from another file) following name references inside decl
  bodies; a `private` decl unreachable from roots is genuinely dead.
  Confirm every removal by rebuilding — the compiler is ground truth.
- Dead-code scan gotcha: when counting references, **count namespace-
  qualified uses** (`Ns.foo` is a use of `foo`) — a regex that excludes a
  leading `.` will false-flag used decls as dead. **But for `private`
  decls the opposite holds**: a private decl is file-local and never
  referenced qualified, so counting `Ns.foo` matches collide with
  same-named decls in *other* namespaces and make dead privates look
  live (e.g. a private `derivative_pow_succ` collides with Mathlib's
  `Polynomial.derivative_pow_succ`). For private decls use a word-boundary
  match that does **not** count a leading `.`, and treat `_core`/`_done`/
  `_tail`-style siblings as distinct names (a substring grep conflates
  them). The compiler is ground truth either way — rebuild after every
  removal. For a "real dead-code cluster" (many decls / >~200 lines /
  cascading orphans), file a punch-list feature issue and leave
  `done_through` unbumped rather than bashing the deletion through a
  review session; removal needs an iterative delete→rescan→rebuild
  fixpoint.

**Idioms and best practices**:
- Are newer APIs or language features being used where appropriate?
- Opportunities to improve type safety, remove unsafe operations

**Toolchain**:
- Check if a newer stable toolchain release is available; upgrade if tests pass

**File size and organization**:
- Files over 500 lines are candidates for splitting; never let a file grow past 1000

**Security**:
- Check for new issues in recent code, verify past fixes

## Phase 6 exit-criteria audits

For a "Phase 6 exit-criteria audit" issue, the *linter clean* criterion
has a trap: `lake build` caches build output and **replays nothing on a
cache hit**, so a library that is already built shows zero warnings even
if its source emits linter warnings on a real compile. Trusting that is a
false "clean". Force a fresh recompile of just the target library's core
modules — delete their oleans, then rebuild:

```bash
find .lake/build -path '*/HexFoo/*' \( -name 'Bar.*' -o -name 'Baz.*' \) -delete
lake build HexFoo 2>&1 | grep -iE 'warning|error|sorry|linter|unused' || echo CLEAN
```

For `mathlib: false` libraries the "Mathlib linter" is just Lean's
built-in linters (Mathlib's `#lint` cannot run without importing
Mathlib); a clean fresh recompile satisfies the criterion. Always
rebuild the direct downstream consumer too (`HexFooMathlib`) after any
dead-code removal — the cross-repo grep can miss nothing, but the
compiler is the only proof the removals were safe.

## Updating Skills

When you discover a recurring pattern or encounter a situation not covered by
existing skills, update the relevant skill file or create a new one.

## Reflect

Run `/reflect` before finishing.
