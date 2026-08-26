# Module-system migration of non-BZ libraries (checkpoint)

## Accomplished

Migrating non-Berlekamp-Zassenhaus libraries to the Lean 4 module system in a
fresh /tmp clone on branch `module-migration-non-bz`. Excluded per the plan:
`HexBerlekampZassenhaus`, `HexBerlekampZassenhausMathlib` (only libs downstream
of BZ), and `HexManual` (by choice; verified it does NOT import BZ).

**Verified green** (`lake build` and `lake build HexConformance` both exit 0,
real exit code checked in-log):

- `HexArith` — `CrossCheck` + umbrella.
- `HexPoly` — umbrella.
- `HexPolyFp` — umbrella.
- `HexModArith` — `Smoke` + umbrella (Smoke needed `public meta import`, below).
- `HexModArithMathlib` — `Basic` (`@[expose]` on `toZMod`/`ofZMod`/`equiv`) +
  umbrella.
- `HexGFqRing` — umbrella.

## The migration recipe (learned the hard way — read before continuing)

Per file: `module` after the copyright header, blank line, then imports as
`public import`, then `public section`. Umbrellas migrate last (after all their
submodules are modules). A `module` file CANNOT import a legacy file, so strict
bottom-up is mandatory.

Two non-obvious requirements dominate the work:

1. **`#eval` / `#guard_msgs` / `#guard` of imported executable defs need
   `public meta import` of the providing module** (in addition to the regular
   `public import` if also used in normal code). These commands run code at
   elaboration time. Exception: defs marked `@[expose]` are meta-accessible, so
   a file calling only exposed upstream defs (e.g. `HexArith/CrossCheck`, which
   uses the exposed Barrett/Montgomery API) needs no meta import. Template:
   `HexPolyFp/SquareFree.lean` (`public meta import` + `public import`).

2. **Exported (in `public section`) theorems proved by `rfl` / `unfold` /
   `change` / `decide` require EVERY definition they unfold to be `@[expose]`** —
   including same-module defs and the backing defs of wrapping instances. The
   compiler error is "Not a definitional equality ... This theorem is exported
   ... all definitions that need to be unfolded ... must be exposed." This is
   the main cost in the delegating-wrapper libraries (GFqField, Hensel, GFq).
   Template: `HexGFqRing/Operations.lean` exposes its operation defs (`zero`,
   `one`, `add`, `mul`, ...) but not the `instance`s.

Gotchas found:
- `@[expose]` is **rejected on a `structure`** ("can only be added when declaring
  a `def`"). The `FiniteField` projection-`rfl` lemmas in `HexGFqField` still need
  a solution for cross-module reduction of the structure projection — UNSOLVED.
- Exposing a `def` whose body calls a `private` def fails with "unknown
  identifier"; the referenced private def must be made public + `@[expose]`
  (e.g. `HexGFqField.invPoly`).
- A `private theorem` referenced later in the same file can report "unknown
  identifier" under `module` + `public section` (seen at
  `HexGFqField/Operations.lean` `pow_zero_eq_one`/`inv_inv_def`) — scoping
  interaction to investigate.

## Process note

`lake build` here is wrapped so the shell ends in `tail`; the background-task
"exit code 0" reflects `tail`, NOT `lake`. ALWAYS read the real status from a
`LAKE_EXIT=$?` line written to the log, in the foreground. (An earlier commit
bundled unverified-broken Tier-1 files because of this; it was reset.)

## Current frontier / next step

Remaining in scope (each needs the `@[expose]`-on-exported-rfl pass above):

- `HexPolyMathlib` (`Basic` line ~524 rfl), `HexPolyZ` (`Basic`: `unfold IsUnit`,
  `change`, and a private `normalizePrimitiveSign` reference), `HexGF2`
  (`Basic` line ~646 rfl + likely more across its 11 files) — all reverted to
  legacy in this checkpoint; redo with the exposure pass.
- `HexGFqField/Operations` got to 5 residual errors (inv/invPoly expose,
  `change` in `inv_zero`, the two private-theorem "unknown identifier"s);
  reverted to legacy for now.
- Then `HexGF2Mathlib`, `HexHensel`(+Mathlib), `HexPolyZMathlib`,
  `HexBerlekamp`(+Mathlib — Risk 1: `ZMod64.Bounds` Prop-instance synthesis),
  `HexConway`, `HexGFq`(+Mathlib), `Hex/` test kit (Risk 3 public API for
  `Conformance.Emit`/`BenchOracle.Flint`).

Build per file/library; read the real `LAKE_EXIT`; rebuild `HexConformance` after
umbrellas (legacy conformance drivers must stay green — they do at this
checkpoint).

## Blockers

`HexGF2` Risk-2 codegen blocker did NOT recur (mechanical `public section`
without `@[expose]` builds the executable kernels fine); its remaining errors are
the ordinary exported-rfl exposure pass. Risk 1 (HexBerlekamp `ZMod64.Bounds`)
not yet reached.
