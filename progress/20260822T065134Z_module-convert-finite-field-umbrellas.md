# Module-system conversion of the four remaining non-module released libraries

## Accomplished

`leanprover/hex`'s aggregate umbrella is `module` + `public import` over every
released library, and a module may not import a non-module module. Four
published libraries had never adopted the module system, so the aggregate could
not build. All four now do.

**HexConway** (umbrella + 7 files). Blanket `@[expose]` on every `def` in
`Table`, `Api`, `Compatibility`, and `Primitivity`: the committed table is data
whose monic/degree/table-hit/compatibility/primitivity lemmas are all `rfl` or
`decide`, so the bodies have to reach importers. This matches `HexGF2`
(83 exposed of 86 defs) and `HexGFqField` (20 of 22). `Rebuild` and
`EntrySource` are generator-only, so their declarations became `meta`, with
`public meta import` for the modules the meta code reaches
(`HexBerlekamp.Irreducibility`, `HexBerlekamp.CertificateSyntax`,
`HexPolyFp.Field`, `HexConway.Table`, `HexConway.Rebuild`). Both generators
emit `@[expose]` above the `def`s they render, so a regeneration stays
module-correct; `conformance/HexConway/Conformance.lean`'s `expectedRender`
fixture tracks that.

**HexGFq** (umbrella + `Basic`). Blanket `@[expose]` again. The six
`packedGF2Entry_2_*_irreducible` theorems had to drop `private`: they are
`packed_irreducible` fields of public `PackedGF2Entry` instances, and a public
declaration's body may not name a module-private one. `packedGF2Entry_2_1_irreducible`
was already public, so this only makes the family consistent.

**HexGF2Mathlib** (umbrella + 3 files). No blanket exposure; the Mathlib
bridges follow `HexPolyFpMathlib`, which exposes nothing. Two load-bearing
changes:

* `ofFpPoly` tabulated its words with core `Array.ofFn`, whose `ofFn.go`
  auxiliary is not exposed, so `ofFpPoly 0 = 0` stopped being `rfl` under the
  module system. Switched to `Hex.Array.ofFn'` from `HexBasic.OfFn`, which
  exists for exactly this. `Array.ofFn'_eq_ofFn` is `@[simp]`, so the
  surrounding coefficient proofs, which are stated about `Array.ofFn`, still
  go through unchanged. With that one line fixed, `ofFpPoly`, `packWord` and
  `coeffOfFp` need no exposure and `packWord`/`coeffOfFp` stay `private`.
* `prime_two` dropped `private`: it appears in the *type* of the public
  `GenericFiniteField` abbreviation.

`GF2n.modulusFpPoly` gained `@[expose]` for a `show` in
`HexGFqMathlib/GF2q.lean`.

**HexGFqMathlib** (umbrella + 4 files). One exposure: `ofPolyHom`, whose
`ofPolyHom_apply` is `rfl`.

## The guard hex-dev lacked

Nothing in this monorepo imported a released umbrella from module code — the
conformance and bench drivers are non-module and may import anything — so a
library that skipped the module system built green here and broke only the
aggregate. `HexAggregateCheck.lean` is a `module` whose entire content is the
same `public import`s `leanprover/hex` carries, in the same order. It is a
`@[default_target] lean_lib` and is listed in `ci.yml`'s `HEX_LIB_TARGETS`, so
a bare local `lake build` and the single CI `build` job both cover it.
`scripts/release/check_released_manifest.py` compares its import list against
the `leanprover/hex` entry's `pins:` in `released.yml` and fails on drift, so
publishing a new library updates the mirror rather than silently skipping it.
`scripts/libgraph.py`'s `KNOWN_EXCEPTIONS` gained the name, beside `Hex` and
`HexManual`, since it is a repo-root `lean_lib` with no `libraries.yml` entry.
Documented in `SPEC/CI.md` §"Released-aggregate mirror".

Verified both directions: reverting `HexGFqMathlib.lean` to its non-module form
reproduces `HexAggregateCheck.lean:7:0: cannot import non-`module`
HexGFqMathlib from `module``, and the converted tree builds it clean.

## Current frontier

Green: the whole `HEX_LIB_TARGETS` set plus `HexAggregateCheck`,
`HexConformance` and the emit-fixture executables, the four finite-field bench
executables, `HexManual`, and a bare `lake build`. All of `check_dag`,
`check_released_manifest`, `check_manual_split`, `check_trust_surface`,
`check_phase4`, `check_phase7`, `check_copyright_headers`,
`check_file_line_counts`, `check_benches_mathlib_free`, `conformance_targets
--check`, and the three `unittest` suites pass.

## Next step

Re-run the publish-out sync so the released repositories pick the conversion
up; the aggregate's build is the thing that was failing.

## Blockers

None.
