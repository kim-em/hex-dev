# Released-repo READMEs for the finite-field Mathlib layers

## Accomplished

Authored two `<Lib>/README.md` files against `SPEC/readme.md`, on the same
branch as the four computational READMEs:

- `HexGF2Mathlib/README.md` (`hex-gf2-mathlib`)
- `HexGFqMathlib/README.md` (`hex-gfq-mathlib`)

Both have the five required sections, a `[[require]]` block naming the released
repository, a Quickstart that states the headline correspondence rather than an
executable surface, and Verification signatures copied verbatim from the
sources: `GF2Poly.equiv`, `GF2Poly.equivPolynomial`, the two `GF2n`/`GF2nPoly`
field equivalences and their `fintype_card` theorems; `FiniteField.field`,
`GFq.fintype_card_eq_pow`, `GFq.equivGaloisField`, `GF2q.equivGFq`,
`GF2q.equivGaloisField` and `conwayEmbed`.

Both Quickstart snippets were elaborated against a full build with
`lake env lean` and reported no errors.
`python3 scripts/release/check_released_manifest.py` still passes; neither
repository has a `released.yml` entry yet, so the manifest does not track these
files.

Two SPEC claims were carried through with their caveats intact rather than
flattened into results:

- `hex-gfq-mathlib`: `Conway.normX`'s reading as the field norm
  `α ^ ((p^n - 1) / (p^m - 1))` is stated as design rationale, not a theorem,
  and the README says which bridges hex-conway is still missing.
- `hex-gfq-mathlib`: the primitivity transport is described as component
  lemmas only, with the absence of the `Primitive.check`-to-`orderOf` glue and
  of the per-entry `orderOf α = p ^ n - 1` conclusion stated outright.

One naming correction: the SPEC attributes
`eval_conwayPoly_subfieldGen_eq_zero` to this library, but that theorem lives
in `HexConway/Compatibility.lean`. The README names this library's own
`substHom_conwayPoly_eq_zero` instead.

## Current frontier

Six READMEs are now committed on `finite-field-batch-readmes`: the four
computational ones and these two correspondence layers. Nothing is pushed.

## Next step

Add `released.yml` entries when these libraries are released. `*-mathlib`
companions take no `component:` label; they appear in the row of the
computational library they bridge.

## Blockers

None.
