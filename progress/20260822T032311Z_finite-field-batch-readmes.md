# Released-repo READMEs for the computational finite-field batch

## Accomplished

Authored four `<Lib>/README.md` files against `SPEC/readme.md`:

- `HexGF2/README.md` (`hex-gf2`)
- `HexConway/README.md` (`hex-conway`)
- `HexGFqField/README.md` (`hex-gfq-field`)
- `HexGFq/README.md` (`hex-gfq`)

Each has the five required sections, a `[[require]]` block naming its released
repository, a Quickstart snippet under 20 lines, headline theorem signatures
quoted verbatim in the Verification section, and the standard Contributing
paragraph.

Every Quickstart snippet was elaborated against a full build with
`lake env lean` and reported no errors.
`python3 scripts/release/check_released_manifest.py` still passes; the four
repositories have no `released.yml` entries yet, so the manifest does not track
these files.

Three SPEC claims were softened to match the implementation:

- `hex-gf2`: `GF2Poly.mul` is schoolbook only, so the README does not mention
  Karatsuba; the packed-vs-generic speedup figures are not quoted, since those
  benches live at the monorepo bench root rather than in the library tree.
- `hex-gf2`: the Euclidean-domain story is described through the proved
  specification lemmas, because there is no bundled instance.
- `hex-conway`: Tier 3 on-demand search is stated as specified but not
  implemented, with no API promised.

## Current frontier

The four files are committed on `finite-field-batch-readmes`. A second agent is
adding two more READMEs on the same branch.

## Next step

Add the corresponding `released.yml` entries, with `component:` labels, when
these libraries are released. That is what puts the READMEs under
`check_released_manifest.py` and into the aggregate README table.

## Blockers

None.
