# verified Isabelle LLL patches

`scripts/oracle/setup_lll_isabelle.sh` applies every `*.patch` in this
directory after unpacking Zenodo record 2636367 and before building
`experiments/svp_verified`.

No patch is currently required for the bundled Haskell extraction with current
GHC. Add narrowly-scoped patches here if future toolchain drift makes the
archive stop building.
