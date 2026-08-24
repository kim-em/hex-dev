# Finite-field batch: publish manifest entries

## Accomplished

- Authored the six released-repo READMEs (HexGF2, HexConway, HexGFqField,
  HexGFq, HexGF2Mathlib, HexGFqMathlib) per SPEC/readme.md, with
  compile-checked Quickstart snippets and honest scoping of SPEC
  overclaims (no Karatsuba, no bundled Euclidean-domain instance, Conway
  Tier 3 absent, normX field-norm reading unproved, primitivity glue
  absent).
- Added the six release-manifest entries after hex-berlekamp in
  topological order (hex-conway, hex-gfq-field, hex-gf2, hex-gf2-mathlib,
  hex-gfq, hex-gfq-mathlib) with mechanically verified pin closures;
  hex-gf2 is `lakefile: lean` with `precompile_modules: true` and ships
  the NTL comparator driver sources; the aggregate pins gain all six.
- Moved the HexGF2, HexGFqField, HexConway, and HexGFq chapters from the
  draft include level to the released level in HexManual.lean.
- check_released_manifest.py: 42 split repositories + 1 aggregate, valid.
  check_manual_split.py: 23 released chapters, 4 draft, consistent.
  check_dag.py: clean.

## Current frontier

- The seven bootstrap skeletons are pushed on the released repos' mains;
  the two baselined existing mirrors (aggregate, hex-berlekamp-mathlib)
  still need their coordinated require edits before a sync.

## Next step

- Merge this batch, then the staged publish per the release plan (token
  verification, local staging build, pinned-SHA dry run, real run).

## Blockers

- Publishing-token widening for the seven new repositories awaits
  org-owner approval.
