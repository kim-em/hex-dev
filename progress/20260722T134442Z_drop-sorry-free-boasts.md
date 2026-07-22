# Drop "sorry-free"/"axiom-free" self-commentary from shipped docstrings

## Accomplished

- Removed docstring boasts asserting a deliverable is `sorry`-free (bare
  minimum for release; reads as unprofessional to comment on):
  - `HexRealRootsMathlib.lean`: dropped "Every theorem in the library is now
    proven; there are no `sorry`s."
  - `HexRealRootsMathlib/TwoCircle.lean`: dropped "It is the last theorem of
    `HexRealRootsMathlib`, and with it the companion is fully `sorry`-free."
  - `HexRealRootsMathlib/IsolateRootsTests.lean`: reworded to keep the real
    content (public-API-only, no `import all`) and drop "and no `sorry`".
  - `HexBareissMathlib.lean`: reworded "no sorry-bound hypothesis" to
    "holds unconditionally (with no side hypothesis)", preserving the meaning
    (the theorem is unconditional).
- Comment-only changes; diff confined to doc-comment prose.
- Left legitimate technical/requirement uses of the terms in PLAN/ and SPEC/
  (review checklists, phase entry conditions, proof-discipline prose) untouched;
  left progress/ and reports/ journals as history.

## Current frontier

Local `lake build` cannot link the `hexmodarithffi` shared library in this
checkout (broken elan/nix `ld-wrapper.sh` path), so oleans could not be produced
locally. CI links on its own runner; relying on it as the authoritative check.

## Next step

Merge once CI is green.

## Blockers

None (local FFI linker breakage is environmental, unrelated to this change).
