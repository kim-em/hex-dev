# hex-graph-iso: the verified nauty-semantic canonical form is complete

The SPEC's two independent requirements are both discharged on the
`nauty` branch, and the public surface has switched.

## What is proved (Lean, Mathlib-free, no sorry/axiom/native_decide)

The verification stack, bottom to top:

- `refine_map` / `specNode_map` (Equivariance, CanonSpec): the whole
  refinement and the unpruned spec tree are equivariant under vertex
  renamings.
- `refine_perm` / `specNode_perm` (CellPerm, CanonSpec): both depend
  on an ordered partition only through each cell's vertex multiset.
  The spec's target-cell rule is the count-multiset join test, which
  sidesteps `bestcell`'s representative dependence.
- `canonSpecKey_eq_of_isomorphic` (SpecIso): isomorphic coloured
  graphs have equal spec keys, via a renaming extracted from the
  isomorphism plus cell-equivalence of the two initial labellings.
- `refine_refInv` (Achieved): refine preserves every input cell's
  contents and only adds partition boundaries; a boundary-monotone
  coarsening theorem tiles coarse spans with fine cells.
- `specNode_achieved` (Achieved): the spec key's rows come from a
  reachable leaf whose labelling permutes every ancestor cell;
  boundary counting shows the search always reaches its leaves.
- `specCanon` (SpecCanon): the total canonical form read off the key
  (rows) and the sorted colour classes; `specCanon_iso`,
  `specCanon_invariant`, `iso_iff_specCanon_eq`.
- Certificates (Cert, CanonForm): `checkNode`/`checkKey` replay a
  `CertNode` tree with `checkKey_sound`; code prunes via
  first-difference dominance, automorphism prunes via
  `checkAutom`/`checkCellsPerm` and `specNode_autom`. `checkCanon`
  validates the achieving labelling (rows, colour sortedness,
  permutation) and packages the `CanonResult`; checked forms are
  key-determined (`checkCanon_form_eq_formOfKey`), giving
  `isomorphic_of_certs` and `not_isomorphic_of_certs`.
- Completeness (Complete): `certifyNode_complete`/`checkKey_complete`
  (the checker accepts the honest certificate for the true key) and
  `bruteCanon?_isSome` (the achieved leaf is among all orderings), so
  `canonicalizeSpec` is total with the full theorem surface.
- Public switch (Ops): `canonicalize`/`canon`/`label`/`findIso`/
  `isIso`, the bounded ops, and the SPEC certificate API
  (`CanonCert`, `certify?`, `checkCanon`, `checkCanon_sound`,
  `DiffCert`, `checkDiff`) are all backed by `canonicalizeSpec`.

## nauty compatibility evidence

- The transcription (`Nauty.run`) stays pinned by the committed
  fixture and the 32,788-case differential campaign against real
  nauty 2.9.3 (both re-verified after the functional
  `rowsOf`/`initialPartition` refactor).
- The fixture and campaign emitters now serialize the *public*
  `canonicalize` answer (label and canonical bits), built through the
  public checked constructors, so the whole corpus pins the public
  surface — form and label — against real nauty, not only the
  transcription. This caught and fixed a real divergence: the
  certificate pipeline's label replay picked a different achieving
  leaf than nauty on 1,346 of 6,028 fixture cases; the label source is
  now the transcribed search's `canonlab` validated by `checkCanon`.
- Conformance guards additionally pin
  `rowsOf (canon G) == (runColored G).canong` on committed cases.
- New bench comparator: `runHexCanon{8,12,16}` versus
  `runNautyCanon{8,12,16}` through an in-process FFI binding against
  the vendored nauty 2.9.3 source (`vendor/nauty-2.9.3`);
  `runCanonAgree16` fails `verify` on any divergence.

## Notes for future work

- The producer prunes by code and by automorphisms (Nauty/CertAutom):
  harvested-generator skipping validated by the unchanged checker.
  Producer prunes are an optimization, not a correctness need.
- The tactic's negative path remains the verified pairwise replay
  (SPEC text updated to record why); the certificate route is on the
  API for compiled callers.
- The public label comes from the transcribed search's `canonlab`
  (nauty's exact tie-breaking) validated by the trusted `checkCanon`;
  the exhaustive fallback plus runtime validation carries totality.
