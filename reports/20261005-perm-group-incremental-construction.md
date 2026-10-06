# Incremental Schreier-Sims construction in HexPermGroup

`Group.ofGenerators` used to rebuild the whole suffix chain from scratch each
time a Schreier generator failed to sift, and each rebuild rescanned every
Schreier generator below it. The number of rebuilds grew twenty- to thirtyfold
with each generator added for the Rubik's cube group. The construction now extends the current
suffix in place (see "Deterministic construction" in
`HexPermGroup/SPEC/hex-perm-group.md`).

Measured on 2026-10-05 with a compiled executable, one process at a time,
timing `Group.ofGenerators` and the order of its chain. The input is the first
`k` of the face turns U, R, F, D, L, B of the Rubik's cube, as permutations of
the 54 facelets.

| face turns | order | rebuild (ms) | rebuilds | incremental (ms) | extensions |
|---|---|---|---|---|---|
| 2 | 73483200 | 45 | 393 | 35 | 240 |
| 3 | 170659735142400 | 1101 | 11849 | 233 | 816 |
| 4 | 1802166803103744000 | 17200 | 254136 | 503 | 1748 |
| 5 | 43252003274489856000 | 226720 | not recorded | 735 | 2382 |
| 6 | 43252003274489856000 | 64507 | not recorded | 633 | 2277 |

Before the change, a profile of the six-turn case attributed the time to
permutation composition and inversion inside sifts and Schreier generator
evaluation, which the rebuilds repeat.

The certificate fixtures emitted by `hexpermgroup_emit_fixtures` are
byte-identical before and after the change.
