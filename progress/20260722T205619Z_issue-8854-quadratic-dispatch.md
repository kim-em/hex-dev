# issue #8854: guarded word-sized quadratic Hensel dispatch complete

## Accomplished

- Added `WordMod.sub_self` to support monic division uniqueness over the word ring.
- Added the guarded `quadraticHenselStepWord?` kernel, preserved the previous implementation as
  `quadraticHenselStepBignum`, and routed `quadraticHenselStep` through the word path with bignum fallback.
- Proved transport for the mod-square operations and both monic divisions, then proved
  `quadraticHenselStepWord?_eq` and the unconditional `quadraticHenselStep_eq_bignum`.
- Rerouted the four specification proofs through `quadraticHenselStep_eq_bignum`.
- Built `HexHensel.Quadratic`, `HexBerlekampZassenhausMathlib`, `HexConformance`, and `hexbz_bench`.
- Audited the touched files for `sorry`, `admit`, and explicit `axiom` declarations; none remain.
  `#print axioms Hex.ZPoly.quadraticHenselStep_eq_bignum` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Ran the requested cold SD4 benchmark. Its result hash/checksum is unchanged at
  `0x687e925fbe11193b` (`7529616566918388027`).

## Current frontier

The assembly is complete and all requested build targets are green. The benchmark produced one successful
35.394 ms cold row, but the singleton parametric harness returned its standard inconclusive/no-verdict-row
exit because a one-point schedule cannot yield a complexity verdict; the result itself was successful.

## Next step

Review and commit the two source changes together with this progress note, then continue the normal PR flow.

## Blockers

None.
