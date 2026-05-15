## Current state

`HexGfq/CrossCheck.lean:350-351` and `HexGfq/EmitFixtures.lean:363-364`
both close the `namespace N16` `generic_irr : FpPoly.Irreducible
genericMod` with `sorry`, where `genericMod = Conway.packedGF2FpPoly
0x100B 16` is the CRC-16-CCITT polynomial `x^16 + x^12 + x^3 + x + 1`.

The sibling `N4` and `N8` namespaces in both files already discharge
their `generic_irr` via the `Berlekamp.rabinTest_imp_irreducible` +
`Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest`
pipeline against a hand-constructed
`Berlekamp.IrreducibilityCertificate`. `N32` does the same via the
`LinearIncrementalQuotient` machinery. Only `N16` is left at `sorry`.

These two `sorry`s are the only theorem-level `sorry`s in `HexGfq/`.
Discharging them gets `HexGfq` to a zero-`sorry` state, which is the
[PLAN/Phase5.md](../blob/main/PLAN/Phase5.md) exit criterion for the
library.

## Deliverables

1. In `HexGfq/CrossCheck.lean` under `namespace N16`, add the same
   irreducibility-certificate infrastructure the sibling `namespace
   N8` uses:
   - `private def genericN16Cert : Berlekamp.IrreducibilityCertificate`
     with `p := 2`, `n := 16`, an explicit `powChain` of Frobenius
     iterates `x, x^2, x^4, ..., x^{2^16} ≡ x  (mod genericMod)`, and
     a `bezout` witness array for the relevant maximal proper divisor
     of `16` (i.e. `8`, per
     `Berlekamp.maximalProperDivisors 16 = [8]`).
   - `private theorem maxProperDiv_16 :
       Berlekamp.maximalProperDivisors 16 = [8] := by decide` if not
     already present nearby.
   - `private theorem genericN16Cert_check :
       Berlekamp.checkIrreducibilityCertificateLinearIncremental
         (Conway.packedGF2FpPoly 0x100B 16)
         (by unfold Conway.packedGF2FpPoly; rfl)
         genericN16Cert = true`, proved with
     `set_option maxRecDepth 4096 in` + a `simp` invocation matching
     the `genericN8Cert_check` shape and case splits over the
     basis-size index.
   - `private theorem genericN16_irr :
       FpPoly.Irreducible (Conway.packedGF2FpPoly 0x100B 16)` via
     `Berlekamp.rabinTest_imp_irreducible` and
     `Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest`.
   - Replace the `sorry` at `HexGfq/CrossCheck.lean:350-351` with
     `exact genericN16_irr`.

2. Do the same in `HexGfq/EmitFixtures.lean` (the two files duplicate
   the per-degree namespace block), replacing the `sorry` at
   `HexGfq/EmitFixtures.lean:363-364` with the analogous local
   `genericN16_irr` reference.

3. Keep the new declarations `private` and follow the existing N8
   formatting (`set_option maxRecDepth 4096 in`, `simp [...]`,
   `constructor`/`rcases` shape, `polyP2` coefficient lists for
   `powChain`). Do not change the public API of `HexGfq/` or the
   `genericMod` definition.

4. Do not add `axiom`, `native_decide`, `TODO`, `FIXME`, or new
   theorem-level `sorry` in the affected files.

## Library placement

Paths: `HexGfq/CrossCheck.lean`, `HexGfq/EmitFixtures.lean`.

SPEC: `SPEC/Libraries/hex-gfq.md` defines `HexGfq` as the library
linking the packed `GF2n` representation with the generic
`GFqField.FiniteField` representation, with cross-check fixtures
witnessing operation agreement at fixed extension degrees. The
`generic_irr` obligation is a local proof obligation for instantiating
`GFqField.FiniteField` at `n = 16`.

Placement questions:

- Does this belong to the library named by the SPEC? Yes; the two
  files are HexGfq's own cross-check and fixture-emission modules,
  and the `N16` namespaces are the existing place for this proof.
- Does it import a bridge layer into a Mathlib-free library? No; the
  proof uses only the existing `Berlekamp` and `Conway` Mathlib-free
  certificate APIs.
- Does it change executable behavior? No; it discharges proof-level
  `sorry`s without changing definitions or `Conway.packedGF2FpPoly`.
- Does it modify immutable SPEC or roadmap files? No.

## Context

Read:

- `PLAN/Phase5.md` (zero-`sorry` exit criterion).
- `SPEC/Libraries/hex-gfq.md`.
- `HexGfq/CrossCheck.lean` around the `genericN8Cert`,
  `genericN8Cert_check`, `genericN8_irr`, `namespace N16`,
  `namespace N32` blocks. The `N32` block under
  `Berlekamp.checkIrreducibilityCertificateLinearIncrementalQuotient`
  is informative but heavier than `N16` needs; the `N8` pattern is
  the closer template.
- `HexGfq/EmitFixtures.lean` around the matching `N8`/`N16`/`N32`
  blocks. The two files share the same per-namespace pattern; expect
  to add a parallel block in each.
- `HexBerlekamp/RabinSoundness.lean` for
  `rabinTest_imp_irreducible`,
  `checkIrreducibilityCertificateLinearIncremental_rabinTest`, and
  `checkIrreducibilityCertificateLinearIncremental`.
- `HexBerlekamp/IrreducibilityCertificate.lean` (or wherever the
  certificate definitions live) for the `powChain` and `bezout`
  obligations the check decomposes into.

The `powChain` entries for `N16` are deterministic: iterated squaring
`x^{2^i} mod genericMod` for `i = 0, 1, ..., 16`, reduced via
`DensePoly` arithmetic over `FpPoly 2`. The `bezout` witness array
must contain at least the witness for the single maximal proper
divisor `8`, expressing
`gcd (x^{2^8} - x) (genericMod) = 1` as a Bezout identity.

## Verification

- `lake build HexGfq.CrossCheck`
- `lake build HexGfq.EmitFixtures`
- `lake build HexGfq`
- `grep -rn 'sorry' HexGfq/` must report zero occurrences after the
  change.
- `python3 scripts/check_dag.py`
- `git diff --check`
- No new `axiom`, `native_decide`, `TODO`, `FIXME`, or theorem-level
  `sorry` in affected files.

## Out of scope

- Refactoring the `N4` / `N8` / `N32` namespaces or extracting their
  duplicated structure across `CrossCheck.lean` and
  `EmitFixtures.lean` into a shared module.
- Touching `Conway.packedGF2FpPoly` or any of the underlying
  `Berlekamp` certificate-check primitives.
- Promoting `libraries.yml` `HexGfq.done_through`. (Phase 5 promotion
  requires zero `sorry` everywhere plus the standard Phase 5
  scripts; that is a separate slice.)
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `AGENTS.md`.
