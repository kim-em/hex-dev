# hex-primality: the Pocklington certificate and checker (milestone 3a)

## Accomplished

- `HexPrimality/Cert.lean`: `PrimeCert` as one inductive (`small`,
  `pock`, and `pock3` carrying the SPEC-amended sqrt witness `w`;
  the cube-root arithmetic is a documented `false` stub until
  milestone 4). `checkPrime`/`checkChildren` are a mutual
  **structurally recursive** pair (well-founded recursion would kill
  kernel reduction), with all workers `@[expose]`: `boundedPowMul` /
  `certProduct` (abort past `n - 1`), `subjectsOk`, `checkWitness`
  written against the kernel-facing `HexArith.powModNat`.
- Soundness: accumulator lemmas, `certProd_dvd` (the fused
  coprime-prime-powers combination over the checker's own fold), the
  gcd-to-noncongruence transport `mod_ne_one_of_gcd`, the
  `pocklington` core theorem (per-entry order extraction, `F ∣ p - 1`
  for every prime divisor, square contradiction), and
  `prime_of_checkPrime` by strong induction on the subject value
  (children have subject dividing `n - 1 < n`), sidestepping the
  nested-inductive induction principle. `prime_of_checkPrimeAt` is
  the single-Bool-slot wrapper for the tactic reifier;
  `CheckedPrimeCert` ties an accepted certificate to its requester.
- `#guard` block: accepted one-factor, two-factor, and two-level
  certificates, and one rejected certificate of each kind (bound too
  small, composite factor, failed gcd witness, non-dividing factor,
  stubbed pock3).

## Current frontier

The checker soundness half of milestone 3 is done. The search half
(`rhoFactor?`, `partialFactor`, `primeCert?`, `isPrime?`) consumes
`Hex.Rand` and stacks on this.

## Next step

Search.lean part 1: Brent rho with dynamic validation and
`partialFactor` with its product invariant.

## Blockers

Stacked on the Miller-Rabin PR; the search half additionally needs the
HexBasic/Rand PR.
