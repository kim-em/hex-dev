# BZ Versus Isabelle Investigation

This comparison pairs the verified original-coordinate M1 production path at
`2ee33dc56118b9bd4da5d1800c3807a38158bdb2` (2026-07-30) with the
already-current Isabelle2025-2 / AFP 2026-05-29 exports (2026-07-28). The
unchanged no-decline classical row comes from `b0150d2b`; the unchanged lattice
row comes from `0b95505b7c926911a9f487bac56676a8c7da48f6`. All were measured
on `chungus2`, pinned to CPU 0, against the same 392-row corpus and warm
persistent-service protocol. Isabelle, no-decline classical, and lattice were
not rerun because the implementation change is confined to Hex's bounded
production classical route.

The Hex artifacts record clean worktrees. Measured protocol overhead was
17.466 µs for Hex public, 18.848 µs for Hex lattice, 18.297 µs for Hex
classical, 17.777 µs for Isabelle BZ, and 17.136 µs for Isabelle LLL.

## Corpus frontiers

| System | Solved / 392 | Solved-row median | p90 | Slowest solved |
|---|---:|---:|---:|---:|
| Hex public factor | 373 | 400.905 µs | 4.079 ms | 8.994 s |
| Hex lattice | 369 | 1.812 ms | 87.886 ms | 9.590 s |
| Hex classical, no decline | 372 | 386.358 µs | 5.556 ms | 3.717 s |
| Verified Isabelle BZ | 371 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 6.109 ms | 1.219 s | 9.528 s |

Hex public solves `cyclo_phi257`, `cyclo_phi331`, `sd5_x_phi45`, and `sd6`,
where verified BZ times out. Verified BZ solves `cyclo_phi121` and
`cyclo_phi1031`, where Hex public times out. Thus Hex has two more successes,
but the frontiers are not nested.

## Common-row ratios

Ratios divide the per-row median Hex service wall clock by Isabelle's. A row
is eligible only when each median is at least ten times its service's measured
protocol overhead.

| Pair | Common solved | Eligible | Median ratio | p10–p90 | Hex faster | Isabelle faster |
|---|---:|---:|---:|---:|---:|---:|
| Hex public / verified BZ | 369 | 234 | 0.865x | 0.466x–2.062x | 135 | 99 |
| Hex classical / verified BZ | 369 | 229 | 0.901x | 0.466x–2.490x | 127 | 102 |
| Hex lattice / verified LLL | 313 | 230 | 0.137x | 0.004x–2.437x | 182 | 48 |

The former 3.95× public/BZ median gap is now a 13.5% aggregate Hex lead.
This is clear aggregate superiority but not uniform superiority: the family
medians are now 1.20× on Chebyshev and 1.26× on Legendre, down from 1.62× and
1.44× before M1. Hex leads on Conway (0.74×), cyclotomic products (0.57×),
Laguerre (0.79×), signed-digit products (0.86×), Swinnerton-Dyer (0.73×), and
Wilkinson (0.61×). Cyclotomic is 1.18× and random products slightly favour Hex
at 0.96×. FLINT, PARI/GP, and NTL remain substantially faster overall.

The broad per-family and per-row spread remains the central qualification.
Original-coordinate M1 makes U18, U20, and U24 faster than Isabelle; P28 reaches
parity, while P30 and P38 narrow to 1.06× and 1.29×. Other individual rows
still exceed 4×, so the aggregate lead does not imply per-instance dominance.
See `hexbz-m1-chebyshev-legendre.md` for the phase attribution and measured
go/no-go outcomes.

The lattice entry point remains substantially faster than verified Isabelle
LLL on its median eligible row, but it solves fewer rows and has a heavy tail.
The broad percentile bands and non-identical timeout frontiers make any single
aggregate ratio inadequate as a release gate.

Every factor-degree check against a committed corpus oracle passed. See
`hexbz-factor-sweep.md` for all eight systems, plots, and artifact provenance.
The current Hex inputs are:

- `hexbz-factor-sweep-hex-2ee33dc5-m1-chungus2.json`
  (current public; SHA-256
  `a604aaaf492dacf726a0ae6315744f14a46dd21d124033b846a73e00f5511e89`)
- `hexbz-factor-sweep-hex-b0150d2b-recombine-cache-chungus2.json`
  (preceding public and unchanged no-decline classical; SHA-256
  `7222c12c206d9fdb3489d98595c72f9eb254f31108e5136722242784eb086be3`)
- `hexbz-factor-sweep-hex-0b95505b-gcd-hensel-final-chungus2.json`
  (unchanged lattice; SHA-256
  `9f9f63ac9f35b3af6d35e530b085a1a1e47e7d03d958179d7597d7850e59c583`)

The path is relative to `reports/bench-results/`.
