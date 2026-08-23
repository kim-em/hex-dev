# hex-primality: batched replay and the verification swap (plan complete)

## Accomplished

- `Sieve.lean` gains the read-back layer: `bitsToList` with
  `mem_bitsToList` and `bitsToList_pairwise_lt`, plus `prime_mod_six`;
  the index round-trip lemmas are now public.
- `Table.lean` verification swapped onto the sieve: the committed
  literal is now tied by `primeTable_eq_bits` (one cheap kernel
  comparison through the kernel-reducible Array equality) to the final
  state of one sieve run replayed in four kernel-checked chunks and
  chained by `sieveGoRange_add`; both membership directions flow
  through `sieve_testBit_iff`. The `coverOk` chunks and the
  `isPrimeTrial` sweep are deleted. **Module elaboration drops from
  ~82 s to 2.2 s** — the scaling claim the SPEC makes for the batched
  sieve, measured. Public statements unchanged; sortedness stays on
  the cheap structural check.
- `SieveElab.lean`: the `#rebuild_primeTable bound sqrtBound batches`
  command runs the compiled sieve, independently cross-checks every
  represented bit against `isPrimeTrial`, and prints the table literal
  plus the whole verification block. Verified to round-trip: its
  emission at `10000 100 4` reproduces the committed table and all
  four states byte-for-byte.

## Current frontier

Every milestone of HexPrimality/SPEC/hex-primality.md is implemented:
the 18-PR plan is complete. Raising `primeTableBound` past `10^4` is
now one bench measurement plus one `#rebuild_primeTable` run.

## Next step

Review and merge the stack bottom-up (#9383 first); CI's PARI oracle
run is the remaining external validation.

## Blockers

None.
