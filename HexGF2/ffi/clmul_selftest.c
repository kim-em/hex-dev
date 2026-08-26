/* Cross-check of the carry-less multiply implementations in clmul.c.
 *
 * `HexGF2/SPEC/hex-gf2.md` requires that tests exercise each compiled wrapper
 * path, not merely whichever one the host happens to select. A build picks its
 * path with preprocessor guards, so a single build can only ever run one of
 * them; `scripts/ci/check_clmul_paths.sh` therefore compiles this twice, once
 * plain and once with the flags that enable an intrinsic, and this program
 * reports which path it got.
 *
 * When an intrinsic is compiled it is compared against the portable reference
 * on every vector, which is the divergence the SPEC is worried about. When it
 * is not, the portable path is still checked against known-answer vectors, so
 * a plain build is not vacuous.
 *
 * The Lean side of the same obligation is `conformance/HexGF2/CrossCheck.lean`,
 * which compares the extern against `Hex.pureClmul` over a pseudorandom stream.
 */
#include <stdint.h>
#include <stdio.h>

void hex_clmul_portable(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo);
int hex_clmul_uses_intrinsic(void);
#if defined(HEX_CLMUL_SELFTEST_EXPECT_INTRINSIC)
void hex_clmul_intrinsic(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo);
#endif

/* Known answers, computed independently of this C code: the first three are
   hand-derived, the rest come from `Hex.pureClmul` evaluated in Lean. */
struct known { uint64_t a, b, hi, lo; };
static const struct known KNOWN[] = {
    { 0u, 0u, 0u, 0u },
    { 1u, 1u, 0u, 1u },
    { 2u, 2u, 0u, 4u },
    { 3u, 3u, 0u, 5u },
    { 0xFFu, 0xFFu, 0u, 0x5555u },
    { 0x8000000000000000ull, 2u, 1u, 0u },
    { 0x8000000000000000ull, 0x8000000000000000ull, 0x4000000000000000ull, 0u },
};

/* Deterministic MMIX linear congruential generator, the same one the Lean
   cross-check uses, so the two halves sweep comparable input shapes. */
static uint64_t next(uint64_t* state) {
    *state = *state * 6364136223846793005ull + 1442695040888963407ull;
    return *state;
}

int main(void) {
    int intrinsic = hex_clmul_uses_intrinsic();
    printf("clmul self-test: intrinsic path %s\n",
           intrinsic ? "compiled" : "not compiled (portable fallback)");

#if defined(HEX_CLMUL_SELFTEST_EXPECT_INTRINSIC)
    if (!intrinsic) {
        fprintf(stderr,
                "clmul self-test: expected an intrinsic build, but the guards "
                "selected the portable path; the flags did not take effect\n");
        return 2;
    }
#endif

    for (unsigned i = 0; i < sizeof(KNOWN) / sizeof(KNOWN[0]); ++i) {
        uint64_t hi, lo;
        hex_clmul_portable(KNOWN[i].a, KNOWN[i].b, &hi, &lo);
        if (hi != KNOWN[i].hi || lo != KNOWN[i].lo) {
            fprintf(stderr,
                    "clmul self-test: portable disagrees with known answer at "
                    "vector %u: got (%llx, %llx), want (%llx, %llx)\n",
                    i, (unsigned long long)hi, (unsigned long long)lo,
                    (unsigned long long)KNOWN[i].hi,
                    (unsigned long long)KNOWN[i].lo);
            return 1;
        }
    }

#if defined(HEX_CLMUL_SELFTEST_EXPECT_INTRINSIC)
    uint64_t state = 0x243F6A8885A308D3ull;
    for (unsigned i = 0; i < 100000u; ++i) {
        uint64_t a = next(&state);
        uint64_t b = next(&state);
        uint64_t phi, plo, ihi, ilo;
        hex_clmul_portable(a, b, &phi, &plo);
        hex_clmul_intrinsic(a, b, &ihi, &ilo);
        if (phi != ihi || plo != ilo) {
            fprintf(stderr,
                    "clmul self-test: intrinsic and portable disagree on "
                    "(%llx, %llx): portable (%llx, %llx), intrinsic (%llx, %llx)\n",
                    (unsigned long long)a, (unsigned long long)b,
                    (unsigned long long)phi, (unsigned long long)plo,
                    (unsigned long long)ihi, (unsigned long long)ilo);
            return 1;
        }
    }
    printf("clmul self-test: intrinsic agrees with portable on 100000 pairs\n");
#else
    (void)next;
#endif

    printf("clmul self-test: OK\n");
    return 0;
}
