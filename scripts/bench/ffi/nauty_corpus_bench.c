/* Standalone nauty 2.9.3 timing reference over a shared corpus file.
 *
 * The in-process comparator `Hex/BenchOracle/ffi/nauty_canon.c` is
 * called from Lean, and its caller pays an O(n^2) marshalling cost on
 * both sides of the FFI boundary inside the timed region: the adjacency
 * is pushed a byte at a time into a `ByteArray`, and the canonical
 * upper triangle comes back as an n(n-1)/2 character `String`. At the
 * sizes the scaling sweeps reach that marshalling is a large fraction
 * of what is being reported as nauty's time, which flatters every Lean
 * implementation it is compared against. This driver runs the same
 * pinned densenauty configuration with no marshalling at all. It emits
 * two numbers per instance: `nauty_ns` times `densenauty` on an already
 * built bitset graph, and `nauty_whole_ns` charges the dense-to-bitset
 * conversion as well, which is the column to put beside a Lean
 * implementation that converts inside its own timed region.
 *
 * Corpus format (written by `hexgraphiso_cactus dump`): repeated blocks
 * of a header `G <name> <family> <n>` followed by n lines of n 0/1
 * characters. Emits one JSON line per instance.
 *
 *   cc -O2 -DUSE_TLS -I vendor/nauty-2.9.3 -o nautybench \
 *      scripts/bench/ffi/nauty_corpus_bench.c \
 *      .lake/build/vendor/nauty-2.9.3/[nauty objects]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "nauty.h"

static long long now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (long long)t.tv_sec * 1000000000LL + t.tv_nsec;
}

/* The pinned configuration, field for field the one in
 * Hex/BenchOracle/ffi/nauty_canon.c. */
static void run_once(graph *g, graph *canong, int *lab, int *ptn, int *orbits,
                     int m, int n, statsblk *stats) {
    static DEFAULTOPTIONS_GRAPH(options);
    options.getcanon = TRUE;
    options.digraph = FALSE;
    options.defaultptn = FALSE;
    options.writeautoms = FALSE;
    options.writemarkers = FALSE;
    options.tc_level = 100;
    options.invarproc = NULL;
    options.mininvarlevel = 0;
    options.maxinvarlevel = 1;
    options.invararg = 0;
    options.schreier = FALSE;
    for (int i = 0; i < n; i++) { lab[i] = i; ptn[i] = 1; }
    ptn[n - 1] = 0;
    densenauty(g, lab, ptn, orbits, &options, stats, m, n, canong);
}

/* Fill nauty's bitset representation from a dense 0/1 byte matrix. */
static void fill_graph(graph *g, unsigned char const *dense, int m, int n) {
    EMPTYGRAPH(g, m, n);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (dense[(size_t)i * n + j]) { ADDONEEDGE(g, i, j, m); }
}

/* Repeat until the measured work has run for a while, so that a
 * microsecond instance is not timed once against a noisy clock; capped
 * so that a slow instance still runs a handful of times. */
#define REPS 25
#define MIN_TOTAL_NS 50000000LL

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: nautybench <corpus>\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 2; }

    size_t cap = 1 << 20;
    char *line = malloc(cap);
    char name[256], family[256];
    int n;
    while (fgets(line, (int)cap, f)) {
        if (sscanf(line, "G %255s %255s %d", name, family, &n) != 3) continue;
        int m = SETWORDSNEEDED(n);
        nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);
        size_t need = (size_t)n + 4;
        if (need > cap) { cap = need * 2; line = realloc(line, cap); }
        graph *g = malloc((size_t)m * n * sizeof(graph));
        graph *canong = malloc((size_t)m * n * sizeof(graph));
        int *lab = malloc(n * sizeof(int));
        int *ptn = malloc(n * sizeof(int));
        int *orbits = malloc(n * sizeof(int));
        unsigned char *dense = malloc((size_t)n * n);
        for (int i = 0; i < n; i++) {
            if (!fgets(line, (int)cap, f)) { fprintf(stderr, "short corpus\n"); return 2; }
            for (int j = 0; j < n; j++)
                dense[(size_t)i * n + j] = (line[j] == '1');
        }
        fill_graph(g, dense, m, n);
        statsblk stats;
        run_once(g, canong, lab, ptn, orbits, m, n, &stats);  /* warmup */
        long long best = -1, whole = -1, spent = 0;
        for (int r = 0; r < REPS; r++) {
            if (r >= 5 && spent > MIN_TOTAL_NS) break;
            long long t0 = now_ns();
            run_once(g, canong, lab, ptn, orbits, m, n, &stats);
            long long dt = now_ns() - t0;
            spent += dt;
            if (best < 0 || dt < best) best = dt;
            /* the same run charged the dense-to-bitset conversion, which
             * is what the Lean columns pay inside their own timers */
            long long t1 = now_ns();
            fill_graph(g, dense, m, n);
            run_once(g, canong, lab, ptn, orbits, m, n, &stats);
            long long dw = now_ns() - t1;
            spent += dw;
            if (whole < 0 || dw < whole) whole = dw;
            if (dt > 1000000000LL) break;  /* one rep suffices past a second */
        }
        printf("{\"name\": \"%s\", \"family\": \"%s\", \"n\": %d, "
               "\"nauty_ns\": %lld, \"nauty_whole_ns\": %lld, "
               "\"nauty_nodes\": %lu}\n",
               name, family, n, best, whole, (unsigned long)stats.numnodes);
        fflush(stdout);
        free(g); free(canong); free(lab); free(ptn); free(orbits); free(dense);
    }
    free(line);
    fclose(f);
    return 0;
}
