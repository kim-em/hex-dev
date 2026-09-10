/* Standalone nauty 2.9.3 timing reference over a shared corpus file.
 *
 * Times all three of the distribution's canonical labelling engines on
 * the same instance: dense `densenauty`, `sparsenauty`, and `Traces`.
 * The dense engine is the one HexGraphIso transcribes and the one the
 * pinned configuration names, but it is the wrong tool on a sparse
 * graph, and the nauty and Traces literature is explicit that the other
 * two exist for exactly the classes where it struggles. Reporting all
 * three keeps a Lean implementation from being flattered or damned by
 * whichever engine happens to be a bad fit for a family.
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
 * two numbers per engine per instance: `<engine>_ns` times the search on
 * an already built native graph, and `<engine>_whole_ns` charges the
 * conversion from the dense corpus form as well, which is the column to
 * put beside a Lean implementation that converts inside its own timed
 * region.
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
#include "nausparse.h"
#include "traces.h"

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

/* Fill a sparsegraph from a dense 0/1 byte matrix. */
static void fill_sparse(sparsegraph *sg, unsigned char const *dense, int n) {
    size_t m = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (dense[(size_t)i * n + j]) m++;
    SG_ALLOC(*sg, n, m, "fill_sparse");
    sg->nv = n;
    sg->nde = m;
    size_t k = 0;
    for (int i = 0; i < n; i++) {
        sg->v[i] = k;
        int d = 0;
        for (int j = 0; j < n; j++)
            if (dense[(size_t)i * n + j]) { sg->e[k++] = j; d++; }
        sg->d[i] = d;
    }
}

/* The pinned configuration transposed to the sparse dispatch: the same
 * fields nauty_canon.c sets, minus the ones that are dense-only. */
static void run_sparse(sparsegraph *sg, sparsegraph *canon, int *lab, int *ptn,
                       int *orbits, int n, statsblk *stats) {
    static DEFAULTOPTIONS_SPARSEGRAPH(options);
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
    sparsenauty(sg, lab, ptn, orbits, &options, stats, canon);
}

/* Traces takes no invariant and no tc_level; the only fields that
 * matter here are the canonical labelling and the caller-supplied
 * partition. */
static void run_traces(sparsegraph *sg, sparsegraph *canon, int *lab, int *ptn,
                       int *orbits, int n, TracesStats *stats) {
    static DEFAULTOPTIONS_TRACES(options);
    options.getcanon = TRUE;
    options.defaultptn = FALSE;
    options.writeautoms = FALSE;
    for (int i = 0; i < n; i++) { lab[i] = i; ptn[i] = 1; }
    ptn[n - 1] = 0;
    Traces(sg, lab, ptn, orbits, &options, stats, canon);
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
    if (argc < 2) {
        fprintf(stderr, "usage: nautybench <corpus> [dense|sparse|traces|all]\n");
        return 2;
    }
    /* One engine per process, so that a sweep under a per-instance time
     * budget spends the budget on the engine being judged and gives up
     * on a family per engine rather than for all three at once. */
    int do_dense = 1, do_sparse = 1, do_traces = 1;
    if (argc > 2 && strcmp(argv[2], "all") != 0) {
        do_dense = strcmp(argv[2], "dense") == 0;
        do_sparse = strcmp(argv[2], "sparse") == 0;
        do_traces = strcmp(argv[2], "traces") == 0;
        if (!do_dense && !do_sparse && !do_traces) {
            fprintf(stderr, "unknown engine %s\n", argv[2]);
            return 2;
        }
    }
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
        TracesStats tstats;
        sparsegraph sg, scanon;
        SG_INIT(sg);
        SG_INIT(scanon);
        fill_sparse(&sg, dense, n);

        long long spent = 0;
        long long dense_best = -1, dense_whole = -1;
        long long sparse_best = -1, sparse_whole = -1;
        long long traces_best = -1, traces_whole = -1;
        unsigned long sparse_nodes = 0, traces_nodes = 0;

        /* dense */
        if (do_dense) {
        run_once(g, canong, lab, ptn, orbits, m, n, &stats);  /* warmup */
        spent = 0;
        for (int r = 0; r < REPS; r++) {
            if (r >= 5 && spent > MIN_TOTAL_NS) break;
            long long t0 = now_ns();
            run_once(g, canong, lab, ptn, orbits, m, n, &stats);
            long long dt = now_ns() - t0;
            spent += dt;
            if (dense_best < 0 || dt < dense_best) dense_best = dt;
            /* the same run charged the dense-to-native conversion, which
             * is what the Lean columns pay inside their own timers */
            long long t1 = now_ns();
            fill_graph(g, dense, m, n);
            run_once(g, canong, lab, ptn, orbits, m, n, &stats);
            long long dw = now_ns() - t1;
            spent += dw;
            if (dense_whole < 0 || dw < dense_whole) dense_whole = dw;
            if (dt > 1000000000LL) break;
        }
        }

        /* sparse */
        if (do_sparse) {
        run_sparse(&sg, &scanon, lab, ptn, orbits, n, &stats);  /* warmup */
        sparse_nodes = stats.numnodes;
        spent = 0;
        for (int r = 0; r < REPS; r++) {
            if (r >= 5 && spent > MIN_TOTAL_NS) break;
            long long t0 = now_ns();
            run_sparse(&sg, &scanon, lab, ptn, orbits, n, &stats);
            long long dt = now_ns() - t0;
            spent += dt;
            if (sparse_best < 0 || dt < sparse_best) sparse_best = dt;
            long long t1 = now_ns();
            sparsegraph tmp;
            SG_INIT(tmp);
            fill_sparse(&tmp, dense, n);
            run_sparse(&tmp, &scanon, lab, ptn, orbits, n, &stats);
            long long dw = now_ns() - t1;
            SG_FREE(tmp);
            spent += dw;
            if (sparse_whole < 0 || dw < sparse_whole) sparse_whole = dw;
            if (dt > 1000000000LL) break;
        }
        }

        /* Traces */
        if (do_traces) {
        run_traces(&sg, &scanon, lab, ptn, orbits, n, &tstats);  /* warmup */
        traces_nodes = tstats.numnodes;
        spent = 0;
        for (int r = 0; r < REPS; r++) {
            if (r >= 5 && spent > MIN_TOTAL_NS) break;
            long long t0 = now_ns();
            run_traces(&sg, &scanon, lab, ptn, orbits, n, &tstats);
            long long dt = now_ns() - t0;
            spent += dt;
            if (traces_best < 0 || dt < traces_best) traces_best = dt;
            long long t1 = now_ns();
            sparsegraph tmp;
            SG_INIT(tmp);
            fill_sparse(&tmp, dense, n);
            run_traces(&tmp, &scanon, lab, ptn, orbits, n, &tstats);
            long long dw = now_ns() - t1;
            SG_FREE(tmp);
            spent += dw;
            if (traces_whole < 0 || dw < traces_whole) traces_whole = dw;
            if (dt > 1000000000LL) break;
        }
        }

        printf("{\"name\": \"%s\", \"family\": \"%s\", \"n\": %d",
               name, family, n);
        if (do_dense)
            printf(", \"nauty_ns\": %lld, \"nauty_whole_ns\": %lld, "
                   "\"nauty_nodes\": %lu", dense_best, dense_whole,
                   (unsigned long)stats.numnodes);
        if (do_sparse)
            printf(", \"sparse_ns\": %lld, \"sparse_whole_ns\": %lld, "
                   "\"sparse_nodes\": %lu", sparse_best, sparse_whole,
                   sparse_nodes);
        if (do_traces)
            printf(", \"traces_ns\": %lld, \"traces_whole_ns\": %lld, "
                   "\"traces_nodes\": %lu", traces_best, traces_whole,
                   traces_nodes);
        printf("}\n");
        fflush(stdout);
        SG_FREE(sg);
        SG_FREE(scanon);
        free(g); free(canong); free(lab); free(ptn); free(orbits); free(dense);
    }
    free(line);
    fclose(f);
    return 0;
}
