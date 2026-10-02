/* Pinned nauty 2.9.3 oracle, dense by default, --sparse for sparsegraph.
 *
 * Requests: n k, then n colours, then either n binary adjacency rows
 * (dense) or an edge count and that many endpoint pairs (sparse).
 * A negative n terminates the stream. Responses contain canonical labels,
 * adjacency (tri or edges), all seven statistics, emitted generators,
 * orbits, and level indices whose exact product is the group order.
 * --trace writes read-only node diagnostics as JSONL to stderr.
 * The vendored implementation is unmodified; callbacks only collect data.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include "nausparse.h"

#define SORT_OF_SORT 3
#define SORT_NAME oracle_sortindirect
#define SORT_TYPE1 int
#define SORT_TYPE2 int
#include "sorttemplates.c"

static int *genbuf, *indices;
static size_t gencap, ngens, nindices;
static unsigned long case_id;

static void fail(const char *message) {
    fprintf(stderr, "shim: %s\n", message);
    exit(2);
}

static void *allocate(size_t count, size_t size) {
    if (count > SIZE_MAX / size) fail("allocation overflow");
    void *p = calloc(count ? count : 1, size);
    if (!p) fail("out of memory");
    return p;
}

static void collectgen(int count, int *perm, int *orbits, int numorbits,
                       int stabvertex, int n) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex;
    if (ngens >= SIZE_MAX / sizeof(int) / (size_t)n - 1)
        fail("generator buffer overflow");
    size_t need = (ngens + 1) * (size_t)n;
    if (need > gencap) {
        int *grown = realloc(genbuf, need * sizeof(int));
        if (!grown) fail("out of memory for generators");
        genbuf = grown;
        gencap = need;
    }
    memcpy(genbuf + ngens * (size_t)n, perm, (size_t)n * sizeof(int));
    ++ngens;
}

static void collectlevel(int *lab, int *ptn, int level, int *orbits,
                         statsblk *stats, int tv, int index, int tcellsize,
                         int numcells, int childcount, int n) {
    (void)lab; (void)ptn; (void)level; (void)orbits; (void)stats;
    (void)tv; (void)tcellsize; (void)childcount;
    if (numcells == n) nindices = 0;
    else {
        if (index < 1 || nindices >= (size_t)n) fail("invalid level index");
        indices[nindices++] = index;
    }
}

static void trace_node(graph *g, int *lab, int *ptn, int level,
                       int numcells, int tc, int code, int m, int n) {
    (void)g; (void)m;
    fprintf(stderr, "{\"case\":%lu,\"level\":%d,\"numcells\":%d,"
                    "\"target\":%d,\"code\":%d,\"lab\":[",
            case_id, level, numcells, tc, code);
    for (int i = 0; i < n; ++i) fprintf(stderr, "%s%d", i ? "," : "", lab[i]);
    fprintf(stderr, "],\"ptn\":[");
    for (int i = 0; i < n; ++i) fprintf(stderr, "%s%d", i ? "," : "", ptn[i]);
    fprintf(stderr, "]}\n");
}

static void read_sparse(sparsegraph *sg, int n) {
    size_t ne;
    if (scanf("%zu", &ne) != 1 || ne > SIZE_MAX / 2 / sizeof(int))
        fail("invalid edge count");
    int *pairs = allocate(2 * ne, sizeof(int));
    SG_ALLOC(*sg, n, 2 * ne, "oracle sparse graph");
    sg->nv = n;
    for (int i = 0; i < n; ++i) sg->d[i] = 0;
    for (size_t i = 0; i < ne; ++i) {
        int a,b;
        if (scanf("%d %d", &a, &b) != 2 || a < 0 || b < 0 || a >= n || b >= n || a == b)
            fail("invalid edge");
        if (sg->d[a] == INT_MAX || sg->d[b] == INT_MAX) fail("degree overflow");
        ++sg->d[a]; ++sg->d[b]; pairs[2*i] = a; pairs[2*i+1] = b;
    }
    size_t *cursor = allocate(n, sizeof(size_t));
    size_t pos = 0;
    for (int i = 0; i < n; ++i) {
        cursor[i] = sg->v[i] = pos;
        pos += (size_t)sg->d[i];
    }
    for (size_t i = 0; i < ne; ++i) {
        int a = pairs[2*i], b = pairs[2*i+1];
        sg->e[cursor[a]++] = b; sg->e[cursor[b]++] = a;
    }
    free(cursor); free(pairs);
    sortlists_sg(sg);
    /* Normalize duplicate edges, preserving sorted contiguous rows. */
    pos = 0;
    for (int i = 0; i < n; ++i) {
        size_t old = sg->v[i];
        int degree = sg->d[i], previous = -1;
        sg->v[i] = pos; sg->d[i] = 0;
        for (int j = 0; j < degree; ++j) {
            int v = sg->e[old + j];
            if (v != previous) { sg->e[pos++] = v; ++sg->d[i]; }
            previous = v;
        }
    }
    sg->nde = pos;
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--sort")) {
        int size, start, len;
        while (scanf("%d %d %d", &size, &start, &len) == 3) {
            if (size < 0) break;
            if (start < 0 || len < 0 || len > size || start > size - len)
                fail("invalid sort interval");
            int *x = allocate(size, sizeof(int)), *y = allocate(size, sizeof(int));
            for (int i = 0; i < size; ++i)
                if (scanf("%d", &x[i]) != 1 || x[i] < 0 || x[i] >= size)
                    fail("invalid sort index");
            for (int i = 0; i < size; ++i)
                if (scanf("%d", &y[i]) != 1 || y[i] < 0) fail("invalid sort key");
            oracle_sortindirect(x + start, y, len);
            for (int i = 0; i < size; ++i) printf("%s%d", i ? " " : "", x[i]);
            putchar('\n');
            free(x); free(y);
        }
        return 0;
    }
    int sparse = 0, trace = 0, refinement = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--sparse")) sparse = 1;
        else if (!strcmp(argv[i], "--trace")) trace = 1;
        else if (!strcmp(argv[i], "--refine")) sparse = refinement = 1;
        else fail("unknown option");
    }
    DEFAULTOPTIONS_GRAPH(dense_options);
    DEFAULTOPTIONS_SPARSEGRAPH(sparse_options);
    optionblk options = sparse ? sparse_options : dense_options;
    options.getcanon = TRUE;
    options.defaultptn = FALSE;
    options.userautomproc = collectgen;
    options.userlevelproc = collectlevel;
    if (trace) options.usernodeproc = trace_node;
    int n,k;
    for (;;) {
        int fields = scanf("%d %d", &n, &k);
        if (fields == EOF) break;
        if (fields != 2) fail("truncated graph header");
        if (n < 0) break;
        if (n < 1 || k < 1 || k > n) fail("invalid vertex or colour count");
        int m = SETWORDSNEEDED(n);
        nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);
        int *lab = allocate(n, sizeof(int)), *ptn = allocate(n, sizeof(int));
        int *orbits = allocate(n, sizeof(int)), *col = allocate(n, sizeof(int));
        indices = allocate(n, sizeof(int));
        for (int i = 0; i < n; ++i)
            if (scanf("%d", &col[i]) != 1 || col[i] < 0 || col[i] >= k)
                fail("invalid colour");
        int pos = 0;
        for (int c = 0; c < k; ++c) {
            int start = pos;
            for (int v = 0; v < n; ++v) if (col[v] == c) lab[pos++] = v;
            if (pos == start) fail("empty colour cell");
            for (int i = start; i < pos; ++i) ptn[i] = 1;
            ptn[pos-1] = 0;
        }
        graph *g = NULL, *canong = NULL;
        SG_DECL(sg); SG_DECL(sc);
        if (sparse) read_sparse(&sg, n);
        else {
            g = allocate((size_t)m * n, sizeof(graph));
            canong = allocate((size_t)m * n, sizeof(graph));
            for (int i = 0; i < n; ++i) {
                char ch;
                for (int j = 0; j < n; ++j) {
                    if (scanf(" %c", &ch) != 1 || (ch != '0' && ch != '1'))
                        fail("invalid adjacency entry");
                    if (ch == '1') ADDELEMENT(GRAPHROW(g, i, m), j);
                }
            }
            for (int i = 0; i < n; ++i) {
                if (ISELEMENT(GRAPHROW(g,i,m),i)) fail("loop");
                for (int j = i+1; j < n; ++j)
                    if (!!ISELEMENT(GRAPHROW(g,i,m),j) != !!ISELEMENT(GRAPHROW(g,j,m),i))
                        fail("asymmetric adjacency");
            }
        }
        if (refinement) {
            int level, cells, code;
            if (scanf("%d %d", &level, &cells) != 2 || level < 0 || cells < 1 || cells > n)
                fail("invalid refinement parameters");
            int *seen = allocate(n, sizeof(int)), *count = allocate(n, sizeof(int));
            set *active = allocate(m, sizeof(set));
            for (int i = 0; i < n; ++i)
                if (scanf("%d", &lab[i]) != 1 || lab[i] < 0 || lab[i] >= n || seen[lab[i]]++)
                    fail("invalid refinement labelling");
            for (int i = 0; i < n; ++i)
                if (scanf("%d", &ptn[i]) != 1 || ptn[i] < 0) fail("invalid partition entry");
            if (ptn[n-1] > level) fail("unterminated partition");
            int actual_cells = 0;
            for (int i = 0; i < n; ++i) actual_cells += ptn[i] <= level;
            if (cells != actual_cells) fail("incorrect partition cell count");
            for (int i = 0; i < n; ++i) {
                int activeFlag;
                if (scanf("%d", &activeFlag) != 1 || (activeFlag != 0 && activeFlag != 1))
                    fail("invalid active bit");
                if (activeFlag) {
                    if (i && ptn[i-1] > level) fail("active position is not a cell start");
                    ADDELEMENT(active, i);
                }
            }
            refine_sg((graph*)&sg, lab, ptn, level, &cells, count, active, &code, m, n);
            printf("{\"lab\":[");
            for (int i = 0; i < n; ++i) printf("%s%d", i ? "," : "", lab[i]);
            printf("],\"ptn\":[");
            for (int i = 0; i < n; ++i) printf("%s%d", i ? "," : "", ptn[i]);
            printf("],\"active\":[");
            for (int i = 0; i < n; ++i) printf("%s%d", i ? "," : "", !!ISELEMENT(active,i));
            printf("],\"numcells\":%d,\"code\":%d,\"target\":%d}\n", cells, code,
                targetcell_sg((graph*)&sg, lab, ptn, level, 100, FALSE, -1, m, n));
            free(seen); free(count); free(active);
            free(lab); free(ptn); free(orbits); free(col); free(indices);
            SG_FREE(sg); SG_FREE(sc);
            ++case_id;
            continue;
        }
        ngens = nindices = 0;
        statsblk stats;
        if (sparse) sparsenauty(&sg, lab, ptn, orbits, &options, &stats, &sc);
        else densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);
        if (stats.errstatus) fail("nauty error");
        printf("lab"); for (int i = 0; i < n; ++i) printf(" %d", lab[i]);
        if (sparse) {
            sortlists_sg(&sc);
            printf(" | edges %zu", sc.nde / 2);
            for (int i = 0; i < n; ++i) for (int j = 0; j < sc.d[i]; ++j) {
                int v = sc.e[sc.v[i]+j]; if (i < v) printf(" %d %d", i, v);
            }
        } else {
            printf(" | tri ");
            for (int i = 0; i < n; ++i) for (int j = i+1; j < n; ++j)
                printf("%d", !!ISELEMENT(GRAPHROW(canong,i,m),j));
        }
        printf(" | nodes %lu | gens %zu", stats.numnodes, ngens);
        for (size_t i = 0; i < ngens * (size_t)n; ++i) printf(" %d", genbuf[i]);
        printf(" | orbits"); for (int i = 0; i < n; ++i) printf(" %d", orbits[i]);
        printf(" | norbits %d | grp %.17g %d | indices", stats.numorbits, stats.grpsize1, stats.grpsize2);
        for (size_t i = 0; i < nindices; ++i) printf(" %d", indices[i]);
        printf(" | stats %d %d %lu %lu %d %lu %lu\n", stats.numorbits,
               stats.numgenerators, stats.numnodes, stats.numbadleaves,
               stats.maxlevel, stats.tctotal, stats.canupdates);
        fflush(stdout);
        free(lab); free(ptn); free(orbits); free(col); free(indices);
        free(g); free(canong); SG_FREE(sg); SG_FREE(sc);
        ++case_id;
    }
    free(genbuf);
    return 0;
}
