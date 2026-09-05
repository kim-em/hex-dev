/* Pinned-options densenauty shim for the HexGraphIso conformance oracle.
 *
 * Compiled by scripts/oracle/graphiso_nauty.py against the hash-verified
 * nauty 2.9.3 source (SHA-256
 * 9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b).
 * The oracle uses 64-bit dense densenauty, m = SETWORDSNEEDED(n), and
 * DEFAULTOPTIONS_GRAPH, changing only the fields required for canonical
 * labelling and a caller-supplied partition, per
 * HexGraphIso/SPEC/hex-graph-iso.md section "nauty compatibility target".
 *
 * Protocol (one case per request, n >= 1):
 *   stdin:  "n k" / colour[0..n-1] / n rows of n chars '0'/'1' / ...
 *           terminated by "-1 -1"
 *   stdout: "lab <n ints> | tri <C(n,2) bits> | nodes <numnodes>
 *            | gens <numgenerators> <numgenerators * n ints>
 *            | orbits <n ints> | norbits <numorbits>
 *            | grp <grpsize1> <grpsize2>"
 *
 * The generators are collected through options.userautomproc, which
 * nauty calls once per emitted generator in discovery order, so the
 * list is the traversal's own output rather than a recomputation.
 * The group order is stats.grpsize1 * 10^stats.grpsize2.
 *
 * lab is initialized by increasing colour and then increasing original
 * vertex; ptn ends exactly at the last position of each colour cell; no
 * active set is passed, so densenauty activates every initial cell. The
 * upper-triangle bits are serialized in row-major order; raw C setwords
 * are never compared.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "nauty.h"

static int *genbuf = NULL;
static size_t gencap = 0;   /* capacity in ints */
static size_t ngens = 0;    /* generators collected */

static void collectgen(int count, int *perm, int *orbits, int numorbits,
                       int stabvertex, int nn) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex;
    size_t need = (ngens + 1) * (size_t)nn;
    if (need > gencap) {
        size_t cap = gencap ? gencap * 2 : 1024;
        while (cap < need) cap *= 2;
        int *grown = realloc(genbuf, cap * sizeof(int));
        if (!grown) { fprintf(stderr, "shim: out of memory\n"); exit(3); }
        genbuf = grown;
        gencap = cap;
    }
    for (int i = 0; i < nn; i++) genbuf[ngens * (size_t)nn + i] = perm[i];
    ngens++;
}

int main(void) {
    DYNALLSTAT(graph, g, g_sz);
    DYNALLSTAT(graph, canong, canong_sz);
    DYNALLSTAT(int, lab, lab_sz);
    DYNALLSTAT(int, ptn, ptn_sz);
    DYNALLSTAT(int, orbits, orbits_sz);
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    int n, k;
    char row[4100];
    const int rowcap = (int)sizeof(row) - 1;

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
    options.userautomproc = collectgen;

    while (scanf("%d %d", &n, &k) == 2) {
        if (n < 1) break;
        if (n > rowcap) {
            fprintf(stderr, "shim: n = %d exceeds the row buffer\n", n);
            return 4;
        }
        int m = SETWORDSNEEDED(n);
        nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);
        DYNALLOC2(graph, g, g_sz, m, n, "malloc");
        DYNALLOC2(graph, canong, canong_sz, m, n, "malloc");
        DYNALLOC1(int, lab, lab_sz, n, "malloc");
        DYNALLOC1(int, ptn, ptn_sz, n, "malloc");
        DYNALLOC1(int, orbits, orbits_sz, n, "malloc");
        int *col = malloc(n * sizeof(int));
        if (!col) { fprintf(stderr, "shim: out of memory\n"); return 3; }
        for (int i = 0; i < n; i++)
            if (scanf("%d", &col[i]) != 1) return 2;
        EMPTYGRAPH(g, m, n);
        for (int i = 0; i < n; i++) {
            if (scanf("%4099s", row) != 1) return 2;
            if ((int)strlen(row) != n) {
                fprintf(stderr, "shim: adjacency row of length %zu for "
                                "n = %d\n", strlen(row), n);
                return 5;
            }
            for (int j = 0; j < n; j++)
                if (row[j] == '1' && i < j) { ADDONEEDGE(g, i, j, m); }
        }
        int pos = 0;
        for (int c = 0; c < k; c++) {
            int start = pos;
            for (int v = 0; v < n; v++)
                if (col[v] == c) lab[pos++] = v;
            for (int i = start; i < pos; i++) ptn[i] = 1;
            if (pos > start) ptn[pos-1] = 0;
        }
        ngens = 0;
        densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);
        printf("lab");
        for (int i = 0; i < n; i++) printf(" %d", lab[i]);
        printf(" | tri ");
        for (int i = 0; i < n; i++)
            for (int j = i+1; j < n; j++)
                printf("%d", ISELEMENT(GRAPHROW(canong, i, m), j) ? 1 : 0);
        printf(" | nodes %lu", stats.numnodes);
        printf(" | gens %lu", (unsigned long)ngens);
        for (size_t t = 0; t < ngens; t++)
            for (int i = 0; i < n; i++)
                printf(" %d", genbuf[t * (size_t)n + i]);
        printf(" | orbits");
        for (int i = 0; i < n; i++) printf(" %d", orbits[i]);
        printf(" | norbits %d", stats.numorbits);
        printf(" | grp %.17g %d\n", stats.grpsize1, stats.grpsize2);
        fflush(stdout);
        free(col);
    }
    return 0;
}
