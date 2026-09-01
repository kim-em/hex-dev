/* Pinned-options densenauty shim for the HexGraphIso conformance oracle.
 *
 * Compiled by scripts/oracle/graphiso_nauty.py against the hash-verified
 * nauty 2.9.3 source (SHA-256
 * 9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b).
 * The oracle uses 64-bit dense densenauty, m = SETWORDSNEEDED(n), and
 * DEFAULTOPTIONS_GRAPH, changing only the fields required for canonical
 * labelling and a caller-supplied partition, per
 * SPEC/Libraries/hex-graph-iso.md section "nauty compatibility target".
 *
 * Protocol (one case per request, n >= 1):
 *   stdin:  "n k" / colour[0..n-1] / n rows of n chars '0'/'1' / ...
 *           terminated by "-1 -1"
 *   stdout: "lab <n ints> | tri <C(n,2) bits> | nodes <numnodes>"
 *
 * lab is initialized by increasing colour and then increasing original
 * vertex; ptn ends exactly at the last position of each colour cell; no
 * active set is passed, so densenauty activates every initial cell. The
 * upper-triangle bits are serialized in row-major order; raw C setwords
 * are never compared.
 */
#include <stdio.h>
#include <stdlib.h>
#include "nauty.h"

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

    while (scanf("%d %d", &n, &k) == 2) {
        if (n < 1) break;
        int m = SETWORDSNEEDED(n);
        nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);
        DYNALLOC2(graph, g, g_sz, m, n, "malloc");
        DYNALLOC2(graph, canong, canong_sz, m, n, "malloc");
        DYNALLOC1(int, lab, lab_sz, n, "malloc");
        DYNALLOC1(int, ptn, ptn_sz, n, "malloc");
        DYNALLOC1(int, orbits, orbits_sz, n, "malloc");
        int *col = malloc(n * sizeof(int));
        for (int i = 0; i < n; i++)
            if (scanf("%d", &col[i]) != 1) return 2;
        EMPTYGRAPH(g, m, n);
        for (int i = 0; i < n; i++) {
            if (scanf("%s", row) != 1) return 2;
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
        densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);
        printf("lab");
        for (int i = 0; i < n; i++) printf(" %d", lab[i]);
        printf(" | tri ");
        for (int i = 0; i < n; i++)
            for (int j = i+1; j < n; j++)
                printf("%d", ISELEMENT(GRAPHROW(canong, i, m), j) ? 1 : 0);
        printf(" | nodes %lu\n", stats.numnodes);
        fflush(stdout);
        free(col);
    }
    return 0;
}
