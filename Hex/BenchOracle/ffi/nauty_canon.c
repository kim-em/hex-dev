/* Pinned-options densenauty FFI comparator for Hex bench drivers.
 *
 * Compiled against the vendored nauty 2.9.3 source in
 * vendor/nauty-2.9.3 (see that directory's README for provenance).
 * The nauty configuration is identical to the conformance oracle shim
 * scripts/oracle/graphiso_nauty_shim.c: 64-bit dense densenauty,
 * m = SETWORDSNEEDED(n), DEFAULTOPTIONS_GRAPH changing only the fields
 * required for canonical labelling and a caller-supplied partition, per
 * SPEC/Libraries/hex-graph-iso.md section "nauty compatibility target".
 *
 * Marshalling (Lean binding: Hex/BenchOracle/Nauty.lean):
 *   in:  n, k as USize (1 <= n <= 255, k <= n);
 *        colors as a ByteArray of n colour bytes;
 *        adj as a ByteArray of n*n row-major 0/1 bytes.
 *   out: ByteArray of n lab bytes, then n*(n-1)/2 upper-triangle 0/1
 *        bytes of the canonical adjacency in row-major order, then the
 *        visited-node count as 8 little-endian bytes.
 *
 * lab is initialized by increasing colour and then increasing original
 * vertex; ptn ends exactly at the last position of each colour cell; no
 * active set is passed, so densenauty activates every initial cell.
 * Raw C setwords are never returned. Not thread-safe (nauty keeps
 * internal state); Hex bench drivers are single-threaded.
 */
#include <lean/lean.h>
#include <stdlib.h>
#include "nauty.h"

LEAN_EXPORT lean_obj_res hex_nauty_canon(size_t n_in, size_t k_in,
        b_lean_obj_arg colors_obj, b_lean_obj_arg adj_obj) {
    int n = (int)n_in;
    int k = (int)k_in;
    uint8_t const *col = lean_sarray_cptr(colors_obj);
    uint8_t const *adj = lean_sarray_cptr(adj_obj);
    int m = SETWORDSNEEDED(n);
    nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);

    graph *g = malloc((size_t)m * n * sizeof(graph));
    graph *canong = malloc((size_t)m * n * sizeof(graph));
    int *lab = malloc(n * sizeof(int));
    int *ptn = malloc(n * sizeof(int));
    int *orbits = malloc(n * sizeof(int));
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;

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

    EMPTYGRAPH(g, m, n);
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (adj[(size_t)i * n + j]) { ADDONEEDGE(g, i, j, m); }
    int pos = 0;
    for (int c = 0; c < k; c++) {
        int start = pos;
        for (int v = 0; v < n; v++)
            if (col[v] == c) lab[pos++] = v;
        for (int i = start; i < pos; i++) ptn[i] = 1;
        if (pos > start) ptn[pos - 1] = 0;
    }
    densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);

    size_t tri = (size_t)n * (n - 1) / 2;
    size_t out_len = (size_t)n + tri + 8;
    lean_obj_res out = lean_alloc_sarray(1, out_len, out_len);
    uint8_t *o = lean_sarray_cptr(out);
    for (int i = 0; i < n; i++) *o++ = (uint8_t)lab[i];
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            *o++ = ISELEMENT(GRAPHROW(canong, i, m), j) ? 1 : 0;
    unsigned long nodes = stats.numnodes;
    for (int b = 0; b < 8; b++) *o++ = (uint8_t)(nodes >> (8 * b));

    free(g); free(canong); free(lab); free(ptn); free(orbits);
    return out;
}
