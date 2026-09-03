/*
 * Lean bridge for the pinned dense-nauty 2.9.3 configuration used by
 * hex-graph-iso. See NautyFFI/Basic.lean for the wire format.
 */
#include <lean/lean.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include "nauty.h"

static lean_obj_res empty_result(void) {
    return lean_alloc_sarray(1, 0, 0);
}

static uint32_t read_u32_le(uint8_t const *p) {
    return ((uint32_t)p[0]) |
           ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

static void write_u32_le(uint8_t *p, uint32_t value) {
    p[0] = (uint8_t)value;
    p[1] = (uint8_t)(value >> 8);
    p[2] = (uint8_t)(value >> 16);
    p[3] = (uint8_t)(value >> 24);
}

LEAN_EXPORT lean_obj_res lean_nauty_canonicalize(
        size_t n_in, size_t color_count_in,
        b_lean_obj_arg colors_obj, b_lean_obj_arg adjacency_obj) {
    if (n_in == 0 || n_in > INT_MAX || color_count_in == 0 ||
            color_count_in > n_in || n_in > SIZE_MAX / n_in ||
            n_in > SIZE_MAX / 4 ||
            lean_sarray_size(colors_obj) != 4 * n_in ||
            lean_sarray_size(adjacency_obj) != n_in * n_in) {
        return empty_result();
    }
    int n = (int)n_in;
    int color_count = (int)color_count_in;
    uint8_t const *colors = lean_sarray_cptr(colors_obj);
    uint8_t const *adjacency = lean_sarray_cptr(adjacency_obj);
    int m = SETWORDSNEEDED(n);
    nauty_check(WORDSIZE, m, n, NAUTYVERSIONID);

    graph *g = malloc((size_t)m * (size_t)n * sizeof(graph));
    graph *canong = malloc((size_t)m * (size_t)n * sizeof(graph));
    int *lab = malloc((size_t)n * sizeof(int));
    int *ptn = malloc((size_t)n * sizeof(int));
    int *orbits = malloc((size_t)n * sizeof(int));
    if (g == NULL || canong == NULL || lab == NULL || ptn == NULL || orbits == NULL) {
        free(g); free(canong); free(lab); free(ptn); free(orbits);
        return empty_result();
    }

    DEFAULTOPTIONS_GRAPH(options);
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
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (adjacency[(size_t)i * (size_t)n + (size_t)j] != 0) {
                ADDONEEDGE(g, i, j, m);
            }
        }
    }

    int position = 0;
    for (int color = 0; color < color_count; ++color) {
        int start = position;
        for (int vertex = 0; vertex < n; ++vertex) {
            uint32_t vertex_color = read_u32_le(colors + 4 * (size_t)vertex);
            if (vertex_color >= (uint32_t)color_count) {
                free(g); free(canong); free(lab); free(ptn); free(orbits);
                return empty_result();
            }
            if (vertex_color == (uint32_t)color) {
                lab[position++] = vertex;
            }
        }
        if (position == start) {
            free(g); free(canong); free(lab); free(ptn); free(orbits);
            return empty_result();
        }
        for (int i = start; i < position; ++i) ptn[i] = 1;
        ptn[position - 1] = 0;
    }

    densenauty(g, lab, ptn, orbits, &options, &stats, m, n, canong);

    size_t triangle_size = (size_t)n * (size_t)(n - 1) / 2;
    size_t output_size = 4 * (size_t)n + triangle_size;
    lean_obj_res output = lean_alloc_sarray(1, output_size, output_size);
    uint8_t *out = lean_sarray_cptr(output);
    for (int i = 0; i < n; ++i) write_u32_le(out + 4 * (size_t)i, (uint32_t)lab[i]);
    out += 4 * (size_t)n;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            *out++ = ISELEMENT(GRAPHROW(canong, i, m), j) ? 1 : 0;
        }
    }

    free(g); free(canong); free(lab); free(ptn); free(orbits);
    return output;
}
