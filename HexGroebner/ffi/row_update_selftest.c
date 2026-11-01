/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */

#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#define HEX_GROEBNER_NO_LEAN
#include "row_update.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(__linux__)
#include <sys/mman.h>
#include <unistd.h>
#endif

static uint32_t seed = 4147;
static uint32_t random_word(void) {
    seed ^= seed << 13;
    seed ^= seed >> 17;
    seed ^= seed << 5;
    return seed;
}

static void fail(const char *message) {
    fprintf(stderr, "row_update_selftest: %s\n", message);
    exit(1);
}

static void check_scalar(uint64_t p, unsigned width, uint64_t a, uint64_t b, uint64_t factor) {
    uint8_t dense[4], coefficient[4], column[4] = {0};
    write_le(dense, width, a);
    write_le(coefficient, width, b);
    uint64_t expected = (a + p - (factor * b) % p) % p;
    if (!update_bytes(p, width, dense, width, column, coefficient, 0, 1, factor) ||
        read_le(dense, width) != expected) fail("scalar arithmetic boundary");
}

static void check_arithmetic(void) {
    /* Exhaust all products in the largest one-byte fields, placing a on both
       sides of the subtraction correction and exactly at cancellation. */
    const uint64_t small[] = {2, 3, 251, 256};
    for (size_t i = 0; i < sizeof(small) / sizeof(small[0]); ++i) {
        uint64_t p = small[i];
        for (uint64_t factor = 0; factor < p; ++factor) {
            for (uint64_t b = 0; b < p; ++b) {
                uint64_t product = (factor * b) % p;
                const uint64_t inputs[] = {0, p - 1, product,
                    product ? product - 1 : p - 1, product + 1 < p ? product + 1 : 0};
                for (size_t j = 0; j < sizeof(inputs) / sizeof(inputs[0]); ++j)
                    check_scalar(p, 1, inputs[j], b, factor);
            }
        }
    }
    const uint64_t wide[] = {257, 65521, 65536, 65537, 2147483647};
    /* Exhaust every b at the largest two-byte prime with maximal factor,
       checking both signs and exact cancellation of the reduced product. */
    for (uint64_t b = 0; b < 65521; ++b) {
        uint64_t product = (UINT64_C(65520) * b) % 65521;
        check_scalar(65521, 2, 0, b, 65520);
        check_scalar(65521, 2, 65520, b, 65520);
        check_scalar(65521, 2, product, b, 65520);
    }
    for (size_t i = 0; i < sizeof(wide) / sizeof(wide[0]); ++i) {
        uint64_t p = wide[i];
        unsigned width = p <= 65536 ? 2 : 4;
        const uint64_t values[] = {0, 1, 2, p / 2, p - 2, p - 1};
        for (size_t a = 0; a < sizeof(values) / sizeof(values[0]); ++a)
            for (size_t b = 0; b < sizeof(values) / sizeof(values[0]); ++b)
                for (size_t f = 0; f < sizeof(values) / sizeof(values[0]); ++f)
                    check_scalar(p, width, values[a], values[b], values[f]);
    }
}

static void check_monomials(void) {
    unsigned cases = 0;
    for (unsigned width = 1; width <= 4; width *= 2) {
        for (unsigned trial = 0; trial < 500; ++trial) {
            size_t n = trial % 129 + 1, bytes = 2 * n * width, output_bytes = 4 * n + 28;
            uint8_t *source = malloc(bytes), *output = malloc(output_bytes);
            uint64_t *left = malloc(n * sizeof(uint64_t)), *right = malloc(n * sizeof(uint64_t));
            if (!source || !output || !left || !right) fail("monomial allocation");
            uint64_t bound = width == 1 ? 256 : width == 2 ? 65536 : UINT64_C(4294967296);
            for (size_t i = 0; i < n; ++i) {
                left[i] = random_word() % bound;
                right[i] = trial % 2 ? random_word() % (left[i] + 1) : random_word() % bound;
                write_le(source + i * width, width, left[i]);
                write_le(source + (n + i) * width, width, right[i]);
            }
            for (unsigned operation = 0; operation < 3; ++operation) {
                int valid = 1, equal_left = 1, equal_right = 1;
                uint64_t degree = 0, mask = 0, hash = UINT64_C(14695981039346656037), largest = 0;
                int actual = prepare_monomial(operation, width, n, 2, 0, 1,
                    source, bytes, output, output_bytes);
                for (size_t i = 0; i < n; ++i) {
                    uint64_t x = left[i], y = right[i];
                    if ((operation == 1 && x + y >= UINT64_C(4294967296)) ||
                        (operation == 2 && y > x)) { valid = 0; break; }
                    uint64_t z = operation == 0 ? (x >= y ? x : y) : operation == 1 ? x + y : x - y;
                    if (actual && read_le(output + i * 4, 4) != z) fail("monomial coordinate");
                    equal_left &= z == x; equal_right &= z == y;
                    degree += z; if (z) mask |= UINT64_C(1) << (i % 64);
                    hash = (hash ^ z) * UINT64_C(1099511628211);
                    if (z > largest) largest = z;
                }
                if (actual != valid) fail("monomial overflow or quotient rejection");
                if (valid) {
                    uint64_t metadata[] = {degree, mask, hash};
                    for (size_t i = 0; i < 3; ++i) {
                        size_t offset = 4 * n + 8 * i;
                        uint64_t value = read_le(output + offset, 4) |
                            (read_le(output + offset + 4, 4) << 32);
                        if (value != metadata[i]) fail("monomial metadata");
                    }
                    if (read_le(output + 4 * n + 24, 4) != largest) fail("monomial maximum");
                    if (equal_monomial(width, n, 0, source, bytes, output, output_bytes) != equal_left ||
                        equal_monomial(width, n, 1, source, bytes, output, output_bytes) != equal_right)
                        fail("monomial exact equality");
                    if (equal_monomial(width, n, 2, source, bytes, output, output_bytes) ||
                        equal_monomial(width, n, 0, source, bytes, output, output_bytes - 1))
                        fail("monomial equality geometry");
                }
                ++cases;
            }
            free(source); free(output); free(left); free(right);
        }
    }
    {
        size_t n = 4096, source_bytes = 2 * n * 4, workspace_bytes = n * 4 + 28;
        uint8_t *source = malloc(source_bytes), *workspace = malloc(workspace_bytes);
        if (!source || !workspace) fail("maximum-arity allocation");
        memset(source, 255, source_bytes);
        if (!prepare_monomial(0, 4, n, 2, 0, 1, source, source_bytes, workspace, workspace_bytes))
            fail("maximum arity rejected");
        uint64_t degree = read_le(workspace + 4 * n, 4) |
            (read_le(workspace + 4 * n + 4, 4) << 32);
        if (degree != UINT64_C(4096) * UINT32_MAX ||
            read_le(workspace + 4 * n + 8, 4) != UINT32_MAX ||
            read_le(workspace + 4 * n + 12, 4) != UINT32_MAX ||
            !equal_monomial(4, n, 1, source, source_bytes, workspace, workspace_bytes))
            fail("maximum-arity metadata");
        if (prepare_monomial(0, 4, n, 2, 2, 0, source, source_bytes, workspace, workspace_bytes) ||
            prepare_monomial(0, 4, n, 2, 0, 2, source, source_bytes, workspace, workspace_bytes) ||
            prepare_monomial(0, 4, n, 2, 0, 1, source, source_bytes - 1, workspace, workspace_bytes))
            fail("maximum-arity invalid identifier or length");
        free(source); free(workspace);
    }
    if (monomial_shape(0, 4, 4096, UINT64_MAX, 0, 0, SIZE_MAX, 16412) ||
        monomial_shape(0, 4, 4097, 1, 0, 0, 16388, 16416) ||
        monomial_shape(0, 4, 0, 1, 0, 0, 0, 28) ||
        monomial_shape(3, 1, 1, 1, 0, 0, 1, 32) ||
        monomial_shape(0, 3, 1, 1, 0, 0, 3, 32)) fail("monomial malformed geometry");
    printf("monomial_selftest: %u cases and malformed boundaries OK\n", cases);
}

static void check_bytes(void) {
    uint8_t left[8193],right[8193];
    for(size_t i=0;i<sizeof(left);++i) left[i]=right[i]=(uint8_t)(i*7919+17);
    const size_t sizes[]={0,1,7,4095,4096,4097,8193};
    for(size_t changed=0;changed<sizeof(left);changed+=1024) {
        right[changed]^=1;
        for(size_t k=0;k<sizeof(sizes)/sizeof(sizes[0]);++k) {
            size_t size=sizes[k];
            const size_t offsets[]={0,1,size/2,size,size+1,SIZE_MAX};
            const size_t counts[]={0,1,7,4095,4096,4097,SIZE_MAX};
            for(size_t i=0;i<sizeof(offsets)/sizeof(offsets[0]);++i) {
                for(size_t j=0;j<sizeof(counts)/sizeof(counts[0]);++j) {
                    size_t start=offsets[i],count=counts[j];
                    int valid=count<=4096 && start<=size && count<=size-start;
                    int expected=valid;
                    if(valid) for(size_t n=0;n<count;++n) if(left[start+n]!=right[start+n]) expected=0;
                    if(equal_bytes(left,size,right,size,start,count)!=expected) fail("byte slice equality");
                    if(equal_bytes(left,size,left,size,start,count)!=valid) fail("aliased byte slice geometry");
                }
            }
        }
        right[changed]^=1;
    }
}

static void check_products(void) {
    const size_t arities[]={1,2,3,63,64,65,4096};
    for(unsigned width=1;width<=4;width*=2) {
        for(size_t k=0;k<sizeof(arities)/sizeof(arities[0]);++k) {
            size_t n=arities[k],terms=4096/n,stride=n*width,bytes=3*stride;
            uint8_t *arena=calloc(bytes,1),*base=malloc(terms*4),*result=malloc(terms*4);
            if(!arena || !base || !result) fail("product allocation");
            for(size_t j=0;j<n;++j) {
                uint64_t x=width==1?random_word()%128:width==2?random_word()%32768:random_word()>>1;
                write_le(arena+stride+j*width,width,x);
                write_le(arena+2*stride+j*width,width,2*x);
            }
            for(size_t i=0;i<terms;++i) {write_le(base+4*i,4,1);write_le(result+4*i,4,2);}
            if(!equal_products(width,n,3,1,0,terms,arena,bytes,base,terms*4,result,terms*4))
                fail("valid cached product rejected");
            if(!equal_products(width,n,3,0,0,terms,arena,bytes,base,terms*4,base,terms*4))
                fail("aliased cached product rejected");
            uint64_t last=read_le(arena+bytes-width,width);
            write_le(arena+bytes-width,width,last+1);
            if(equal_products(width,n,3,1,0,terms,arena,bytes,base,terms*4,result,terms*4))
                fail("last product coordinate mismatch accepted");
            write_le(arena+bytes-width,width,last);
            if(equal_products(width,n,3,1,0,terms+1,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,n,3,1,UINT64_MAX,0,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,n,UINT64_MAX,1,0,terms,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,n,3,3,0,terms,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(3,n,3,1,0,terms,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,0,3,1,0,0,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,4097,3,1,0,0,arena,bytes,base,terms*4,result,terms*4) ||
               equal_products(width,n,3,1,0,terms,arena,bytes-1,base,terms*4,result,terms*4) ||
               equal_products(width,n,3,1,0,terms,arena,bytes,base,terms*4,result,terms*4-1))
                fail("malformed cached product accepted");
            write_le(base+4*(terms-1),4,3);
            if(equal_products(width,n,3,1,0,terms,arena,bytes,base,terms*4,result,terms*4))
                fail("invalid cached base identifier accepted");
            free(arena);free(base);free(result);
        }
    }
    /* A nonzero slice must inspect its last term, whose ID is valid but whose
       exponent sum is wrong. Checking only the first term or ignoring start fails. */
    uint8_t arena[]={0,1,2,3},base[12],result[12];
    for(size_t i=0;i<3;++i) {write_le(base+4*i,4,i);write_le(result+4*i,4,i<2?i+1:2);}
    if(!equal_products(1,1,4,1,0,2,arena,4,base,12,result,12) ||
       equal_products(1,1,4,1,1,2,arena,4,base,12,result,12) ||
       equal_products(1,1,4,1,2,1,arena,4,base,12,result,12))
        fail("late in-range product mismatch or nonzero start");
    puts("cached products: all widths, coordinate bounds, aliases and malformed arenas passed");
}

static void check_inspect(void) {
    unsigned cases=0;
    for(unsigned w=1;w<=4;w*=2) {
        uint64_t bound=UINT64_C(1)<<(w*8);
        for(unsigned trial=0;trial<300;++trial) {
            size_t n=trial==299?4096:trial%129+1,bytes=2*n*w;
            uint8_t *arena=malloc(bytes),*saved=malloc(bytes);
            uint64_t *a=malloc(n*sizeof(uint64_t)),*b=malloc(n*sizeof(uint64_t));
            if(!arena || !saved || !a || !b) fail("comparison allocation");
            for(size_t i=0;i<n;++i) {
                a[i]=random_word()%bound;
                b[i]=trial%3==0?a[i]:trial%3==1?a[i]/2:random_word()%bound;
            }
            if(trial%3==0) b[trial%n]=(a[trial%n]+1)%bound;
            for(size_t i=0;i<n;++i) {write_le(arena+i*w,w,a[i]);write_le(arena+(n+i)*w,w,b[i]);}
            memcpy(saved,arena,bytes);
            for(unsigned op=0;op<3;++op) {
                uint8_t expected=1;
                for(size_t k=0;k<n;++k) {
                    size_t i=op==1?n-1-k:k;
                    if(op==2) {if(a[i]>b[i]) {expected=0;break;}}
                    else if(a[i]!=b[i]) {expected=op==1?(b[i]<a[i]?0:2):(a[i]<b[i]?0:2);break;}
                }
                if(inspect_monomials(op,w,n,0,1,arena,bytes)!=expected) fail("different packed comparison");
                /* A partial unused third row is outside both read spans. */
                if(w*n>1 && inspect_monomials(op,w,n-1,0,0,arena,bytes)!=1) fail("unused partial row");
                if(inspect_monomials(op,w,n,0,0,arena,bytes)!=1) fail("equal packed comparison");
                if(inspect_monomials(op,w,n,0,1,arena,bytes-1)!=3) fail("truncated comparison rows");
                if(inspect_monomials(op,w,n,0,2,arena,bytes)!=3) fail("comparison row bound");
                ++cases;
            }
            if(memcmp(saved,arena,bytes)) fail("borrowed comparison mutated");
            free(arena);free(saved);free(a);free(b);
        }
        if(inspect_monomials(0,w,0,0,0,NULL,0)!=1) fail("zero arity comparison");
        if(inspect_monomials(2,w,4097,0,0,NULL,0)!=3 ||
           inspect_monomials(2,w,UINT64_MAX,0,0,NULL,0)!=3 ||
           inspect_monomials(2,w,1,UINT64_MAX,0,NULL,0)!=3) fail("comparison integer boundary");
    }
    if(inspect_monomials(3,1,0,0,0,NULL,0)!=3 ||
       inspect_monomials(0,3,0,0,0,NULL,0)!=3) fail("comparison opcode/width");
    printf("packed monomial comparisons: %u array-oracle cases and malformed boundaries OK\n",cases);
}

static void check_inspect_pages(void) {
#if defined(__linux__)
    long page_value=sysconf(_SC_PAGESIZE);
    if(page_value<=0) fail("comparison page size");
    size_t page=(size_t)page_value,counts[]={1,7,4096};
    for(unsigned w=1;w<=4;w*=2) for(unsigned k=0;k<3;++k) for(unsigned end=0;end<2;++end) {
        size_t n=counts[k],bytes=2*n*w,pages=(bytes+page-1)/page,total=(pages+2)*page;
        uint8_t *mapping=mmap(NULL,total,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
        if(mapping==MAP_FAILED || mprotect(mapping+page,pages*page,PROT_READ|PROT_WRITE)) fail("comparison guard mapping");
        uint8_t *arena=end?mapping+(pages+1)*page-bytes:mapping+page;
        for(size_t i=0;i<n;++i) {write_le(arena+i*w,w,i%17);write_le(arena+(n+i)*w,w,i%17+(i==n-1));}
        if(mprotect(mapping+page,pages*page,PROT_READ)) fail("comparison read-only mapping");
        if(inspect_monomials(0,w,n,0,1,arena,bytes)!=0 ||
           inspect_monomials(1,w,n,0,1,arena,bytes)!=2 ||
           inspect_monomials(2,w,n,0,1,arena,bytes)!=1) fail("comparison guarded result");
        if(inspect_monomials(2,w,n,0,2,arena,bytes)!=3 ||
           inspect_monomials(0,w,n,0,1,arena,bytes-1)!=3) fail("comparison guarded rejection");
        if(munmap(mapping,total)) fail("comparison guard unmap");
    }
#endif
}

int main(void) {
    check_inspect();
    check_inspect_pages();
    check_bytes();
    check_products();
    check_arithmetic();
    check_monomials();
    const uint64_t moduli[] = {2, 3, 251, 256, 257, 65521, 65536, 65537, 2147483647};
    unsigned cases = 0;
    for (unsigned field = 0; field < sizeof(moduli) / sizeof(moduli[0]); ++field) {
        uint64_t p = moduli[field];
        unsigned width = p <= 256 ? 1 : p <= 65536 ? 2 : 4;
        size_t bytes = 37 * width;
        uint8_t *dense = malloc(bytes), *expected = malloc(bytes);
        uint8_t *columns = malloc(64 * 4), *coefficients = malloc(64 * width);
        if (!dense || !expected || !columns || !coefficients) fail("allocation");
        for (unsigned trial = 0; trial < 500; ++trial) {
            for (size_t i = 0; i < 37; ++i) write_le(dense + i * width, width, random_word() % p);
            memcpy(expected, dense, bytes);
            for (size_t i = 0; i < 64; ++i) {
                write_le(columns + 4 * i, 4, random_word() % 37);
                write_le(coefficients + width * i, width, random_word() % p);
            }
            size_t start = random_word() % 65;
            size_t count = random_word() % (65 - start);
            uint64_t factor = trial % 2 ? p - 1 : random_word() % p;
            unsigned checked = row_shape(p, bytes, 64 * 4, 64 * width, start, count, factor);
            if (checked != width) fail("geometry rejected");
            for (size_t i = start; i < start + count; ++i) {
                size_t column = (size_t)read_le(columns + 4 * i, 4);
                uint64_t a = read_le(expected + column * width, width);
                uint64_t b = read_le(coefficients + i * width, width);
                uint64_t value = (a + p - factor * b % p) % p;
                write_le(expected + column * width, width, value);
            }
            if (!update_bytes(p, width, dense, bytes, columns, coefficients, start, count, factor))
                fail("valid update rejected");
            if (memcmp(expected, dense, bytes)) fail("different modular result");
            ++cases;
        }
        free(dense); free(expected); free(columns); free(coefficients);
    }
    if (row_shape(7, 1, 4, 1, SIZE_MAX, 1, 1)) fail("start overflow accepted");
    if (row_shape(7, 1, 4, 1, 0, SIZE_MAX, 1)) fail("count overflow accepted");
    if (row_shape(7, 1, 5, 1, 0, 1, 1)) fail("misaligned columns accepted");
    if (row_shape(257, 1, 4, 2, 0, 1, 1)) fail("misaligned dense accepted");
    if (row_shape(7, 1, 4, 2, 0, 1, 1)) fail("coefficient length accepted");
    if (row_shape(0, 1, 4, 1, 0, 1, 1)) fail("zero modulus accepted");
    if (row_shape(2147483648, 4, 4, 4, 0, 1, 1)) fail("wide modulus accepted");
    if (row_shape(7, 1, 4, 1, 0, 1, 7)) fail("noncanonical factor accepted");
    uint8_t dense[] = {1}, bad_columns[] = {255,255,255,255}, coefficients[] = {1};
    if (update_bytes(7, 1, dense, 1, bad_columns, coefficients, 0, 1, 1)) fail("bad column accepted");
    uint8_t columns[] = {0,0,0,0};
    coefficients[0] = 7;
    if (update_bytes(7, 1, dense, 1, columns, coefficients, 0, 1, 1)) fail("bad coefficient accepted");
    coefficients[0] = 1; dense[0] = 7;
    if (update_bytes(7, 1, dense, 1, columns, coefficients, 0, 1, 1)) fail("bad dense value accepted");
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    printf("row_update_selftest: uint128 Barrett, %u cases and malformed boundaries OK\n", cases);
#else
    printf("row_update_selftest: exact remainder, %u cases and malformed boundaries OK\n", cases);
#endif
    return 0;
}
