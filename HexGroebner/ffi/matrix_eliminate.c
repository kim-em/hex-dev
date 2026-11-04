/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "matrix_runtime.h"

#ifndef HEX_GROEBNER_MATRIX_ACCEPTED
#define HEX_GROEBNER_MATRIX_ACCEPTED() ((void)0)
#endif
#ifndef HEX_GROEBNER_MATRIX_DEFERRED
#define HEX_GROEBNER_MATRIX_DEFERRED() ((void)0)
#endif

#define MATRIX_QUANTUM UINT64_C(1048576)
#define BINARY_LOGICAL_QUANTUM (UINT64_C(1)<<32)
#define BINARY_WORD_QUANTUM (UINT64_C(1)<<28)
#ifndef HEX_GROEBNER_BINARY_TABLE_USED
#define HEX_GROEBNER_BINARY_TABLE_USED() ((void)0)
#endif
#ifndef HEX_GROEBNER_BINARY_PROJECT_USED
#define HEX_GROEBNER_BINARY_PROJECT_USED() ((void)0)
#endif
#ifndef HEX_GROEBNER_BINARY_SCAN_USED
#define HEX_GROEBNER_BINARY_SCAN_USED() ((void)0)
#endif
#ifndef HEX_GROEBNER_BINARY_PIVOTS_USED
#define HEX_GROEBNER_BINARY_PIVOTS_USED(bytes) ((void)(bytes))
#endif
#ifndef HEX_GROEBNER_BINARY_SPARSE_USED
#define HEX_GROEBNER_BINARY_SPARSE_USED() ((void)0)
#endif
#ifndef HEX_GROEBNER_BINARY_WORD_USED
#define HEX_GROEBNER_BINARY_WORD_USED(id) ((void)(id))
#endif

typedef struct {
    uint64_t limits[7],stats[8],p,columns,quantum,scratch,words,capacity;
    unsigned width;
    uint8_t cache,binary,project;
    lean_object *dense,*slots,*pivots,*native_pivots,*remainders,*binary_rows,*binary_meta,*project_rows,*project_meta,*project_table;
    uint64_t rank;
} matrix_context;

static uint64_t matrix_read(const uint8_t *p,unsigned w) {
    uint64_t x=p[0];
    if(w>1) x|=(uint64_t)p[1]<<8;
    if(w>2) x|=(uint64_t)p[2]<<16 | (uint64_t)p[3]<<24;
    return x;
}
static void matrix_write(uint8_t *p,unsigned w,uint64_t x) {
    p[0]=(uint8_t)x;
    if(w>1) p[1]=(uint8_t)(x>>8);
    if(w>2) {p[2]=(uint8_t)(x>>16);p[3]=(uint8_t)(x>>24);}
}
static int matrix_charge(uint64_t *count,uint64_t amount,uint64_t limit) {
    if(*count>limit || amount>limit-*count) return 0;
    *count+=amount;return 1;
}
static int matrix_work(matrix_context *c,uint64_t n) {
    uint64_t cap=c->limits[5]<c->quantum?c->limits[5]:c->quantum;
    return matrix_charge(&c->stats[0],n,cap);
}
static int matrix_bytes(matrix_context *c,uint64_t n) {
    return matrix_charge(&c->stats[3],n,c->limits[4]-c->scratch);
}
static lean_object *matrix_empty(void) {
    return lean_mk_empty_array_with_capacity(lean_box(0));
}
static lean_object *matrix_zeros(size_t n) {
    lean_object *a=lean_alloc_sarray(1,n,n);
    memset(lean_sarray_cptr(a),0,n);return a;
}
static lean_object *matrix_take(b_lean_obj_arg o,unsigned field) {
    lean_object *x=lean_ctor_get(o,field);lean_inc(x);return x;
}
static lean_object *matrix_row(lean_obj_arg columns,lean_obj_arg coefficients) {
    lean_object *row=lean_alloc_ctor(0,2,0);
    lean_ctor_set(row,0,columns);lean_ctor_set(row,1,coefficients);return row;
}
static int matrix_inverse(matrix_context *c,uint64_t a,uint64_t *inverse) {
    if(a==1) {*inverse=1;return 1;}
    uint64_t exponent=c->p-2,value=1;
    while(exponent) {
        if(exponent&1) {
            if(!matrix_work(c,1)) return 0;
            value=(value*a)%c->p;
        }
        exponent>>=1;
        if(exponent) {
            if(!matrix_work(c,1)) return 0;
            a=(a*a)%c->p;
        }
    }
    *inverse=value;return 1;
}
static void matrix_cleanup(matrix_context *c) {
    if(c->project_table) lean_dec(c->project_table);
    if(c->project_meta) lean_dec(c->project_meta);
    if(c->project_rows) lean_dec(c->project_rows);
    if(c->binary_meta) lean_dec(c->binary_meta);
    if(c->binary_rows) lean_dec(c->binary_rows);
    if(c->dense) lean_dec(c->dense);
    if(c->slots) lean_dec(c->slots);
    if(c->pivots) lean_dec(c->pivots);
    if(c->native_pivots) lean_dec(c->native_pivots);
    if(c->remainders) lean_dec(c->remainders);
}
/* Installed rows are already canonical and monic. Thus the optional factory's
   exact acceptance and charges are known without allocating an unused cache.
   Parent-budget refusal costs zero, as in Matrix.preparePivot. A work-cap
   decline occurs only when the same reference charge exceeds MATRIX_QUANTUM. */
static int matrix_prepare(matrix_context *c,b_lean_obj_arg row) {
    if(!c->cache) return 1;
    uint64_t n=lean_sarray_size(lean_ctor_get(row,0))/4;
    if(n<128 || n>4096) return 1;
    const uint8_t *ids=lean_sarray_cptr(lean_ctor_get(row,0));
    uint64_t span=matrix_read(ids+(size_t)(n-1)*4,4)-matrix_read(ids,4)+1;
    if(n>=span || 3*span>4*n) return 1;
    uint64_t bytes=4*span,work=bytes+3*n+span+2;
    if(work>c->limits[5]-c->stats[0] || bytes>c->limits[4]-c->stats[3]) return 1;
    return matrix_work(c,work) && matrix_bytes(c,bytes);
}
static int matrix_install(matrix_context *c,lean_obj_arg row,uint64_t column,
        uint64_t inverse,uint64_t sugar,uint8_t from_target) {
    if(column>=c->columns || !matrix_prepare(c,row)) {lean_dec(row);return 0;}
    size_t id=lean_array_size(c->pivots);
    if(c->binary) {
        if(id>=c->capacity) {lean_dec(row);return 0;}
        uint8_t *packed=lean_sarray_cptr(c->binary_rows)+(size_t)id*c->words*8;
        lean_object *ids=lean_ctor_get(row,0);
        size_t n=lean_sarray_size(ids)/4;
        if(!n || n>c->columns) {lean_dec(row);return 0;}
        for(size_t i=0;i<n;++i) {
            uint64_t col=matrix_read(lean_sarray_cptr(ids)+4*i,4);
            packed[col>>3]|=(uint8_t)(1u<<(col&7));
        }
        /* Private little-endian (entry count, final column, sugar) records.
           Canonical nonempty rows have at most columns <= 16384 entries. */
        uint8_t *meta=lean_sarray_cptr(c->binary_meta)+id*16;
        matrix_write(meta,4,n);
        matrix_write(meta+4,4,matrix_read(lean_sarray_cptr(ids)+(n-1)*4,4));
        for(unsigned b=0;b<8;++b) meta[8+b]=(uint8_t)(sugar>>(8*b));
    }
    lean_object *native=lean_alloc_ctor(0,3,0);
    lean_ctor_set(native,0,matrix_take(row,0));
    lean_ctor_set(native,1,matrix_take(row,1));
    lean_ctor_set(native,2,lean_uint64_to_nat(sugar));
    c->native_pivots=lean_array_push(c->native_pivots,native);
    lean_object *pivot=lean_alloc_ctor(0,3,9);
    lean_ctor_set(pivot,0,row);lean_ctor_set(pivot,1,lean_box(0));
    lean_ctor_set(pivot,2,lean_uint64_to_nat(sugar));
    lean_ctor_set_uint64(pivot,3*sizeof(void*),inverse);
    lean_ctor_set_uint8(pivot,3*sizeof(void*)+8,from_target);
    c->pivots=lean_array_push(c->pivots,pivot);
    matrix_write(lean_sarray_cptr(c->slots)+(size_t)column*4,4,id+1);
    if(!from_target) ++c->rank;
    return 1;
}
static void matrix_remainder(matrix_context *c,lean_obj_arg row,uint64_t sugar) {
    lean_object *out=lean_alloc_ctor(0,3,0);
    lean_ctor_set(out,0,row);lean_ctor_set(out,1,lean_box(0));
    lean_ctor_set(out,2,lean_uint64_to_nat(sugar));
    c->remainders=lean_array_push(c->remainders,out);
}

/* F2 rows and the accumulator live in a private bit matrix. The complete
   scratch payload is admitted against the parent's packed-byte allowance. No bit
   buffer escapes the frame; logical charges retain the sparse reference model.
   memcpy word loads/stores avoid alignment and effective-type assumptions. */
static uint8_t *matrix_binary_dense(matrix_context *c) {
    return lean_sarray_cptr(c->binary_rows)+(size_t)c->capacity*c->words*8;
}
/* The bitmap has a little-endian byte layout on every host. Compilers fold
   this fixed-width decode into an unaligned load (and a swap if necessary). */
static uint64_t matrix_binary_load(const uint8_t *p) {
    return (uint64_t)p[0] | (uint64_t)p[1]<<8 | (uint64_t)p[2]<<16 |
        (uint64_t)p[3]<<24 | (uint64_t)p[4]<<32 | (uint64_t)p[5]<<40 |
        (uint64_t)p[6]<<48 | (uint64_t)p[7]<<56;
}
static unsigned matrix_binary_ctz(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
    return (unsigned)__builtin_ctzll(x);
#else
    unsigned n=0;while(!(x&1)) {x>>=1;++n;}return n;
#endif
}
static unsigned matrix_binary_popcount(uint64_t x) {
    x-=((x>>1)&UINT64_C(0x5555555555555555));
    x=(x&UINT64_C(0x3333333333333333))+((x>>2)&UINT64_C(0x3333333333333333));
    x=(x+(x>>4))&UINT64_C(0x0f0f0f0f0f0f0f0f);
    return (unsigned)((x*UINT64_C(0x0101010101010101))>>56);
}
static uint64_t matrix_binary_interval(const uint8_t *data,uint64_t word,
        uint64_t first,uint64_t last) {
    uint64_t bits=matrix_binary_load(data+(size_t)word*8);
    if(word==(first>>6)) bits&=UINT64_MAX<<(first&63);
    if(word==(last>>6) && (last&63)!=63)
        bits&=(UINT64_C(1)<<((last&63)+1))-1;
    return bits;
}
static void matrix_binary_xor(uint8_t *restrict data,const uint8_t *restrict row,
        uint64_t first,uint64_t last) {
    for(uint64_t i=first;i<=last;++i) {
        uint64_t a,b;
        memcpy(&a,data+(size_t)i*8,8);memcpy(&b,row+(size_t)i*8,8);
        a^=b;memcpy(data+(size_t)i*8,&a,8);
    }
}
/* Four consecutive dense known reducers admit a 16-row XOR table. The
   incoming head pattern is triangular, not necessarily the identity: simulate
   those four pivot decisions before choosing a combination. Cost, support end
   and sugar summarize every selected source, including cancelled tails. */
static int matrix_project_table(matrix_context *c,uint64_t first,uint64_t nt,
        uint64_t *through) {
    uint64_t heads[4],ids[4],sizes[4],ends[4],labels[4],found=0;
    for(uint64_t col=first;col<c->columns && found<4;++col) {
        uint64_t slot=matrix_read(lean_sarray_cptr(c->slots)+col*4,4);
        if(!slot) continue;
        const uint8_t *meta=lean_sarray_cptr(c->binary_meta)+(slot-1)*16;
        uint64_t n=matrix_read(meta,4),end=matrix_read(meta+4,4);
        if(n<=(end>>6)-(col>>6)+1) return 0;
        heads[found]=col;ids[found]=slot-1;sizes[found]=n;ends[found]=end;
        labels[found]=matrix_binary_load(meta+8);++found;
    }
    if(found!=4) return 0;
    uint8_t pattern[4]={0},selection[16]={0};
    for(unsigned k=0;k<4;++k) {
        const uint8_t *row=lean_sarray_cptr(c->binary_rows)+(size_t)ids[k]*c->words*8;
        for(unsigned j=0;j<4;++j)
            if(row[heads[j]>>3]&(1u<<(heads[j]&7))) pattern[k]|=(uint8_t)(1u<<j);
    }
    for(unsigned mask=0;mask<16;++mask) {
        unsigned bits=mask,selected=0;
        for(unsigned k=0;k<4;++k) if(bits&(1u<<k)) {
            selected|=1u<<k;bits^=pattern[k];
        }
        selection[mask]=(uint8_t)selected;
    }
    uint64_t cost[16]={0},last[16]={0},sugar[16]={0},count[16]={0};
    uint8_t *table=lean_sarray_cptr(c->project_table);
    memset(table,0,(size_t)c->words*8);
    for(unsigned mask=1;mask<16;++mask) {
        unsigned k=matrix_binary_ctz(mask),prev=mask&(mask-1);
        const uint8_t *row=lean_sarray_cptr(c->binary_rows)+(size_t)ids[k]*c->words*8;
        const uint8_t *before=table+(size_t)prev*c->words*8;
        uint8_t *out=table+(size_t)mask*c->words*8;
        HEX_GROEBNER_BINARY_WORD_USED(ids[k]);
        for(uint64_t w=0;w<c->words;++w) {
            uint64_t a,b;memcpy(&a,before+w*8,8);memcpy(&b,row+w*8,8);
            a^=b;memcpy(out+w*8,&a,8);
        }
        cost[mask]=cost[prev]+sizes[k];count[mask]=count[prev]+1;
        last[mask]=last[prev]>ends[k]?last[prev]:ends[k];
        sugar[mask]=sugar[prev]>labels[k]?sugar[prev]:labels[k];
    }
    for(uint64_t t=0;t<nt;++t) {
        uint8_t *data=lean_sarray_cptr(c->project_rows)+(size_t)t*c->words*8;
        unsigned bits=0;
        for(unsigned k=0;k<4;++k)
            if(data[heads[k]>>3]&(1u<<(heads[k]&7))) bits|=1u<<k;
        unsigned mask=selection[bits];
        if(!mask) continue;
        HEX_GROEBNER_BINARY_TABLE_USED();
        if(!matrix_work(c,cost[mask])) return -1;
        matrix_binary_xor(data,table+(size_t)mask*c->words*8,first>>6,last[mask]>>6);
        uint8_t *meta=lean_sarray_cptr(c->project_meta)+t*16;
        uint64_t end=matrix_binary_load(meta),label=matrix_binary_load(meta+8);
        if(last[mask]>end) end=last[mask];
        if(sugar[mask]>label) label=sugar[mask];
        for(unsigned b=0;b<8;++b) {meta[b]=(uint8_t)(end>>(8*b));meta[8+b]=(uint8_t)(label>>(8*b));}
        c->stats[6]+=count[mask];
    }
    *through=heads[3];return 1;
}
/* Each target pivot has zero coefficients at every known leading column.
   Projecting through all known reducers first therefore preserves both the
   later target-pivot factors and the exact sparse reference row. Last/sugar
   retain maxima over the original support and every used reducer, even when
   combined tails cancel. Partial attempts never expose reordered charges. */
static int matrix_project_binary(matrix_context *c,lean_obj_arg targets,
        lean_obj_arg sugars,uint64_t nr,uint64_t nt,uint64_t ns) {
    HEX_GROEBNER_BINARY_PROJECT_USED();
    uint8_t *rows=lean_sarray_cptr(c->project_rows);
    uint8_t *labels=lean_sarray_cptr(c->project_meta);
    for(uint64_t t=0;t<nt;++t) {
        lean_object *row=lean_array_cptr(targets)[t];
        lean_object *cs=lean_ctor_get(row,0);
        uint64_t n=lean_sarray_size(cs)/4;
        if(!matrix_work(c,n)) return 0;
        uint8_t *data=rows+(size_t)t*c->words*8;
        for(uint64_t j=0;j<n;++j) {
            uint64_t col=matrix_read(lean_sarray_cptr(cs)+j*4,4);
            data[col>>3]|=(uint8_t)(1u<<(col&7));
        }
        uint64_t last=n?matrix_read(lean_sarray_cptr(cs)+(n-1)*4,4):0;
        uint64_t sugar=ns?lean_unbox(lean_array_cptr(sugars)[nr+t]):0;
        for(unsigned b=0;b<8;++b) {
            labels[t*16+b]=(uint8_t)(last>>(8*b));
            labels[t*16+8+b]=(uint8_t)(sugar>>(8*b));
        }
    }
    for(uint64_t col=0;col<c->columns;++col) {
        uint64_t slot=matrix_read(lean_sarray_cptr(c->slots)+col*4,4);
        if(!slot) continue;
        uint64_t through=col;
        int grouped=matrix_project_table(c,col,nt,&through);
        if(grouped<0) return 0;
        if(grouped) {col=through;continue;}
        const uint8_t *meta=lean_sarray_cptr(c->binary_meta)+(slot-1)*16;
        uint64_t n=matrix_read(meta,4),end=matrix_read(meta+4,4);
        uint64_t sugar=matrix_binary_load(meta+8);
        const uint8_t *packed=lean_sarray_cptr(c->binary_rows)+(size_t)(slot-1)*c->words*8;
        uint64_t span=(end>>6)-(col>>6)+1;
        for(uint64_t t=0;t<nt;++t) {
            uint8_t *data=rows+(size_t)t*c->words*8;
            if(!(data[col>>3]&(1u<<(col&7)))) continue;
            if(!matrix_work(c,n)) return 0;
            if(n<=span) {
                HEX_GROEBNER_BINARY_SPARSE_USED();
                lean_object *pivot=lean_array_cptr(c->native_pivots)[slot-1];
                const uint8_t *ids=lean_sarray_cptr(lean_ctor_get(pivot,0));
                for(uint64_t j=0;j<n;++j) {
                    uint64_t k=matrix_read(ids+j*4,4);
                    data[k>>3]^=(uint8_t)(1u<<(k&7));
                }
            } else {
                HEX_GROEBNER_BINARY_WORD_USED(slot-1);
                matrix_binary_xor(data,packed,col>>6,end>>6);
            }
            uint64_t last=matrix_binary_load(labels+t*16);
            uint64_t label=matrix_binary_load(labels+t*16+8);
            if(end>last) last=end;
            if(sugar>label) label=sugar;
            for(unsigned b=0;b<8;++b) {
                labels[t*16+b]=(uint8_t)(last>>(8*b));
                labels[t*16+8+b]=(uint8_t)(label>>(8*b));
            }
            ++c->stats[6];
        }
    }
    return 1;
}
static int matrix_scan_binary(matrix_context *c,uint64_t first,uint64_t *last,
        uint64_t *leading,uint64_t *sugar) {
    HEX_GROEBNER_BINARY_SCAN_USED();
    uint8_t *data=matrix_binary_dense(c);
    uint64_t charged=first;
    uint64_t col=first;
    while(col<c->columns && col<=*last) {
        if(col>=charged) {
            uint64_t stop=col+64<*last+1?col+64:*last+1;
            if(!matrix_work(c,stop-col)) return 0;
            charged=stop;
            int zero=1;
            for(uint64_t word=col>>6;word<=((stop-1)>>6);++word)
                if(matrix_binary_interval(data,word,col,stop-1)) {zero=0;break;}
            if(zero) {col=stop;continue;}
        }
        if(!(data[col>>3]&(1u<<(col&7)))) {++col;continue;}
        uint64_t slot=matrix_read(lean_sarray_cptr(c->slots)+col*4,4);
        if(!slot) {if(!*leading) *leading=col+1;++col;continue;}
        const uint8_t *meta=lean_sarray_cptr(c->binary_meta)+(slot-1)*16;
        uint64_t n=matrix_read(meta,4),end=matrix_read(meta+4,4);
        if(end>*last) *last=end;
        uint64_t label=matrix_binary_load(meta+8);
        if(label>*sugar) *sugar=label;
        if(!matrix_work(c,n)) return 0;
        uint64_t span=(end>>6)-(col>>6)+1;
        if(n<=span) {
            HEX_GROEBNER_BINARY_SPARSE_USED();
            lean_object *pivot=lean_array_cptr(c->native_pivots)[slot-1];
            const uint8_t *ids=lean_sarray_cptr(lean_ctor_get(pivot,0));
            for(uint64_t i=0;i<n;++i) {
                uint64_t j=matrix_read(ids+i*4,4);
                data[j>>3]^=(uint8_t)(1u<<(j&7));
            }
        } else {
            HEX_GROEBNER_BINARY_WORD_USED(slot-1);
            const uint8_t *packed=lean_sarray_cptr(c->binary_rows)+(size_t)(slot-1)*c->words*8;
            matrix_binary_xor(data,packed,col>>6,end>>6);
        }
        ++c->stats[6];
        ++col;
    }
    return 1;
}
static lean_object *matrix_gather_binary(matrix_context *c,uint64_t first,uint64_t last) {
    if(!matrix_work(c,last+1-first)) return NULL;
    uint8_t *data=matrix_binary_dense(c);uint64_t n=0;
    for(uint64_t word=first>>6;word<=last>>6;++word)
        n+=matrix_binary_popcount(matrix_binary_interval(data,word,first,last));
    /* Only complete successful frames expose counters. Aggregate admission
       has the same success condition and totals as per-entry reference charges. */
    if(!matrix_charge(&c->stats[2],n,c->limits[3]) || !matrix_bytes(c,5*n)) return NULL;
    lean_object *ids=lean_alloc_sarray(1,(size_t)(4*n),(size_t)(4*n));
    lean_object *coeff=lean_alloc_sarray(1,(size_t)n,(size_t)n);
    uint64_t index=0;
    for(uint64_t word=first>>6;word<=last>>6;++word) {
        uint64_t bits=matrix_binary_interval(data,word,first,last);
        while(bits) {
            uint64_t j=word*64+matrix_binary_ctz(bits);
            matrix_write(lean_sarray_cptr(ids)+4*index,4,j);
            lean_sarray_cptr(coeff)[index++]=1;
            bits&=bits-1;
        }
    }
    /* Earlier columns have been eliminated, and later ones were never set. */
    memset(data,0,(size_t)c->words*8);
    return matrix_row(ids,coeff);
}

/* The accumulator moves into each existing bounded scan call. Borrowed input
   rows and pivot buffers remain immutable. Only the returned owned accumulator
   is recovered; intermediate result/state headers are released immediately. */
static int matrix_scan(matrix_context *c,uint64_t first,uint64_t *last,
        uint64_t *leading,uint64_t *sugar) {
    if(c->binary) return matrix_scan_binary(c,first,last,leading,sugar);
    lean_object *state=lean_alloc_ctor(0,8,8);
    lean_ctor_set(state,0,c->dense);c->dense=NULL;
    lean_ctor_set(state,1,lean_uint64_to_nat(first));
    lean_ctor_set(state,2,lean_uint64_to_nat(*last));
    lean_ctor_set(state,3,lean_uint64_to_nat(first));
    for(unsigned i=4;i<7;++i) lean_ctor_set(state,i,lean_box(0));
    lean_ctor_set(state,7,lean_uint64_to_nat(*sugar));
    lean_ctor_set_uint64(state,8*sizeof(void*),0);
    uint64_t cap=c->limits[5]<c->quantum?c->limits[5]:c->quantum;
    uint64_t calls=(c->columns*(c->columns+2)+4095)/4096+1;
    for(uint64_t call=0;call<calls;++call) {
        lean_object *remaining=lean_uint64_to_nat(cap-c->stats[0]);
        lean_object *out=lean_hex_scan_transition(c->p,c->slots,c->native_pivots,
            state,lean_box(4096),remaining,lean_box(0),0);
        state=NULL;lean_dec(remaining);
        uint8_t status=lean_ctor_get_uint8(out,5*sizeof(void*));
        uint64_t work=lean_unbox(lean_ctor_get(out,2));
        uint64_t reductions=lean_unbox(lean_ctor_get(out,3));
        if(!matrix_work(c,work)) {lean_dec(out);return 0;}
        c->stats[6]+=reductions;
        if(status==1) {
            lean_object *next=lean_ctor_get(out,0);
            c->dense=matrix_take(next,0);
            *last=lean_unbox(lean_ctor_get(next,2));
            *leading=lean_unbox(lean_ctor_get(next,4));
            *sugar=lean_unbox(lean_ctor_get(next,7));
            lean_dec(out);return 1;
        }
        if(status!=0) {lean_dec(out);return 0;}
        state=matrix_take(out,0);lean_dec(out);
    }
    lean_dec(state);return 0;
}
static lean_object *matrix_gather(matrix_context *c,uint64_t column,uint64_t last,
        uint64_t inverse) {
    if(c->binary) return matrix_gather_binary(c,column,last);
    if(!matrix_work(c,last+1-column)) return NULL;
    lean_object *state=lean_alloc_ctor(0,4,0);
    lean_ctor_set(state,0,c->dense);c->dense=NULL;
    lean_ctor_set(state,1,matrix_zeros(0));lean_ctor_set(state,2,matrix_zeros(0));
    lean_ctor_set(state,3,lean_uint64_to_nat(column));
    uint64_t cap=c->limits[5]<c->quantum?c->limits[5]:c->quantum;
    uint64_t calls=(last+1-column+4095)/4096+1;
    for(uint64_t call=0;call<calls;++call) {
        lean_object *stop=lean_uint64_to_nat(last+1);
        lean_object *entries=lean_uint64_to_nat(c->limits[3]-c->stats[2]);
        lean_object *bytes=lean_uint64_to_nat(c->limits[4]-c->stats[3]);
        lean_object *work=lean_uint64_to_nat(cap-c->stats[0]);
        lean_object *out=lean_hex_gather(c->p,state,stop,lean_box(4096),entries,bytes,work,inverse);
        state=NULL;lean_dec(stop);lean_dec(entries);lean_dec(bytes);lean_dec(work);
        uint8_t status=lean_ctor_get_uint8(out,4*sizeof(void*));
        if(!matrix_charge(&c->stats[2],lean_unbox(lean_ctor_get(out,1)),c->limits[3]) ||
           !matrix_bytes(c,lean_unbox(lean_ctor_get(out,2))) ||
           !matrix_work(c,lean_unbox(lean_ctor_get(out,3)))) {lean_dec(out);return NULL;}
        if(status==1) {
            lean_object *next=lean_ctor_get(out,0);
            c->dense=matrix_take(next,0);
            lean_object *row=matrix_row(matrix_take(next,1),matrix_take(next,2));
            lean_dec(out);return row;
        }
        if(status!=0) {lean_dec(out);return NULL;}
        state=matrix_take(out,0);lean_dec(out);
    }
    lean_dec(state);return NULL;
}

/* ABI: PrimeField is its unboxed uint64 modulus (prime 2 <= p < 2^31).
   All five object arguments are borrowed: MatrixLimits has seven Nat fields and dense/binary Bool bytes,
   columns is Nat, rows are Lean Arrays of SparseRow(two ByteArrays), sugars is
   Array Nat. independent is uint8 Bool. Limits above Nat's scalar range saturate
   above every possible accepted total; sugars must be scalar Nats.
   Ordinary 64-bit frames admit <=4096 columns/1024 reducers/64 targets.
   Opt-in F2 frames admit <=16384/16384/1024, with <=2^32 logical work,
   <=2^28 packing/scalar/word visits, and the complete private payload reserved
   against the parent peak. Distinct reducer leading columns and work bounds are
   checked before allocation; canonical row validation precedes elimination.
   Dense workspace is owned; inputs, including overlapping arrays, are immutable.
   Some(Result(Except.ok(Prod(Echelon(rows,rank,emptyTrace),remainders)),stats))
   contains exact reference rows and eight Nat counters, using the layouts in
   EliminationKernel.lean. None releases all local owners and permits bounded
   continuation outside this frame. Charged speculative work before a decline is bounded
   by min(parent remaining work,frame quantum); F2 packing/word work also has
   its explicit shape bound. With optional preparation, the reference
   may succeed above the frame quantum. A declined prefix then costs less than
   its own reference computation; this per-frame overhead can recur on multiple
   matrices. Without dense preparation or private F2 payload, the shape bound
   makes a charged decline imply reference failure. Private-payload admission
   can decline an otherwise successful reference.
   Scan/gather symbols come from HexGroebnerMatrixNative. Lake links its complete
   imported shared library; keep that carrier dependency and these ABIs intact. */
LEAN_EXPORT lean_obj_res lean_hex_groebner_eliminate_matrix(uint64_t p,
        b_lean_obj_arg limits,b_lean_obj_arg column_arg,b_lean_obj_arg reducers,
        b_lean_obj_arg targets,b_lean_obj_arg sugars,uint8_t independent) {
    matrix_context c={0};
    if(sizeof(void*)!=8 || p<2 || p>=UINT64_C(2147483648) ||
       !lean_is_scalar(column_arg)) goto defer;
    c.p=p;c.width=p<=256?1:p<=65536?2:4;c.columns=lean_unbox(column_arg);
    c.binary=p==2 && lean_ctor_get_uint8(limits,7*sizeof(void*)+1);
    c.quantum=c.binary?BINARY_LOGICAL_QUANTUM:MATRIX_QUANTUM;
    c.cache=p==INT32_MAX && lean_ctor_get_uint8(limits,7*sizeof(void*));
    size_t nr=lean_array_size(reducers),nt=lean_array_size(targets);
    if(c.columns>(c.binary?16384:4096) || nr>(c.binary?16384:1024) || nt>(c.binary?1024:64)) goto defer;
    size_t rows=nr+nt,ns=lean_array_size(sugars);
    if(ns && ns!=rows) goto defer;
    for(unsigned i=0;i<7;++i) {
        lean_object *x=lean_ctor_get(limits,i);
        c.limits[i]=lean_is_scalar(x)?lean_unbox(x):UINT64_MAX/2;
    }
    if(c.columns>c.limits[0] || rows>c.limits[1]) goto defer;
    c.words=(c.columns+63)/64;c.capacity=rows<c.columns?rows:c.columns;
    c.project=c.binary && c.columns>=64 && nr>=4 && nt>=64;
    if(c.binary) c.scratch=(c.capacity+1)*c.words*8+16*c.capacity;
    if(c.project) c.scratch+=nt*(c.words*8+16)+16*c.words*8;
    if(c.scratch>c.limits[4]) goto defer;
    for(size_t i=0;i<ns;++i) if(!lean_is_scalar(lean_array_cptr(sugars)[i])) goto defer;
    uint64_t workspace=c.columns*(c.width+4);
    if(c.limits[5]<2*rows+workspace || c.limits[4]<workspace) goto defer;
    uint64_t entries=0;
    for(size_t i=0;i<rows;++i) {
        lean_object *row=lean_array_cptr(i<nr?reducers:targets)[i<nr?i:i-nr];
        size_t cb=lean_sarray_size(lean_ctor_get(row,0));
        size_t vb=lean_sarray_size(lean_ctor_get(row,1));
        size_t n=cb/4;
        if(cb%4 || n>c.quantum/2 || entries>c.quantum/2-n ||
           vb!=n*c.width) goto defer;
        entries+=n;
    }
    uint64_t bound=rows*65+2*entries+workspace+
        nt*(entries+(nt+3)*c.columns+64)+c.columns;
    if(bound>c.quantum) goto defer;
    if(c.binary) {
        uint64_t physical=rows*(c.words+8)+3*entries+4*nt*c.columns+5*c.columns+
            nt*(rows*c.words+64)+c.columns;
        if(c.project) physical+=nt*(c.columns+2*c.words+8)+((nr+3)/4)*(16*c.words+512)+8*nt*nr+4*c.columns;
        if(physical>BINARY_WORD_QUANTUM) goto defer;
    }
    uint8_t seen[2048]={0};
    for(size_t i=0;i<nr;++i) {
        lean_object *cs=lean_ctor_get(lean_array_cptr(reducers)[i],0);
        if(!lean_sarray_size(cs)) continue;
        uint64_t col=matrix_read(lean_sarray_cptr(cs),4);
        if(col>=c.columns || (seen[col/8]&(1u<<(col%8)))) goto defer;
        seen[col/8]|=(uint8_t)(1u<<(col%8));
    }
    /* Validate all borrowed rows before allocating elimination state. */
    for(size_t i=0;i<rows;++i) {
        lean_object *row=lean_array_cptr(i<nr?reducers:targets)[i<nr?i:i-nr];
        lean_object *cs=lean_ctor_get(row,0),*vs=lean_ctor_get(row,1);
        size_t n=lean_sarray_size(cs)/4;
        if(!matrix_work(&c,1) ||
           !matrix_charge(&c.stats[1],n,c.limits[2]) ||
           !matrix_bytes(&c,n*(4+c.width)) || !matrix_work(&c,n)) goto defer;
        uint64_t previous=0;
        for(size_t j=0;j<n;++j) {
            uint64_t col=matrix_read(lean_sarray_cptr(cs)+j*4,4);
            uint64_t value=matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width);
            if(col>=c.columns || (j && col<=previous) || !value || value>=p) goto defer;
            previous=col;
        }
    }
    if(!matrix_bytes(&c,workspace) || !matrix_work(&c,workspace)) goto defer;
    if(c.binary) {
        c.binary_rows=matrix_zeros((size_t)(c.capacity+1)*c.words*8);
        c.binary_meta=matrix_zeros((size_t)c.capacity*16);
        if(c.project) {
            c.project_rows=matrix_zeros((size_t)nt*c.words*8);
            c.project_meta=matrix_zeros((size_t)nt*16);
            c.project_table=matrix_zeros((size_t)16*c.words*8);
        }
        HEX_GROEBNER_BINARY_PIVOTS_USED(c.scratch);
    }
    c.dense=matrix_zeros(c.binary?0:(size_t)c.columns*c.width);
    c.slots=matrix_zeros((size_t)c.columns*4);
    c.pivots=matrix_empty();c.native_pivots=matrix_empty();c.remainders=matrix_empty();
    for(size_t i=0;i<rows;++i) {
        if(c.project && i==nr && !matrix_project_binary(&c,targets,sugars,nr,nt,ns)) goto defer;
        uint8_t target=i>=nr;
        lean_object *row=lean_array_cptr(target?targets:reducers)[target?i-nr:i];
        lean_object *cs=lean_ctor_get(row,0),*vs=lean_ctor_get(row,1);
        size_t n=lean_sarray_size(cs)/4;
        uint64_t sugar=ns?lean_unbox(lean_array_cptr(sugars)[i]):0;
        if(!matrix_work(&c,1)) goto defer;
        if(!n) {
            if(independent && target)
                matrix_remainder(&c,matrix_row(matrix_zeros(0),matrix_zeros(0)),sugar);
            ++c.stats[7];++c.stats[5];continue;
        }
        uint64_t first=matrix_read(lean_sarray_cptr(cs),4);
        if(!target) {
            uint64_t inverse;
            if(!matrix_inverse(&c,matrix_read(lean_sarray_cptr(vs),c.width),&inverse) ||
               !matrix_charge(&c.stats[2],n,c.limits[3]) ||
               !matrix_bytes(&c,n*(4+c.width))) goto defer;
            lean_object *output;
            if(inverse==1) {lean_inc(row);output=row;}
            else {
                if(!matrix_work(&c,n)) goto defer;
                lean_object *coeff=lean_alloc_sarray(1,n*c.width,n*c.width);
                for(size_t j=0;j<n;++j) {
                    uint64_t value=matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width);
                    matrix_write(lean_sarray_cptr(coeff)+j*c.width,c.width,(value*inverse)%p);
                }
                output=matrix_row(matrix_take(row,0),coeff);
            }
            if(!matrix_install(&c,output,first,inverse,sugar,0)) goto defer;
        } else {
            if(!c.project && !matrix_work(&c,n)) goto defer;
            for(size_t j=0;!c.project && j<n;++j) {
                uint64_t col=matrix_read(lean_sarray_cptr(cs)+j*4,4);
                if(c.binary) matrix_binary_dense(&c)[col>>3]|=(uint8_t)(1u<<(col&7));
                else matrix_write(lean_sarray_cptr(c.dense)+(size_t)col*c.width,c.width,
                    matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width));
            }
            uint64_t last=matrix_read(lean_sarray_cptr(cs)+(n-1)*4,4),leading=0;
            if(c.project) {
                uint64_t t=i-nr;
                memcpy(matrix_binary_dense(&c),lean_sarray_cptr(c.project_rows)+(size_t)t*c.words*8,
                    (size_t)c.words*8);
                last=matrix_binary_load(lean_sarray_cptr(c.project_meta)+t*16);
                sugar=matrix_binary_load(lean_sarray_cptr(c.project_meta)+t*16+8);
            }
            if(!matrix_scan(&c,first,&last,&leading,&sugar)) goto defer;
            if(leading) {
                uint64_t col=leading-1,inverse=1;
                if(col>=c.columns || last>=c.columns || col>last) goto defer;
                if(!independent && !c.binary && !matrix_inverse(&c,
                    matrix_read(lean_sarray_cptr(c.dense)+(size_t)col*c.width,c.width),&inverse))
                    goto defer;
                lean_object *output=matrix_gather(&c,col,last,inverse);
                if(!output) goto defer;
                if(independent) matrix_remainder(&c,output,sugar);
                else if(!matrix_install(&c,output,col,inverse,sugar,1)) goto defer;
            } else {
                if(independent)
                    matrix_remainder(&c,matrix_row(matrix_zeros(0),matrix_zeros(0)),sugar);
                ++c.stats[7];
            }
        }
        ++c.stats[5];
    }
    lean_object *ordered=matrix_empty();
    if(!independent) {
        if(!matrix_work(&c,c.columns)) {lean_dec(ordered);goto defer;}
        for(size_t col=0;col<(size_t)c.columns;++col) {
            uint64_t slot=matrix_read(lean_sarray_cptr(c.slots)+col*4,4);
            if(slot) {
                lean_object *pivot=lean_array_cptr(c.pivots)[slot-1];lean_inc(pivot);
                ordered=lean_array_push(ordered,pivot);
            }
        }
    }
    lean_object *echelon=lean_alloc_ctor(0,3,0);
    lean_ctor_set(echelon,0,ordered);lean_ctor_set(echelon,1,lean_uint64_to_nat(c.rank));
    lean_ctor_set(echelon,2,matrix_empty());
    lean_object *pair=lean_alloc_ctor(0,2,0);
    lean_ctor_set(pair,0,echelon);lean_ctor_set(pair,1,c.remainders);c.remainders=NULL;
    lean_object *ok=lean_alloc_ctor(1,1,0);lean_ctor_set(ok,0,pair);
    lean_object *stats=lean_alloc_ctor(0,8,0);
    for(unsigned i=0;i<8;++i) lean_ctor_set(stats,i,lean_uint64_to_nat(c.stats[i]));
    lean_object *result=lean_alloc_ctor(0,2,0);
    lean_ctor_set(result,0,ok);lean_ctor_set(result,1,stats);
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,result);
    matrix_cleanup(&c);HEX_GROEBNER_MATRIX_ACCEPTED();return some;
defer:
    matrix_cleanup(&c);HEX_GROEBNER_MATRIX_DEFERRED();return lean_box(0);
}

/* Independent row/workspace primitives retain the original Lean validator
   as their model; unsupported shapes defer before any charged work. */
LEAN_EXPORT lean_obj_res lean_hex_matrix_validate(uint64_t p,b_lean_obj_arg limits,
        b_lean_obj_arg columns,b_lean_obj_arg index,b_lean_obj_arg row,b_lean_obj_arg stats) {
#if UINTPTR_MAX == UINT64_MAX
    if(!lean_is_scalar(columns) || lean_unbox(columns)>UINT32_MAX) return lean_box(0);
    uint64_t cols=lean_unbox(columns),n=lean_sarray_size(lean_ctor_get(row,0))/4;
    /* Bound inspected row entries independently of the ambient column count.
       At most 524296 valid payload bytes are read before returning to Lean. */
    if(n>65537) return lean_box(0);
    uint64_t counts[8],allow[7];
    for(unsigned i=0;i<8;++i) {
        lean_object *v=lean_ctor_get(stats,i);
        if(!lean_is_scalar(v) || lean_unbox(v)>(UINT64_C(1)<<62)-1) return lean_box(0);
        counts[i]=lean_unbox(v);
    }
    for(unsigned i=0;i<7;++i) {
        lean_object *v=lean_ctor_get(limits,i);
        allow[i]=lean_is_scalar(v)?lean_unbox(v):UINT64_MAX/2;
    }
    unsigned width=p<=256?1:p<=65536?2:4;
    lean_object *ids=lean_ctor_get(row,0),*coeff=lean_ctor_get(row,1),*error=NULL;
    uint64_t column_bytes=lean_sarray_size(ids),coefficient_bytes=lean_sarray_size(coeff);
    unsigned resource=0,tag=0;uint64_t entry=0;
    if(!matrix_charge(&counts[0],1,allow[5])) {resource=5;goto exhausted;}
    if(column_bytes%4 || coefficient_bytes!=n*width) {tag=2;goto invalid;}
    if(!matrix_charge(&counts[1],n,allow[2])) {resource=2;goto exhausted;}
    if(!matrix_charge(&counts[3],column_bytes+coefficient_bytes,allow[4])) {resource=4;goto exhausted;}
    if(!matrix_charge(&counts[0],n,allow[5])) {resource=5;goto exhausted;}
    uint64_t previous=0;
    for(entry=0;entry<n;++entry) {
        uint64_t col=matrix_read(lean_sarray_cptr(ids)+4*entry,4);
        if(col>=cols || (entry && col<=previous)) {tag=3;goto invalid;}
        uint64_t value=matrix_read(lean_sarray_cptr(coeff)+width*entry,width);
        if(!value || value>=p) {tag=4;goto invalid;}
        previous=col;
    }
    goto result;
exhausted:
    error=lean_alloc_ctor(5,0,1);lean_ctor_set_uint8(error,0,(uint8_t)resource);goto result;
invalid:
    error=lean_alloc_ctor(tag,tag==2?1:2,0);lean_inc(index);lean_ctor_set(error,0,index);
    if(tag!=2) lean_ctor_set(error,1,lean_uint64_to_nat(entry));
result:;
    lean_object *out_stats=lean_alloc_ctor(0,8,0);
    for(unsigned i=0;i<8;++i) lean_ctor_set(out_stats,i,lean_uint64_to_nat(counts[i]));
    lean_object *outcome=lean_alloc_ctor(error?0:1,1,0);lean_ctor_set(outcome,0,error?error:lean_box(0));
    lean_object *pair=lean_alloc_ctor(0,2,0);lean_ctor_set(pair,0,outcome);lean_ctor_set(pair,1,out_stats);
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,pair);return some;
#else
    (void)p;(void)limits;(void)columns;(void)index;(void)row;(void)stats;return lean_box(0);
#endif
}

LEAN_EXPORT lean_obj_res lean_hex_matrix_zeros(b_lean_obj_arg size) {
    if(!lean_is_scalar(size) || lean_unbox(size)>1048576) return lean_box(0);
    lean_object *bytes=matrix_zeros(lean_unbox(size));
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,bytes);return some;
}
