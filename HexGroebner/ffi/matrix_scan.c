/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include "matrix_simd.h"

static inline uint64_t rd(const uint8_t *p, unsigned w) {
    uint64_t v=p[0];
    if(w>1) v|=(uint64_t)p[1]<<8;
    if(w>2) v|=(uint64_t)p[2]<<16 | (uint64_t)p[3]<<24;
    return v;
}
static inline void wr(uint8_t *p,unsigned w,uint64_t v) {
    p[0]=(uint8_t)v;
    if(w>1) p[1]=(uint8_t)(v>>8);
    if(w>2) {p[2]=(uint8_t)(v>>16);p[3]=(uint8_t)(v>>24);}
}
static uint64_t bounded_nat(b_lean_obj_arg n,uint64_t cap) {
    lean_object *limit=lean_uint64_to_nat(cap);
    uint64_t value=lean_nat_dec_le(n,limit)?lean_uint64_of_nat(n):cap;
    lean_dec(limit);
    return value;
}
static inline int geometry(b_lean_obj_arg pivot,unsigned w,uint64_t *size) {
    size_t cb=lean_sarray_size(lean_ctor_get(pivot,0));
    size_t vb=lean_sarray_size(lean_ctor_get(pivot,1));
    *size=cb/4;
    return cb%4==0 && *size!=0 && *size<=UINT32_MAX && vb==*size*w;
}
static lean_obj_res result(lean_obj_arg state,lean_obj_arg events,
        uint64_t work,uint64_t reductions,uint64_t traces,uint8_t status) {
    lean_object *out=lean_alloc_ctor(0,5,1);
    lean_ctor_set(out,0,state);lean_ctor_set(out,1,events);
    lean_ctor_set(out,2,lean_uint64_to_nat(work));
    lean_ctor_set(out,3,lean_uint64_to_nat(reductions));
    lean_ctor_set(out,4,lean_uint64_to_nat(traces));
    lean_ctor_set_uint8(out,5*sizeof(void*),status);
    return out;
}

__attribute__((always_inline))
static inline int scalar_update(uint8_t *data,const uint8_t *cs,const uint8_t *vs,
        unsigned w,uint64_t columns,uint64_t entry,uint64_t p,uint64_t factor,uint64_t reciprocal) {
    uint64_t j=rd(cs+(size_t)entry*4,4),b=rd(vs+(size_t)entry*w,w);
    if(j>=columns || !b || b>=p || (entry && rd(cs+(size_t)(entry-1)*4,4)>=j)) return 0;
    uint64_t a=rd(data+(size_t)j*w,w);
    if(a>=p) return 0;
    uint64_t product=factor*b;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    uint64_t q=w<4?(product*reciprocal)>>32:(uint64_t)(((__uint128_t)product*reciprocal)>>64);
    product-=q*p;if(product>=p) product-=p;
#else
    (void)reciprocal;
    product%=p;
#endif
    uint64_t difference=a-product;
    difference+=p&(UINT64_C(0)-(difference>>63));
    wr(data+(size_t)j*w,w,difference);
    return 1;
}

#define HEX_SCAN_NAME hex_scan_u8
#define HEX_SCAN_ATTRIBUTE
#define HEX_SCAN_VECTOR 0
#define HEX_SCAN_WIDTH 1
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#define HEX_SCAN_NAME hex_scan_u16
#define HEX_SCAN_ATTRIBUTE
#define HEX_SCAN_VECTOR 0
#define HEX_SCAN_WIDTH 2
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#define HEX_SCAN_NAME hex_scan_u32
#define HEX_SCAN_ATTRIBUTE
#define HEX_SCAN_VECTOR 0
#define HEX_SCAN_WIDTH 4
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#if HEX_GROEBNER_AVX2
#define HEX_SCAN_NAME hex_scan_avx2_u8
#define HEX_SCAN_ATTRIBUTE __attribute__((target("avx2")))
#define HEX_SCAN_VECTOR 1
#define HEX_SCAN_WIDTH 1
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#endif
#if HEX_GROEBNER_AVX2
#define HEX_SCAN_NAME hex_scan_avx2_u16
#define HEX_SCAN_ATTRIBUTE __attribute__((target("avx2")))
#define HEX_SCAN_VECTOR 1
#define HEX_SCAN_WIDTH 2
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#endif
#if HEX_GROEBNER_AVX2
#define HEX_SCAN_NAME hex_scan_avx2
#define HEX_SCAN_ATTRIBUTE __attribute__((target("avx2")))
#define HEX_SCAN_VECTOR 1
#define HEX_SCAN_WIDTH 4
#include "matrix_scan_impl.h"
#undef HEX_SCAN_NAME
#undef HEX_SCAN_ATTRIBUTE
#undef HEX_SCAN_VECTOR
#undef HEX_SCAN_WIDTH
#endif

LEAN_EXPORT lean_obj_res lean_hex_scan_transition(uint64_t p,
        b_lean_obj_arg slots,b_lean_obj_arg pivots,lean_obj_arg initial,
        b_lean_obj_arg quantum,b_lean_obj_arg work,b_lean_obj_arg trace,uint8_t provenance) {
#if HEX_GROEBNER_AVX2
    if(p>65536 && (p&1) && hex_avx2_available())
        return hex_scan_avx2(p,slots,pivots,initial,quantum,work,trace,provenance);
    if((p&1) && hex_avx2_available()) {
        if(p<=256) return hex_scan_avx2_u8(p,slots,pivots,initial,quantum,work,trace,provenance);
        return hex_scan_avx2_u16(p,slots,pivots,initial,quantum,work,trace,provenance);
    }
#endif
    if(p<=256) return hex_scan_u8(p,slots,pivots,initial,quantum,work,trace,provenance);
    if(p<=65536) return hex_scan_u16(p,slots,pivots,initial,quantum,work,trace,provenance);
    return hex_scan_u32(p,slots,pivots,initial,quantum,work,trace,provenance);
}

static lean_object *append_scalar(lean_obj_arg bytes,unsigned w,uint64_t value) {
    size_t used=lean_sarray_size(bytes),cap=lean_sarray_capacity(bytes);
    if(!lean_is_exclusive(bytes) || cap-used<w) {
        size_t wanted=used+w;
        size_t grown=cap>SIZE_MAX/2?wanted:cap*2;
        if(grown<wanted) grown=wanted;
        lean_object *copy=lean_alloc_sarray(1,used,grown);
        memcpy(lean_sarray_cptr(copy),lean_sarray_cptr(bytes),used);
        lean_dec(bytes);bytes=copy;
    }
    wr(lean_sarray_cptr(bytes)+used,w,value);
    lean_sarray_set_size(bytes,used+w);
    return bytes;
}

static lean_obj_res gather_result(lean_obj_arg state,uint64_t entries,
        uint64_t bytes,uint64_t work,uint8_t status) {
    lean_object *out=lean_alloc_ctor(0,4,1);
    lean_ctor_set(out,0,state);lean_ctor_set(out,1,lean_uint64_to_nat(entries));
    lean_ctor_set(out,2,lean_uint64_to_nat(bytes));lean_ctor_set(out,3,lean_uint64_to_nat(work));
    lean_ctor_set_uint8(out,4*sizeof(void*),status);
    return out;
}

LEAN_EXPORT lean_obj_res lean_hex_gather(uint64_t p,lean_obj_arg initial,
        b_lean_obj_arg stop_arg,b_lean_obj_arg quantum_arg,b_lean_obj_arg entries_arg,
        b_lean_obj_arg bytes_arg,b_lean_obj_arg work_arg,uint64_t factor) {
    unsigned w=p<=256?1:p<=65536?2:4;
    lean_object *dense=lean_ctor_get(initial,0),*cols=lean_ctor_get(initial,1),*coeff=lean_ctor_get(initial,2);
    size_t db=lean_sarray_size(dense),cb=lean_sarray_size(cols),vb=lean_sarray_size(coeff);
    uint64_t size=db/w,stop=bounded_nat(stop_arg,UINT64_C(4294967296));
    uint64_t cursor=bounded_nat(lean_ctor_get(initial,3),UINT64_C(4294967296));
    uint64_t quantum=bounded_nat(quantum_arg,4097);
    if(p<2 || p>=UINT64_C(2147483648) || !factor || factor>=p || quantum>4096 || db%w ||
       size>UINT32_MAX || cursor>stop || stop>size || cb%4 || vb!=(cb/4)*w)
        return gather_result(initial,0,0,0,5);
    uint64_t entries_limit=bounded_nat(entries_arg,4096),bytes_limit=bounded_nat(bytes_arg,32768);
    uint64_t work_limit=bounded_nat(work_arg,4096);
    lean_inc(dense);lean_inc(cols);lean_inc(coeff);lean_dec(initial);
    dense=lean_sarray_ensure_exclusive(dense);
    /* Output aliases retain their original data until append_scalar copies. */
    uint8_t *data=lean_sarray_cptr(dense);
    uint64_t entries=0,bytes=0,work=0;uint8_t status=0;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    uint64_t reciprocal;
    if(w<4) reciprocal=UINT64_C(4294967296)/p;
    else {reciprocal=UINT64_MAX/p;if(UINT64_MAX%p==p-1) ++reciprocal;}
#endif
    for(uint64_t tick=0;tick<quantum;++tick) {
        if(cursor>=stop) {status=1;break;}
        uint64_t a=rd(data+(size_t)cursor*w,w);
        if(a>=p) {status=6;break;}
        if(a) {
            size_t cn=lean_sarray_size(cols),vn=lean_sarray_size(coeff);
            if(cn && rd(lean_sarray_cptr(cols)+cn-4,4)>=cursor) {status=6;break;}
            if(entries>=entries_limit) {status=2;break;}++entries;
            if(bytes+4+w>bytes_limit) {status=3;break;}bytes+=4+w;
            if(cn>SIZE_MAX-4 || vn>SIZE_MAX-w) {status=5;break;}
            if(factor!=1) {if(work>=work_limit) {status=4;break;}++work;}
            uint64_t value=a;
            if(factor!=1) {
            value*=factor;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
            uint64_t q=w<4?(value*reciprocal)>>32:(uint64_t)(((__uint128_t)value*reciprocal)>>64);
            value-=q*p;if(value>=p) value-=p;
#else
            value%=p;
#endif
            }
            cols=append_scalar(cols,4,cursor);coeff=append_scalar(coeff,w,value);
            wr(data+(size_t)cursor*w,w,0);
        }
        ++cursor;
    }
    lean_object *state=lean_alloc_ctor(0,4,0);
    lean_ctor_set(state,0,dense);lean_ctor_set(state,1,cols);lean_ctor_set(state,2,coeff);
    lean_ctor_set(state,3,lean_uint64_to_nat(cursor));
    return gather_result(state,entries,bytes,work,status);
}
