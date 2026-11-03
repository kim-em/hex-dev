/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_AVX512_H
#define HEX_GROEBNER_AVX512_H
#include "matrix_simd.h"
#ifndef HEX_GROEBNER_AVX512_USED
#define HEX_GROEBNER_AVX512_USED(width,contiguous) ((void)0)
#endif
#if HEX_GROEBNER_AVX2 && !defined(HEX_GROEBNER_NO_AVX512)
#define HEX_GROEBNER_AVX512 1
static inline int hex_avx512_available(void) {
    static atomic_uint cached=0;
    unsigned known=atomic_load_explicit(&cached,memory_order_relaxed);
    if(known) return known==2;
    unsigned a,b,c,d,lo,hi;int available=0;
    const unsigned xsave=(1u<<26)|(1u<<27)|(1u<<28);
    const unsigned features=(1u<<16)|(1u<<17)|(1u<<30)|(1u<<31);
    if(__get_cpuid(1,&a,&b,&c,&d) && (c&xsave)==xsave) {
        __asm__ volatile("xgetbv" : "=a"(lo),"=d"(hi) : "c"(0));
        (void)hi;
        if((lo&0xe6)==0xe6 && __get_cpuid_count(7,0,&a,&b,&c,&d) &&
           (b&features)==features && (b&(1u<<5))) available=1;
    }
    atomic_store_explicit(&cached,available?2:1,memory_order_relaxed);return available;
}
/* Sixteen independent canonical updates, or zero with dense unchanged.
   The caller bounds all source loads to sixteen entries. Validation, exact
   modular arithmetic and narrow-gather headroom match the eight-lane kernel.
   A declined packet must fall back to eight-lane/scalar updates in order.
   Keep validation and exactness changes in step with hex_scan8_mode. */
__attribute__((target("avx512f,avx512dq,avx512bw,avx512vl"),always_inline))
static inline __m512i hex_mont32_even16(__m512i b,__m512i factor,
        __m512i negative_inverse,__m512i p64,__m512i pm1) {
    __m512i t=_mm512_mul_epu32(b,factor);
    __m512i m=_mm512_mullo_epi32(t,negative_inverse);
    __m512i sum=_mm512_add_epi64(t,_mm512_mul_epu32(m,p64));
    __m512i u=_mm512_srli_epi64(sum,32);
    return _mm512_mask_sub_epi64(u,_mm512_cmpgt_epi64_mask(u,pm1),u,p64);
}

/* For p=2^31-1, folding the high 31 bits into the low 31 bits gives
   a residue below 2p for every product x<p². One subtraction canonicalizes it. */
__attribute__((target("avx512f,avx512dq,avx512bw,avx512vl"),always_inline))
static inline __m512i hex_mersenne31_even16(__m512i b,__m512i factor) {
    __m512i p=_mm512_set1_epi64(INT32_MAX),pm1=_mm512_set1_epi64(INT32_MAX-1);
    __m512i x=_mm512_mul_epu32(b,factor);
    __m512i r=_mm512_add_epi64(_mm512_and_si512(x,p),_mm512_srli_epi64(x,31));
    return _mm512_mask_sub_epi64(r,_mm512_cmpgt_epi64_mask(r,pm1),r,p);
}

__attribute__((target("avx512f,avx512dq,avx512bw,avx512vl"),always_inline))
static inline unsigned hex_scan16_mode(uint8_t *dense,const uint8_t *columns,const uint8_t *coefficients,
        size_t entry,uint64_t column_count,uint32_t p,uint32_t multiplier,uint32_t reduction,unsigned width,unsigned mersenne) {
    if(mersenne && (width!=4 || p!=INT32_MAX)) return 0;
    __m512i j=_mm512_loadu_si512((const void *)(columns+entry*4));
    __m512i b;
    if(width==1) b=_mm512_cvtepu8_epi32(_mm_loadu_si128((const __m128i *)(coefficients+entry)));
    else if(width==2) b=_mm512_cvtepu16_epi32(_mm256_loadu_si256((const __m256i *)(coefficients+entry*2)));
    else b=_mm512_loadu_si512((const void *)(coefficients+entry*4));
    int32_t first,last;memcpy(&first,columns+entry*4,4);memcpy(&last,columns+(entry+15)*4,4);
    if(first<0 || last<0 || (uint64_t)last>=column_count) return 0;
    if(entry) {uint32_t previous;memcpy(&previous,columns+(entry-1)*4,4);if(previous>=(uint32_t)first) return 0;}
    __m512i before=_mm512_permutexvar_epi32(_mm512_setr_epi32(0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14),j);
    __mmask16 sorted=_mm512_cmpgt_epi32_mask(j,before)|1;
    __m512i pv=_mm512_set1_epi32((int32_t)p);
    __mmask16 valid=sorted & _mm512_cmpgt_epi32_mask(b,_mm512_setzero_si512()) & _mm512_cmpgt_epi32_mask(pv,b);
    if(valid!=UINT16_MAX) return 0;
    __m512i consecutive=_mm512_add_epi32(_mm512_set1_epi32(first),_mm512_setr_epi32(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15));
    int contiguous=_mm512_cmpeq_epi32_mask(j,consecutive)==UINT16_MAX;
    __m512i a;
    if(width<4 && !contiguous && column_count-(uint32_t)last < 4/width) return 0;
    if(width==1) {
        a=contiguous?_mm512_cvtepu8_epi32(_mm_loadu_si128((const __m128i *)(dense+(size_t)first))):
            _mm512_and_si512(_mm512_i32gather_epi32(j,(const void *)dense,1),_mm512_set1_epi32(255));
    } else if(width==2) {
        a=contiguous?_mm512_cvtepu16_epi32(_mm256_loadu_si256((const __m256i *)(dense+(size_t)first*2))):
            _mm512_and_si512(_mm512_i32gather_epi32(j,(const void *)dense,2),_mm512_set1_epi32(65535));
    } else a=contiguous?_mm512_loadu_si512((const void *)(dense+(size_t)first*4)):
        _mm512_i32gather_epi32(j,(const void *)dense,4);
    valid=_mm512_cmpgt_epi32_mask(a,_mm512_set1_epi32(-1)) & _mm512_cmpgt_epi32_mask(pv,a);
    if(valid!=UINT16_MAX) return 0;
    __m512i f=_mm512_set1_epi32((int32_t)multiplier),inv=_mm512_set1_epi32((int32_t)reduction);
    __m512i product;
    if(width<4) {
        /* x < p^2 < 2^32; floor(2^32/p) underestimates x/p by at most one. */
        __m512i x=_mm512_mullo_epi32(b,f);
        __m512i even=_mm512_srli_epi64(_mm512_mul_epu32(x,inv),32);
        __m512i odd=_mm512_srli_epi64(_mm512_mul_epu32(_mm512_srli_epi64(x,32),inv),32);
        __m512i q=_mm512_or_si512(even,_mm512_slli_epi64(odd,32));
        product=_mm512_sub_epi32(x,_mm512_mullo_epi32(q,pv));
        product=_mm512_mask_sub_epi32(product,_mm512_cmpgt_epi32_mask(product,_mm512_set1_epi32((int32_t)p-1)),product,pv);
    } else if(mersenne) {
        HEX_GROEBNER_MERSENNE_USED();
        /* The existing caller supplies factor*2^32 mod p. Since 2^32=2 mod p,
           recover factor by modular halving without changing the ABI. */
        uint32_t canonical=(multiplier>>1)+(multiplier&1)*UINT32_C(1073741824);
        __m512i f31=_mm512_set1_epi64(canonical);
        __m512i even=hex_mersenne31_even16(b,f31);
        __m512i odd=hex_mersenne31_even16(_mm512_srli_epi64(b,32),f31);
        product=_mm512_or_si512(even,_mm512_slli_epi64(odd,32));
    } else {
        __m512i p64=_mm512_set1_epi64(p),pm1=_mm512_set1_epi64(p-1);
        __m512i even=hex_mont32_even16(b,f,inv,p64,pm1);
        __m512i odd=hex_mont32_even16(_mm512_srli_epi64(b,32),f,inv,p64,pm1);
        product=_mm512_or_si512(even,_mm512_slli_epi64(odd,32));
    }
    __m512i difference=_mm512_sub_epi32(a,product);
    difference=_mm512_add_epi32(difference,_mm512_and_si512(_mm512_srai_epi32(difference,31),pv));
    if(contiguous) {
        if(width==4) _mm512_storeu_si512((void *)(dense+(size_t)first*4),difference);
        else if(width==2) _mm256_storeu_si256((__m256i *)(dense+(size_t)first*2),_mm512_cvtepi32_epi16(difference));
        else _mm_storeu_si128((__m128i *)(dense+(size_t)first),_mm512_cvtepi32_epi8(difference));
    } else {
        uint32_t indices[16],values[16];
        _mm512_storeu_si512((void *)indices,j);_mm512_storeu_si512((void *)values,difference);
        for(unsigned k=0;k<16;++k) memcpy(dense+(size_t)indices[k]*width,&values[k],width);
    }
    HEX_GROEBNER_AVX512_USED(width,contiguous);
    return 16;
}
#else
#define HEX_GROEBNER_AVX512 0
#endif
#endif
