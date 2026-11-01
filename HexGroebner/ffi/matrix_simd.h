/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_SIMD_H
#define HEX_GROEBNER_SIMD_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>

#if (defined(__x86_64__) || defined(__i386__)) && defined(__GNUC__) && !defined(HEX_GROEBNER_NO_AVX2)
#define HEX_GROEBNER_AVX2 1
#include <immintrin.h>
#include <cpuid.h>
#include <stdatomic.h>

/* Cache only an ISA capability, with no compiler-runtime CPU model symbols.
   XGETBV is executed only after CPU and OS XSAVE support are established. */
static inline int hex_avx2_available(void) {
    static atomic_uint cached=0;
    unsigned known=atomic_load_explicit(&cached,memory_order_relaxed);
    if(known) return known==2;
    unsigned a,b,c,d,lo,hi;
    int available=0;
    const unsigned xsave=(1u<<26)|(1u<<27)|(1u<<28);
    if(__get_cpuid(1,&a,&b,&c,&d) && (c&xsave)==xsave) {
        __asm__ volatile("xgetbv" : "=a"(lo),"=d"(hi) : "c"(0));
        (void)hi;
        if((lo&6)==6 && __get_cpuid_count(7,0,&a,&b,&c,&d) && (b&(1u<<5))) available=1;
    }
    atomic_store_explicit(&cached,available?2:1,memory_order_relaxed);
    return available;
}

static inline uint32_t hex_mont32_inverse(uint32_t p) {
    uint32_t inverse=1;
    for(unsigned i=0;i<5;++i) inverse*=2-p*inverse;
    return UINT32_C(0)-inverse;
}

/* For odd 2 < p < 2^31, R=2^32 and 0<=a,b<p:
   f=(aR mod p), t=f*b<p^2, m=(t*(-p^-1)) mod R.
   t+m*p < p^2+R*p < 3*2^62 < 2^64 and is divisible by R.
   u=(t+m*p)/R < 2p, so one subtraction gives the canonical a*b mod p.
   Each 64-bit lane holds one product; the upper 32-bit lanes are unused. */
__attribute__((target("avx2"),always_inline))
static inline __m256i hex_mont32_even(__m256i b,__m256i factor,
        __m256i negative_inverse,__m256i p64,__m256i pm1) {
    __m256i t=_mm256_mul_epu32(b,factor);
    __m256i m=_mm256_mullo_epi32(t,negative_inverse);
    __m256i sum=_mm256_add_epi64(t,_mm256_mul_epu32(m,p64));
    __m256i u=_mm256_srli_epi64(sum,32);
    return _mm256_sub_epi64(u,_mm256_and_si256(_mm256_cmpgt_epi64(u,pm1),p64));
}

/* Eight independent canonical updates, or zero with dense unchanged.
   The caller supplies eight in-bounds packed row entries and disjoint owned
   dense/borrowed source buffers. All row validation precedes gathers/stores;
   invalid vectors fall back to scalar processing to preserve failure prefixes.
   Width is 1, 2 or 4. For narrow widths, multiplier is the canonical factor and
   reduction=floor(2^32/p). For width 4, multiplier=factor*2^32 mod p and
   reduction=-p^-1 mod 2^32. Narrow gathers read four bytes only when the complete
   read lies within the logical dense buffer; otherwise the caller uses scalar updates. */
__attribute__((target("avx2"),always_inline))
static inline unsigned hex_scan8(uint8_t *dense,const uint8_t *columns,const uint8_t *coefficients,
        size_t entry,uint64_t column_count,uint32_t p,uint32_t multiplier,uint32_t reduction,unsigned width) {
    __m256i j=_mm256_loadu_si256((const __m256i *)(columns+entry*4));
    __m256i b;
    if(width==1) b=_mm256_cvtepu8_epi32(_mm_loadl_epi64((const __m128i *)(coefficients+entry)));
    else if(width==2) b=_mm256_cvtepu16_epi32(_mm_loadu_si128((const __m128i *)(coefficients+entry*2)));
    else b=_mm256_loadu_si256((const __m256i *)(coefficients+entry*4));
    int32_t first=_mm256_extract_epi32(j,0),last=_mm256_extract_epi32(j,7);
    if(first<0 || last<0 || (uint64_t)last>=column_count) return 0;
    if(entry) {uint32_t previous;memcpy(&previous,columns+(entry-1)*4,4);if(previous>=(uint32_t)first) return 0;}
    __m256i before=_mm256_permutevar8x32_epi32(j,_mm256_setr_epi32(0,0,1,2,3,4,5,6));
    __m256i sorted=_mm256_or_si256(_mm256_cmpgt_epi32(j,before),_mm256_setr_epi32(-1,0,0,0,0,0,0,0));
    __m256i pv=_mm256_set1_epi32((int32_t)p);
    __m256i valid=_mm256_and_si256(sorted,_mm256_and_si256(
        _mm256_cmpgt_epi32(b,_mm256_setzero_si256()),_mm256_cmpgt_epi32(pv,b)));
    if(_mm256_movemask_epi8(valid)!=-1) return 0;
    __m256i consecutive=_mm256_add_epi32(_mm256_set1_epi32(first),_mm256_setr_epi32(0,1,2,3,4,5,6,7));
    int contiguous=_mm256_movemask_epi8(_mm256_cmpeq_epi32(j,consecutive))==-1;
    __m256i a;
    if(width<4 && !contiguous && column_count-(uint32_t)last < 4/width) return 0;
    if(width==1) {
        a=contiguous?_mm256_cvtepu8_epi32(_mm_loadl_epi64((const __m128i *)(dense+(size_t)first))):
            _mm256_and_si256(_mm256_i32gather_epi32((const int *)dense,j,1),_mm256_set1_epi32(255));
    } else if(width==2) {
        a=contiguous?_mm256_cvtepu16_epi32(_mm_loadu_si128((const __m128i *)(dense+(size_t)first*2))):
            _mm256_and_si256(_mm256_i32gather_epi32((const int *)dense,j,2),_mm256_set1_epi32(65535));
    } else a=contiguous?_mm256_loadu_si256((const __m256i *)(dense+(size_t)first*4)):
        _mm256_i32gather_epi32((const int *)dense,j,4);
    valid=_mm256_and_si256(_mm256_cmpgt_epi32(a,_mm256_set1_epi32(-1)),_mm256_cmpgt_epi32(pv,a));
    if(_mm256_movemask_epi8(valid)!=-1) return 0;
    __m256i f=_mm256_set1_epi32((int32_t)multiplier),inv=_mm256_set1_epi32((int32_t)reduction);
    __m256i product;
    if(width<4) {
        /* x < p^2 < 2^32; floor(2^32/p) underestimates x/p by at most one. */
        __m256i x=_mm256_mullo_epi32(b,f);
        __m256i even=_mm256_srli_epi64(_mm256_mul_epu32(x,inv),32);
        __m256i odd=_mm256_srli_epi64(_mm256_mul_epu32(_mm256_srli_epi64(x,32),inv),32);
        __m256i q=_mm256_or_si256(even,_mm256_slli_epi64(odd,32));
        product=_mm256_sub_epi32(x,_mm256_mullo_epi32(q,pv));
        product=_mm256_sub_epi32(product,_mm256_and_si256(_mm256_cmpgt_epi32(product,_mm256_set1_epi32((int32_t)p-1)),pv));
    } else {
        __m256i p64=_mm256_set1_epi64x(p),pm1=_mm256_set1_epi64x(p-1);
        __m256i even=hex_mont32_even(b,f,inv,p64,pm1);
        __m256i odd=hex_mont32_even(_mm256_srli_epi64(b,32),f,inv,p64,pm1);
        product=_mm256_or_si256(even,_mm256_slli_epi64(odd,32));
    }
    __m256i difference=_mm256_sub_epi32(a,product);
    difference=_mm256_add_epi32(difference,_mm256_and_si256(_mm256_srai_epi32(difference,31),pv));
    if(contiguous) {
        if(width==4) _mm256_storeu_si256((__m256i *)(dense+(size_t)first*4),difference);
        else {
            __m128i words=_mm_packus_epi32(_mm256_castsi256_si128(difference),_mm256_extracti128_si256(difference,1));
            if(width==2) _mm_storeu_si128((__m128i *)(dense+(size_t)first*2),words);
            else _mm_storel_epi64((__m128i *)(dense+(size_t)first),_mm_packus_epi16(words,_mm_setzero_si128()));
        }
        return 8;
    }
    uint32_t indices[8],values[8];
    _mm256_storeu_si256((__m256i *)indices,j);
    _mm256_storeu_si256((__m256i *)values,difference);
    for(unsigned k=0;k<8;++k) memcpy(dense+(size_t)indices[k]*width,&values[k],width);
    return 8;
}
#else
#define HEX_GROEBNER_AVX2 0
#endif
#endif
