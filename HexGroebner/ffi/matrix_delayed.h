/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_DELAYED_H
#define HEX_GROEBNER_DELAYED_H

#if HEX_GROEBNER_AVX2
__attribute__((target("avx2")))
static void delayed_update_avx2(matrix_context *c,const delayed_pivot *pivot,uint64_t factor) {
    __m256i factors=_mm256_set1_epi64x((long long)factor);
    uint8_t *data=lean_sarray_cptr(c->dense);
    uint64_t j=1;
    for(;j+4<=pivot->size;j+=4) {
        HEX_GROEBNER_DELAYED_UPDATE(c->width);
        uint32_t indices[4];memcpy(indices,pivot->columns+(size_t)j*4,16);
        __m128i ids=_mm_loadu_si128((const __m128i_u*)indices);
        __m256i coefficients;
        if(c->width==2) {
            __m128i packed=_mm_loadl_epi64((const __m128i*)(pivot->coefficients+(size_t)j*2));
            coefficients=_mm256_cvtepu16_epi64(packed);
        } else {
            uint32_t packed;memcpy(&packed,pivot->coefficients+(size_t)j,4);
            coefficients=_mm256_cvtepu8_epi64(_mm_cvtsi32_si128((int)packed));
        }
        __m256i products=_mm256_mul_epu32(coefficients,factors);
        int contiguous=indices[1]==indices[0]+1 && indices[2]==indices[0]+2 && indices[3]==indices[0]+3;
        __m256i current=contiguous?_mm256_loadu_si256((const __m256i_u*)(data+(size_t)indices[0]*8)):
            _mm256_i32gather_epi64((const long long int*)data,ids,8);
        __m256i updated=_mm256_add_epi64(current,products);
        if(contiguous) _mm256_storeu_si256((__m256i_u*)(data+(size_t)indices[0]*8),updated);
        else {
            uint64_t values[4];_mm256_storeu_si256((__m256i_u*)values,updated);
            for(unsigned k=0;k<4;++k) memcpy(data+(size_t)indices[k]*8,&values[k],8);
        }
    }
    for(;j<pivot->size;++j) {
        uint64_t k=matrix_read(pivot->columns+(size_t)j*4,4);
        uint64_t b=matrix_read(pivot->coefficients+(size_t)j*c->width,c->width);
        delayed_write(c,k,delayed_read(c,k)+factor*b);
    }
}
#endif

#if HEX_GROEBNER_AVX2
__attribute__((target("avx2")))
static void delayed_update_wide_avx2(matrix_context *c,const delayed_pivot *pivot,uint64_t factor) {
    __m256i factors=_mm256_set1_epi64x((long long)factor);
    __m256i modulus=_mm256_set1_epi64x((long long)c->modulus_squared);
    __m256i threshold=_mm256_set1_epi64x((long long)(c->modulus_squared-1));
    uint8_t *data=lean_sarray_cptr(c->dense);
    uint64_t j=1;
    for(;j+4<=pivot->size;j+=4) {
        HEX_GROEBNER_DELAYED_UPDATE(c->width);
        uint32_t indices[4];memcpy(indices,pivot->columns+(size_t)j*4,16);
        __m128i ids=_mm_loadu_si128((const __m128i_u*)indices);
        __m256i coefficients;
        coefficients=_mm256_cvtepu32_epi64(_mm_loadu_si128(
            (const __m128i_u*)(pivot->coefficients+(size_t)j*4)));
        __m256i products=_mm256_mul_epu32(coefficients,factors);
        int contiguous=indices[1]==indices[0]+1 && indices[2]==indices[0]+2 && indices[3]==indices[0]+3;
        __m256i current=contiguous?_mm256_loadu_si256((const __m256i_u*)(data+(size_t)indices[0]*8)):
            _mm256_i32gather_epi64((const long long int*)data,ids,8);
        __m256i updated=_mm256_add_epi64(current,products);
        updated=_mm256_sub_epi64(updated,_mm256_and_si256(
            _mm256_cmpgt_epi64(updated,threshold),modulus));
        if(contiguous) _mm256_storeu_si256((__m256i_u*)(data+(size_t)indices[0]*8),updated);
        else {
            uint64_t values[4];_mm256_storeu_si256((__m256i_u*)values,updated);
            for(unsigned k=0;k<4;++k) memcpy(data+(size_t)indices[k]*8,&values[k],8);
        }
    }
    for(;j<pivot->size;++j) {
        uint64_t k=matrix_read(pivot->columns+(size_t)j*4,4);
        uint64_t b=matrix_read(pivot->coefficients+(size_t)j*c->width,c->width);
        uint64_t value=delayed_read(c,k)+factor*b;
        if(value>=c->modulus_squared) value-=c->modulus_squared;
        delayed_write(c,k,value);
    }
}
#endif

/* Small fields receive at most columns products and stay below 2^50.
   Wider fields keep residues modulo p^2; each step is below 2*p^2 < 2^63,
   so one correction restores acc<p^2 and preserves the residue modulo p. */
static int delayed_scan(matrix_context *c,uint64_t first,uint64_t *last,
        uint64_t *leading,uint64_t *sugar) {
    uint64_t charged=first;
    for(uint64_t col=first;col<c->columns && col<=*last;++col) {
        if(col>=charged) {
            uint64_t stop=col+64<*last+1?col+64:*last+1;
            if(!matrix_work(c,stop-col)) return 0;
            charged=stop;
        }
        uint64_t a=delayed_read(c,col)%c->p;
        delayed_write(c,col,a);
        if(!a) continue;
        uint64_t slot=matrix_read(lean_sarray_cptr(c->slots)+(size_t)col*4,4);
        if(!slot) {if(!*leading) *leading=col+1;continue;}
        delayed_pivot pivot;
        memcpy(&pivot,lean_sarray_cptr(c->delayed_meta)+(size_t)(slot-1)*sizeof(pivot),sizeof(pivot));
        if(pivot.end>*last) *last=pivot.end;
        if(pivot.sugar>*sugar) *sugar=pivot.sugar;
        if(!matrix_work(c,pivot.size)) return 0;
        uint64_t factor=c->p-a;
#if HEX_GROEBNER_AVX2
        if(hex_avx2_available()) {
            if(c->width==4) delayed_update_wide_avx2(c,&pivot,factor);
            else delayed_update_avx2(c,&pivot,factor);
        }
        else
#endif
        {
            HEX_GROEBNER_DELAYED_UPDATE(0);
            for(uint64_t j=1;j<pivot.size;++j) {
                uint64_t k=matrix_read(pivot.columns+(size_t)j*4,4);
                uint64_t b=matrix_read(pivot.coefficients+(size_t)j*c->width,c->width);
                uint64_t value=delayed_read(c,k)+factor*b;
                if(c->width==4 && value>=c->modulus_squared) value-=c->modulus_squared;
                delayed_write(c,k,value);
            }
        }
        delayed_write(c,col,0);
        ++c->stats[6];
    }
    return 1;
}
static lean_object *delayed_gather(matrix_context *c,uint64_t first,uint64_t last,
        uint64_t inverse) {
    if(!matrix_work(c,last+1-first)) return NULL;
    uint64_t n=0;
    for(uint64_t col=first;col<=last;++col) if(delayed_read(c,col)%c->p) ++n;
    if(!matrix_charge(&c->stats[2],n,c->limits[3]) ||
       !matrix_bytes(c,n*(4+c->width)) || (inverse!=1 && !matrix_work(c,n))) return NULL;
    lean_object *cs=lean_alloc_sarray(1,(size_t)n*4,(size_t)n*4);
    lean_object *vs=lean_alloc_sarray(1,(size_t)n*c->width,(size_t)n*c->width);
    uint64_t i=0;
    for(uint64_t col=first;col<=last;++col) {
        uint64_t a=delayed_read(c,col)%c->p;
        delayed_write(c,col,0);
        if(a) {
            matrix_write(lean_sarray_cptr(cs)+(size_t)i*4,4,col);
            matrix_write(lean_sarray_cptr(vs)+(size_t)i*c->width,c->width,(a*inverse)%c->p);
            ++i;
        }
    }
    return matrix_row(cs,vs);
}


/* Every validated nonzero F2 coefficient is one. XOR preserves parity even
   under test-only even accumulator offsets; normalization precedes each test. */
static int sparse_scan(matrix_context *c,uint64_t first,uint64_t *last,
        uint64_t *leading,uint64_t *sugar) {
    /* These private buffers are stable throughout scanning. The accumulator
       is fresh and disjoint from slots, descriptors and every borrowed pivot. */
    uint8_t *restrict data=lean_sarray_cptr(c->dense);
    const uint8_t *slots=lean_sarray_cptr(c->slots);
    const uint8_t *metadata=lean_sarray_cptr(c->delayed_meta);
    uint64_t charged=first;
    for(uint64_t col=first;col<c->columns && col<=*last;++col) {
        if(col>=charged) {
            uint64_t stop=col+64<*last+1?col+64:*last+1;
            if(!matrix_work(c,stop-col)) return 0;
            charged=stop;
        }
        uint64_t a;memcpy(&a,data+(size_t)col*8,8);a&=UINT64_C(1);
        memcpy(data+(size_t)col*8,&a,8);
        if(!a) continue;
        uint64_t slot=matrix_read(slots+(size_t)col*4,4);
        if(!slot) {if(!*leading) *leading=col+1;continue;}
        delayed_pivot pivot;
        memcpy(&pivot,metadata+(size_t)(slot-1)*sizeof(pivot),sizeof(pivot));
        if(pivot.end>*last) *last=pivot.end;
        if(pivot.sugar>*sugar) *sugar=pivot.sugar;
        if(!matrix_work(c,pivot.size)) return 0;
        HEX_GROEBNER_SPARSE_UPDATE();
        for(uint64_t j=1;j<pivot.size;++j) {
            uint64_t k=matrix_read(pivot.columns+(size_t)j*4,4);
            uint64_t value;memcpy(&value,data+(size_t)k*8,8);value^=UINT64_C(1);
            memcpy(data+(size_t)k*8,&value,8);
        }
        uint64_t zero=0;memcpy(data+(size_t)col*8,&zero,8);
        ++c->stats[6];
    }
    return 1;
}

#endif
