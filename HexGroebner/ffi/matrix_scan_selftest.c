/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include "matrix_simd.h"
#include <assert.h>
#include <stdio.h>
#if HEX_GROEBNER_AVX2
static uint64_t random_state=UINT64_C(0x6390743202398481);
static uint32_t random32(void) {
    random_state^=random_state<<13;random_state^=random_state>>7;random_state^=random_state<<17;
    return (uint32_t)random_state;
}
__attribute__((target("avx2")))
static void check(uint32_t p,uint32_t factor) {
    uint32_t inverse=hex_mont32_inverse(p);
    assert((uint32_t)(p*inverse)==UINT32_MAX);
    uint32_t f=(uint32_t)(((uint64_t)factor<<32)%p);
    uint32_t cols[16],coeff[16],dense[128],expected[128];
    for(unsigned k=0;k<128;++k) dense[k]=k%3==0?0:k%3==1?p-1:random32()%p;
    unsigned stride=(random32()%3==0)?1:7;
    for(unsigned k=0;k<16;++k) {cols[k]=k*stride;coeff[k]=k%3==0?1:k%3==1?p-1:random32()%(p-1)+1;}
    memcpy(expected,dense,sizeof(dense));
    for(unsigned k=0;k<16;++k) {
        uint64_t product=(uint64_t)factor*coeff[k]%p;
        expected[cols[k]]=(uint32_t)((expected[cols[k]]+(uint64_t)p-product)%p);
    }
    for(unsigned entry=0;entry<16;entry+=8)
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,entry,128,p,f,inverse)==8);
    assert(memcmp(expected,dense,sizeof(dense))==0);
    for(unsigned bad=0;bad<8;++bad) {
        uint32_t saved=coeff[bad];coeff[bad]=p;
        memcpy(expected,dense,sizeof(dense));
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse)==0);
        assert(memcmp(expected,dense,sizeof(dense))==0);coeff[bad]=saved;
        saved=dense[cols[bad]];dense[cols[bad]]=p;
        memcpy(expected,dense,sizeof(dense));
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse)==0);
        assert(memcmp(expected,dense,sizeof(dense))==0);dense[cols[bad]]=saved;
    }
    uint32_t saved=cols[4];cols[4]=cols[3];memcpy(expected,dense,sizeof(dense));
    assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse)==0);
    assert(memcmp(expected,dense,sizeof(dense))==0);cols[4]=saved;
    cols[7]=UINT32_MAX;
    assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse)==0);
}
#endif
int main(void) {
#if HEX_GROEBNER_AVX2
    if(hex_avx2_available()) {
        uint32_t fields[]={65537,65539,131071,1000003,1000000007,2147483629,2147483647};
        for(unsigned i=0;i<sizeof(fields)/sizeof(fields[0]);++i) {
            uint32_t p=fields[i];
            for(unsigned k=0;k<1000;++k) check(p,random32()%p);
            check(p,0);check(p,1);check(p,p-1);
        }
        for(unsigned k=0;k<10000;++k) {
            uint32_t p=(random32()&UINT32_C(0x7fffffff))|UINT32_C(0x10001);
            check(p,random32()%p);
        }
        puts("exact AVX2 Montgomery updates: residues, boundary fields and invalid-prefix fallback passed");
        return 0;
    }
#endif
    puts("AVX2 unavailable; scalar fallback selected");
    return 0;
}
