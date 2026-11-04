/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#ifdef NDEBUG
#undef NDEBUG
#endif
static unsigned packets=0,widths=0;
#define HEX_GROEBNER_AVX512_USED(w,c) (++packets,widths|=1u<<(2*((w)==1?0:(w)==2?1:2)+!(c)))
#include "matrix_avx512.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#if HEX_GROEBNER_AVX512
#include <sys/mman.h>
#include <unistd.h>
static uint64_t rng=UINT64_C(0x1492983957290541);
static uint32_t random32(void) {
    rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return (uint32_t)rng;
}
static void put(uint8_t *p,unsigned w,uint32_t v) {memcpy(p,&v,w);}
static uint32_t get(const uint8_t *p,unsigned w) {uint32_t v=0;memcpy(&v,p,w);return v;}
__attribute__((target("avx512f,avx512dq,avx512bw,avx512vl")))
static void check(uint32_t p,unsigned stride,unsigned offset,unsigned at_end,unsigned padding,uint32_t factor) {
    unsigned w=p<=256?1:p<=65536?2:4,n=offset+15*stride+1+padding,entries=offset+16;
    long page=sysconf(_SC_PAGESIZE);assert(page>0 && n*w<(unsigned)page);
    uint8_t *maps[3],*buffers[3];size_t sizes[]={n*w,entries*4,entries*w};
    for(unsigned i=0;i<3;++i) {
        maps[i]=mmap(NULL,3*(size_t)page,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
        assert(maps[i]!=MAP_FAILED);assert(mprotect(maps[i]+page,(size_t)page,PROT_READ|PROT_WRITE)==0);
        buffers[i]=maps[i]+(at_end?2*(size_t)page-sizes[i]:(size_t)page);
    }
    uint8_t *d=buffers[0],*c=buffers[1],*b=buffers[2],expected[1024],saved[1024];
    uint32_t mult=w<4?factor:(uint32_t)(((uint64_t)factor<<32)%p);
    uint32_t reduction=w<4?(uint32_t)(UINT64_C(4294967296)/p):hex_mont32_inverse(p);
    for(unsigned i=0;i<n;++i) put(d+i*w,w,i%3==0?0:i%3==1?p-1:random32()%p);
    for(unsigned i=0;i<offset;++i) {put(c+i*4,4,i);put(b+i*w,w,1);}
    memcpy(expected,d,n*w);
    for(unsigned i=0;i<16;++i) {
        uint32_t col=offset+i*stride,coefficient=i%3==0?1:i%3==1?p-1:random32()%(p-1)+1;
        put(c+(offset+i)*4,4,col);put(b+(offset+i)*w,w,coefficient);
        put(expected+col*w,w,(uint32_t)((get(d+col*w,w)+(uint64_t)p-(uint64_t)factor*coefficient%p)%p));
    }
    unsigned mode=p==INT32_MAX;
    memcpy(saved,d,n*w);
    unsigned accepted=stride==1 || w==4 || padding+1>=4/w;
    assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==(accepted?16:0));
    assert(memcmp(d,accepted?expected:saved,n*w)==0);
    if(accepted) {
#define REFUSE() do {memcpy(saved,d,n*w);assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==0);assert(memcmp(d,saved,n*w)==0);}while(0)
        for(unsigned i=0;i<16;++i) {
            uint32_t col=get(c+(offset+i)*4,4),v=get(b+(offset+i)*w,w);
            put(b+(offset+i)*w,w,0);REFUSE();
            put(b+(offset+i)*w,w,p);REFUSE();
            if(w==4) {put(b+(offset+i)*w,w,UINT32_MAX);REFUSE();}
            put(b+(offset+i)*w,w,v);
            v=get(d+col*w,w);put(d+col*w,w,p);REFUSE();
            if(w==4) {put(d+col*w,w,UINT32_MAX);REFUSE();}
            put(d+col*w,w,v);
            put(c+(offset+i)*4,4,i?get(c+(offset+i-1)*4,4):UINT32_MAX);REFUSE();
            put(c+(offset+i)*4,4,col);
        }
        uint32_t last=get(c+(entries-1)*4,4);
        put(c+(entries-1)*4,4,n);REFUSE();put(c+(entries-1)*4,4,last);
        if(offset) {put(c+(offset-1)*4,4,offset);REFUSE();put(c+(offset-1)*4,4,offset-1);}
        if(!mode) {mode=1;REFUSE();mode=0;}
#undef REFUSE
    }
    for(unsigned i=0;i<3;++i) assert(munmap(maps[i],3*(size_t)page)==0);
}
/* Exhaust the one-byte arithmetic independently of the guard-page geometry.
   Each product checks zero, p-1, the exact residue and an adjacent residue. */
__attribute__((target("avx512f,avx512dq,avx512bw,avx512vl")))
static void exhaustive(void) {
    uint32_t columns[16];uint8_t dense[64],coefficients[16],expected[64];
    for(uint32_t p=3;p<=255;p+=2) for(uint32_t factor=0;factor<p;++factor)
        for(uint32_t coefficient=1;coefficient<p;++coefficient) {
            unsigned stride=(factor+coefficient)%2?1:3;uint32_t product=factor*coefficient%p;
            memset(dense,0,sizeof(dense));memset(expected,0,sizeof(expected));
            for(unsigned i=0;i<16;++i) {
                uint32_t value=i%4==0?0:i%4==1?p-1:i%4==2?product:(product+1)%p;
                columns[i]=i*stride;coefficients[i]=(uint8_t)coefficient;dense[i*stride]=(uint8_t)value;
                expected[i*stride]=(uint8_t)((value+p-product)%p);
            }
            assert(hex_scan16_mode(dense,(uint8_t*)columns,coefficients,0,64,p,factor,
                (uint32_t)(UINT64_C(4294967296)/p),1,0)==16);
            assert(memcmp(dense,expected,sizeof(dense))==0);
        }
}
#endif
int main(void) {
#if HEX_GROEBNER_AVX512
    if(hex_avx512_available()) {
        uint32_t fields[]={3,251,257,32003,65521,65537,1073741789,2147483629,INT32_MAX};
        for(unsigned k=0;k<sizeof(fields)/sizeof(fields[0]);++k) {
            uint32_t p=fields[k],factors[]={0,1,2,p/2,p/2+1,p-1};
            for(unsigned trial=0;trial<128;++trial) for(unsigned f=0;f<6;++f)
                check(p,trial%2?1:7,(trial/2)%2,(trial/4)%2,(trial/8)%5,factors[f]);
        }
        for(unsigned i=0;i<128;++i) {
            uint32_t p=(random32()&INT32_MAX)|3u;
            check(p,i%2?1:7,(i/2)%2,(i/4)%2,(i/8)%5,random32()%p);
        }
        exhaustive();assert(widths==63);
        printf("AVX-512 exact packets: %u; all six width/layout paths\n",packets);
        return 0;
    }
#endif
#if !defined(HEX_GROEBNER_NO_AVX2) && !defined(HEX_GROEBNER_NO_AVX512)
    const char *required=getenv("HEX_GROEBNER_REQUIRE_AVX512");
    if(required && strcmp(required,"1")==0) {fputs("AVX-512 coverage required but unavailable\n",stderr);return 1;}
#endif
    (void)packets;(void)widths;puts("AVX-512 unavailable or disabled; portable fallback retained");return 0;
}
