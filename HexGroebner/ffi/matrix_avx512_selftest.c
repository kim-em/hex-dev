/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#ifdef NDEBUG
#undef NDEBUG
#endif
static unsigned packets=0;
#define HEX_GROEBNER_AVX512_USED() (++packets)
#include "matrix_avx512.h"
#include <assert.h>
#include <stdio.h>
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
static void check(uint32_t p,unsigned stride,unsigned offset,unsigned at_end) {
    unsigned w=p<=256?1:p<=65536?2:4,n=16*stride+4,entries=offset+16;
    long page=sysconf(_SC_PAGESIZE);assert(page>0 && n*w<(unsigned)page);
    uint8_t *maps[3],*buffers[3];size_t sizes[]={n*w,entries*4,entries*w};
    for(unsigned i=0;i<3;++i) {
        maps[i]=mmap(NULL,3*(size_t)page,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
        assert(maps[i]!=MAP_FAILED);assert(mprotect(maps[i]+page,(size_t)page,PROT_READ|PROT_WRITE)==0);
        buffers[i]=maps[i]+(at_end?2*(size_t)page-sizes[i]:(size_t)page);
    }
    uint8_t *d=buffers[0],*c=buffers[1],*b=buffers[2],expected[1024],saved[1024];
    uint32_t factor=random32()%p,mult=w<4?factor:(uint32_t)(((uint64_t)factor<<32)%p);
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
    assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==16);
    assert(memcmp(d,expected,n*w)==0);
    /* Every invalid lane declines without mutating any byte. */
    for(unsigned i=0;i<16;++i) {
        uint32_t col=get(c+(offset+i)*4,4),v=get(b+(offset+i)*w,w);
        put(b+(offset+i)*w,w,p);memcpy(saved,d,n*w);
        assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==0);
        assert(memcmp(d,saved,n*w)==0);put(b+(offset+i)*w,w,v);
        v=get(d+col*w,w);put(d+col*w,w,p);memcpy(saved,d,n*w);
        assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==0);
        assert(memcmp(d,saved,n*w)==0);put(d+col*w,w,v);
        uint32_t invalid=i?get(c+(offset+i-1)*4,4):UINT32_MAX;
        put(c+(offset+i)*4,4,invalid);memcpy(saved,d,n*w);
        assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==0);
        assert(memcmp(d,saved,n*w)==0);put(c+(offset+i)*4,4,col);
    }
    if(w<4 && stride>1) {
        /* A final narrow cell has no complete four-byte gather. Decline
           before the guard page and leave even the valid prefix unchanged. */
        put(c+(entries-1)*4,4,n-1);memcpy(saved,d,n*w);
        assert(hex_scan16_mode(d,c,b,offset,n,p,mult,reduction,w,mode)==0);
        assert(memcmp(d,saved,n*w)==0);
    }
    for(unsigned i=0;i<3;++i) assert(munmap(maps[i],3*(size_t)page)==0);
}
#endif
int main(void) {
#if HEX_GROEBNER_AVX512
    if(hex_avx512_available()) {
        uint32_t fields[]={3,251,257,32003,65521,65537,1073741789,2147483629,INT32_MAX};
        for(unsigned k=0;k<sizeof(fields)/sizeof(fields[0]);++k)
            for(unsigned trial=0;trial<128;++trial)
                check(fields[k],trial%2?1:7,(trial/2)%2,(trial/4)%2);
        assert(packets==1152);printf("AVX-512 exact packets: %u\n",packets);
    } else puts("AVX-512 unavailable; portable fallback retained");
#else
    (void)packets;puts("AVX-512 disabled; portable fallback retained");
#endif
    return 0;
}
