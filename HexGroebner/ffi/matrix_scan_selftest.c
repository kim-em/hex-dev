/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
/* Selftests must execute their assertions even with external release flags. */
#ifdef NDEBUG
#undef NDEBUG
#endif
#include "matrix_simd.h"
#if HEX_GROEBNER_AVX2 && (defined(__unix__) || defined(__APPLE__))
#include <sys/mman.h>
#include <unistd.h>
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
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
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,entry,128,p,f,inverse,4)==8);
    assert(memcmp(expected,dense,sizeof(dense))==0);
    for(unsigned bad=0;bad<8;++bad) {
        uint32_t saved=coeff[bad];coeff[bad]=p;
        memcpy(expected,dense,sizeof(dense));
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse,4)==0);
        assert(memcmp(expected,dense,sizeof(dense))==0);coeff[bad]=saved;
        saved=dense[cols[bad]];dense[cols[bad]]=p;
        memcpy(expected,dense,sizeof(dense));
        assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse,4)==0);
        assert(memcmp(expected,dense,sizeof(dense))==0);dense[cols[bad]]=saved;
    }
    uint32_t saved=cols[4];cols[4]=cols[3];memcpy(expected,dense,sizeof(dense));
    assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse,4)==0);
    assert(memcmp(expected,dense,sizeof(dense))==0);cols[4]=saved;
    cols[7]=UINT32_MAX;
    assert(hex_scan8((uint8_t*)dense,(uint8_t*)cols,(uint8_t*)coeff,0,128,p,f,inverse,4)==0);
}
/* Exhaust all odd one-byte moduli, factors and nonzero coefficients. Each
   vector checks subtraction at zero, p-1, the product and adjacent residues.
   Contiguous and gathered paths share this exact arithmetic. */
__attribute__((target("avx2")))
static void check_u8_products(void) {
    uint32_t columns[8]={0,1,2,3,4,5,6,7};
    uint8_t dense[8],coefficients[8],expected[8];
    for(uint32_t p=3;p<=255;p+=2) {
        uint32_t reciprocal=(uint32_t)(UINT64_C(4294967296)/p);
        for(uint32_t factor=0;factor<p;++factor) {
            for(uint32_t b=1;b<p;++b) {
                uint32_t product=factor*b%p;
                for(unsigned i=0;i<8;++i) {
                    uint32_t a=i%4==0?0:i%4==1?p-1:i%4==2?product:(product+1)%p;
                    coefficients[i]=(uint8_t)b;dense[i]=(uint8_t)a;
                    expected[i]=(uint8_t)((a+p-product)%p);
                }
                assert(hex_scan8(dense,(const uint8_t*)columns,coefficients,0,8,
                    p,factor,reciprocal,1)==8);
                assert(memcmp(dense,expected,sizeof(dense))==0);
            }
        }
    }
}

#if defined(__unix__) || defined(__APPLE__)
struct guarded_buffer { uint8_t *mapping,*data;size_t page; };
static struct guarded_buffer guarded(size_t bytes,unsigned at_end) {
    long length=sysconf(_SC_PAGESIZE);assert(length>0 && bytes<=(size_t)length);
    size_t page=(size_t)length;
    uint8_t *mapping=mmap(NULL,3*page,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    assert(mapping!=MAP_FAILED);
    assert(mprotect(mapping+page,page,PROT_READ|PROT_WRITE)==0);
    return (struct guarded_buffer){mapping,at_end?mapping+2*page-bytes:mapping+page,page};
}
static void release(struct guarded_buffer buffer) {
    assert(munmap(buffer.mapping,3*buffer.page)==0);
}
__attribute__((target("avx2")))
static void check_guard_pages(uint32_t p,unsigned stride,unsigned at_end) {
    struct guarded_buffer d=guarded(128*4,at_end),c=guarded(16*4,at_end),v=guarded(16*4,at_end);
    uint32_t columns[16],coefficients[16],dense[128],expected[128];
    for(unsigned i=0;i<128;++i) dense[i]=i%3?p-1:0;
    for(unsigned i=0;i<16;++i) {
        columns[i]=127-(15-i)*stride;coefficients[i]=i%2?p-1:1;
    }
    memcpy(expected,dense,sizeof(dense));
    uint32_t factor=p-1,f=(uint32_t)(((uint64_t)factor<<32)%p),inverse=hex_mont32_inverse(p);
    for(unsigned i=0;i<16;++i)
        expected[columns[i]]=(uint32_t)((expected[columns[i]]+(uint64_t)p-
            (uint64_t)factor*coefficients[i]%p)%p);
    memcpy(d.data,dense,sizeof(dense));memcpy(c.data,columns,sizeof(columns));
    memcpy(v.data,coefficients,sizeof(coefficients));
    assert(hex_scan8(d.data,c.data,v.data,0,128,p,f,inverse,4)==8);
    assert(hex_scan8(d.data,c.data,v.data,8,128,p,f,inverse,4)==8);
    assert(memcmp(d.data,expected,sizeof(expected))==0);
    /* Every source ends at its guard page; the last valid dense column is 127.
       Invalid vectors must return before any gather or store. */
    columns[15]=128;memcpy(c.data,columns,sizeof(columns));
    assert(hex_scan8(d.data,c.data,v.data,8,128,p,f,inverse,4)==0);
    assert(memcmp(d.data,expected,sizeof(expected))==0);
    columns[15]=127;columns[12]=UINT32_MAX;memcpy(c.data,columns,sizeof(columns));
    assert(hex_scan8(d.data,c.data,v.data,8,128,p,f,inverse,4)==0);
    assert(memcmp(d.data,expected,sizeof(expected))==0);
    columns[12]=127-3*stride;coefficients[15]=p;
    memcpy(c.data,columns,sizeof(columns));memcpy(v.data,coefficients,sizeof(coefficients));
    assert(hex_scan8(d.data,c.data,v.data,8,128,p,f,inverse,4)==0);
    assert(memcmp(d.data,expected,sizeof(expected))==0);
    release(d);release(c);release(v);
}
static unsigned width(uint32_t p) {return p<=256?1:p<=65536?2:4;}
static uint32_t read_value(const uint8_t *b,unsigned w,unsigned i) {uint32_t v=0;memcpy(&v,b+(size_t)i*w,w);return v;}
static void write_value(uint8_t *b,unsigned w,unsigned i,uint32_t v) {memcpy(b+(size_t)i*w,&v,w);}
__attribute__((target("avx2")))
static void check_narrow(uint32_t p,uint32_t factor,unsigned stride,unsigned padding,unsigned end) {
 unsigned w=width(p);struct guarded_buffer d=guarded(128*w,end),c=guarded(16*4,end),v=guarded(16*w,end);
 uint8_t expected[128*4],before[128*4];uint32_t columns[16],coefficients[16];
 for(unsigned i=0;i<128;++i) write_value(d.data,w,i,i%3==0?0:i%3==1?p-1:random32()%p);
 for(unsigned i=0;i<16;++i) {columns[i]=127-padding-(15-i)*stride;coefficients[i]=i%3==0?1:i%3==1?p-1:random32()%(p-1)+1;write_value(v.data,w,i,coefficients[i]);}
 memcpy(c.data,columns,sizeof(columns));memcpy(expected,d.data,128*w);
 uint32_t inverse=w<4?(uint32_t)(UINT64_C(4294967296)/p):hex_mont32_inverse(p);
 uint32_t f=w<4?factor:(uint32_t)(((uint64_t)factor<<32)%p);
 if(w==4) assert((uint32_t)(inverse*p)==UINT32_MAX);
 for(unsigned entry=0;entry<16;entry+=8) {
  memcpy(before,d.data,128*w);
  unsigned n=hex_scan8(d.data,c.data,v.data,entry,128,p,f,inverse,w);
  unsigned should= (stride==1 || 128-columns[entry+7]>=4/w)?8:0;
  assert(n==should);
  if(n) for(unsigned i=entry;i<entry+8;++i) {
   uint32_t a=read_value(expected,w,columns[i]);uint64_t product=(uint64_t)factor*coefficients[i]%p;
   write_value(expected,w,columns[i],(uint32_t)((a+(uint64_t)p-product)%p));
  } else assert(memcmp(before,d.data,128*w)==0);
  assert(memcmp(expected,d.data,128*w)==0);
 }
 for(unsigned bad=0;bad<8;++bad) {
  uint32_t saved=coefficients[bad];write_value(v.data,w,bad,p);memcpy(before,d.data,128*w);
  assert(hex_scan8(d.data,c.data,v.data,0,128,p,f,inverse,w)==0);assert(memcmp(before,d.data,128*w)==0);write_value(v.data,w,bad,saved);
  saved=read_value(d.data,w,columns[bad]);write_value(d.data,w,columns[bad],p);memcpy(before,d.data,128*w);
  assert(hex_scan8(d.data,c.data,v.data,0,128,p,f,inverse,w)==0);assert(memcmp(before,d.data,128*w)==0);write_value(d.data,w,columns[bad],saved);
 }
 columns[15]=128;memcpy(c.data,columns,sizeof(columns));memcpy(before,d.data,128*w);
 assert(hex_scan8(d.data,c.data,v.data,8,128,p,f,inverse,w)==0);assert(memcmp(before,d.data,128*w)==0);
 release(d);release(c);release(v);
}
#endif

#endif
int main(void) {
#if HEX_GROEBNER_AVX2
    if(hex_avx2_available()) {
        check_u8_products();
        puts("exhaustive odd one-byte modulus products: passed");
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
#if defined(__unix__) || defined(__APPLE__)
        for(unsigned stride=1;stride<=8;++stride) {
            for(unsigned at_end=0;at_end<2;++at_end) {
                check_guard_pages(65537,stride,at_end);
                check_guard_pages(2147483647,stride,at_end);
            }
        }
        uint32_t narrow[]={3,5,127,251,255,257,32003,65521,65535};
        for(unsigned i=0;i<sizeof(narrow)/sizeof(narrow[0]);++i) {
            uint32_t p=narrow[i];
            for(unsigned stride=1;stride<=8;++stride) {
                for(unsigned padding=0;padding<=4;++padding) {
                    for(unsigned at_end=0;at_end<2;++at_end) {
                        check_narrow(p,0,stride,padding,at_end);
                        check_narrow(p,1,stride,padding,at_end);
                        check_narrow(p,p-1,stride,padding,at_end);
                        check_narrow(p,random32()%p,stride,padding,at_end);
                    }
                }
            }
        }
        puts("SIMD guard pages: start/end boundaries, contiguous/strided vectors and invalid-prefix preservation passed");
#endif
        puts("exact AVX2 Barrett/Montgomery updates: all widths, boundary fields and invalid-prefix fallback passed");
        return 0;
    }
#endif
#if !defined(HEX_GROEBNER_NO_AVX2)
    const char *required=getenv("HEX_GROEBNER_REQUIRE_AVX2");
    if(required && strcmp(required,"1")==0) {
        fputs("AVX2 coverage required but unavailable\n",stderr);return 1;
    }
#endif
    puts("AVX2 unavailable; scalar fallback selected");
    return 0;
}
