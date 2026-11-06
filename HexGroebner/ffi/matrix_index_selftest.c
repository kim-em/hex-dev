/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "matrix_eliminate.c"
static __attribute__((noinline)) uint32_t checked_column(const uint8_t *p) {
 return sparse_column(p);
}
int main(void) {
 uint32_t state=1;uint64_t checks=0;
 for(unsigned trial=0;trial<4096;++trial) {
  state=UINT32_C(1664525)*state+UINT32_C(1013904223);
  uint32_t values[]={0,1,255,256,65535,65536,1048575,UINT32_C(2147483648),UINT32_MAX,state};
  for(unsigned v=0;v<sizeof(values)/sizeof(values[0]);++v)for(unsigned offset=0;offset<8;++offset) {
   uint8_t *bytes=malloc(offset+4);assert(bytes);
   memset(bytes,0xa5,offset+4);uint32_t expected=values[v];
   for(unsigned j=0;j<4;++j)bytes[offset+j]=(uint8_t)(expected>>(j*8));
   assert(matrix_read(bytes+offset,4)==expected);
   assert(checked_column(bytes+offset)==expected);++checks;free(bytes);
  }
 }
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
 const char *mode="native";
#else
 const char *mode="bytewise";
#endif
 printf("PASS %s %llu aligned/unaligned little-endian index boundaries\n",mode,(unsigned long long)checks);return 0;
}
