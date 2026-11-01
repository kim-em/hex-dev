/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#define HEX_GROEBNER_NO_LEAN
#define HEX_GROEBNER_TRIE_SELFTEST
#include "trie_lookup.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(__linux__)
#include <sys/mman.h>
#include <unistd.h>
#endif

static void require(int condition,const char *message) {
    if(!condition) {fprintf(stderr,"trie_selftest: %s\n",message);exit(1);}
}
static void put(uint8_t *out,unsigned width,uint64_t value) {
    for(unsigned i=0;i<width;++i) out[i]=(uint8_t)(value>>(8*i));
}
struct buffer {uint8_t *data,*mapping;size_t size,mapped;};
static struct buffer buffer_new(size_t size,unsigned end) {
    struct buffer out={0};out.size=size;
#if defined(__linux__)
    size_t page=(size_t)sysconf(_SC_PAGESIZE),body=((size+page-1)/page)*page;
    if(!body) body=page;
    out.mapped=body+2*page;
    out.mapping=mmap(NULL,out.mapped,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    require(out.mapping!=MAP_FAILED,"mmap");
    require(!mprotect(out.mapping+page,body,PROT_READ|PROT_WRITE),"mprotect write");
    out.data=out.mapping+page+(end?body-size:0);
#else
    (void)end;out.mapping=calloc(size+1,1);require(out.mapping!=NULL,"allocation");out.data=out.mapping;
#endif
    memset(out.data,0,size);return out;
}
static void readonly(struct buffer *b) {
#if defined(__linux__)
    size_t page=(size_t)sysconf(_SC_PAGESIZE);
    require(!mprotect(b->mapping+page,b->mapped-2*page,PROT_READ),"mprotect read");
#else
    (void)b;
#endif
}
static void release(struct buffer b) {
#if defined(__linux__)
    require(!munmap(b.mapping,b.mapped),"munmap");
#else
    free(b.mapping);
#endif
}
/* A maximum-size root with 2047 leaf children reaches the largest stack and
   every last byte of all borrowed inputs. The independent answer is the last
   leaf, with the unique least priority. Both edge placements catch
   overreads and underreads; read protection catches writes to borrowed data. */
static void bush(unsigned width,unsigned end) {
    const unsigned n=2048;const size_t edge_bytes=(n-1)*8;
    struct buffer nodes=buffer_new(n*24,end),edges=buffer_new(edge_bytes,end);
    struct buffer arena=buffer_new(n*width,end),metadata=buffer_new(n*24,end);
    put(nodes.data+8,4,n-1);
    uint64_t maximum=width==1?255:width==2?65535:UINT32_MAX;
    for(unsigned i=1;i<n;++i) {
        uint8_t *record=nodes.data+i*24;
        put(record,4,1);put(record+4,4,n-1);put(record+12,4,i+1);
        put(record+16,4,n-i);put(record+20,4,i);
        put(edges.data+(i-1)*8,4,i%251);put(edges.data+(i-1)*8+4,4,i);
        put(arena.data+i*width,width,maximum);
    }
    require(trie_valid(1,nodes.data,nodes.size,edges.data,edges.size,n-1),"valid full bush");
    uint8_t *leaf=nodes.data+(n-1)*24;
    uint64_t priority=trie_read(leaf+16,4);
    put(leaf+16,4,0);
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size,n-1),"zero leaf priority");
    put(leaf+16,4,priority);
    put(leaf+20,4,n);
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size,n-1),"leading beyond maximum");
    put(leaf+20,4,n-1);
    put(nodes.data+24+4,4,0);
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size,n-1),"nonroot cursor mismatch");
    put(nodes.data+24+4,4,n-1);
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size-8,n-1),"aligned edge-count mismatch");

    readonly(&nodes);readonly(&edges);readonly(&arena);readonly(&metadata);
    struct trie_result r=trie_lookup(1,n-1,width,n,n-1,arena.data,arena.size,
        metadata.data,metadata.size,nodes.data,nodes.size,edges.data,edges.size,4095);
    require(r.status==1 && r.work==4095 && r.key==n,"complete maximum lookup");
    const uint64_t allowances[]={0,1,2047,2048,4094};
    for(unsigned i=0;i<sizeof(allowances)/sizeof(allowances[0]);++i) {
        uint64_t budget=allowances[i];r=trie_lookup(1,n-1,width,n,n-1,
            arena.data,arena.size,metadata.data,metadata.size,nodes.data,nodes.size,
            edges.data,edges.size,budget);
        require(r.status==2 && r.work==(budget==0?0:budget<2048?1:budget),"exact exhaustion prefix");
    }
    r=trie_lookup(1,n-1,width,n,n-1,arena.data,arena.size-1,
        metadata.data,metadata.size,nodes.data,nodes.size,edges.data,edges.size,UINT64_MAX);
    require(r.status==3 && !r.work,"short arena rejected before reads");
    r=trie_lookup(1,n-1,width,n,n-1,arena.data,arena.size,
        metadata.data,metadata.size-1,nodes.data,nodes.size,edges.data,edges.size,UINT64_MAX);
    require(r.status==3 && !r.work,"short metadata rejected before reads");
    require(!trie_valid(1,nodes.data,nodes.size-1,edges.data,edges.size,n-1),"short node record");
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size-1,n-1),"short edge record");
    release(nodes);release(edges);release(arena);release(metadata);
}
static void constant(unsigned end) {
    struct buffer nodes=buffer_new(24,end),edges=buffer_new(0,end);
    struct buffer arena=buffer_new(0,end),metadata=buffer_new(24,end);
    put(nodes.data+12,4,1);put(nodes.data+16,4,1);
    require(trie_valid(0,nodes.data,24,edges.data,0,0),"zero-variable tree");
    readonly(&nodes);readonly(&edges);readonly(&arena);readonly(&metadata);
    struct trie_result r=trie_lookup(0,0,1,1,0,arena.data,0,metadata.data,24,
        nodes.data,24,edges.data,0,1);
    require(r.status==1 && r.key==1 && r.work==1,"zero-variable lookup");
    release(nodes);release(edges);release(arena);release(metadata);
}
/* Removing the node-limit guard from the validator makes the final child
   overrun its fixed parents array; ASan must catch that mutation. */
static void oversized(unsigned end) {
    const unsigned n=2049;
    struct buffer nodes=buffer_new(n*24,end),edges=buffer_new((n-1)*8,end);
    put(nodes.data+8,4,n-1);
    for(unsigned i=1;i<n;++i) {
        uint8_t *record=nodes.data+i*24;
        put(record,4,1);put(record+4,4,n-1);
        put(record+12,4,i);put(record+16,4,i);
        put(edges.data+(i-1)*8+4,4,i);
    }
    readonly(&nodes);readonly(&edges);
    require(!trie_valid(1,nodes.data,nodes.size,edges.data,edges.size,0),"2049-node tree rejected");
    release(nodes);release(edges);
}
int main(void) {
    for(unsigned end=0;end<2;++end) {
        constant(end);
        oversized(end);
        for(unsigned width=1;width<=4;width*=2) bush(width,end);
    }
    puts("trie_selftest: maximum tree/stack, read-only guard pages and exact budgets passed");
    return 0;
}
