/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_TRIE_LOOKUP_H
#define HEX_GROEBNER_TRIE_LOOKUP_H

#if !defined(HEX_GROEBNER_NO_LEAN) || defined(HEX_GROEBNER_TRIE_SELFTEST)
#include <stdint.h>
#include <stddef.h>

static inline uint64_t trie_read(const uint8_t *p,unsigned width) {
    uint64_t out=0;
    for(unsigned i=0;i<width;++i) out|=(uint64_t)p[i]<<(i*8);
    return out;
}

struct trie_result {uint32_t key;uint64_t work;uint8_t status;};
static inline struct trie_result trie_decline(void) {return (struct trie_result){0,0,3};}

/* A View carries the portable tree-validation proof. Each nonroot has one
   parent, depths increase, and there are at most 2048 nodes and 2047 edges.
   The fixed stack and work/edge guards additionally bound malformed raw probes.
   No storage is modified and no pointer outlives the call. */
static struct trie_result trie_lookup(uint64_t arity,uint64_t max_leading,unsigned w,
        uint64_t count,uint64_t query,const uint8_t *arena,size_t arena_bytes,
        const uint8_t *metadata,size_t metadata_bytes,
        const uint8_t *nodes,size_t node_bytes,const uint8_t *edges,size_t edge_bytes,
        uint64_t remaining) {
    uint64_t n=node_bytes/24;
    if(arity>4096 || (w!=1 && w!=2 && w!=4) || !n || n>2048 || node_bytes%24 ||
       edge_bytes!=(n-1)*8 || count>UINT32_MAX || query>=count || max_leading>=count ||
       arena_bytes!=count*arity*w || metadata_bytes!=count*24) return trie_decline();
    uint32_t pending[2048],sp=1;
    pending[0]=0;
    uint32_t best=0,best_size=0,best_leading=0;
    uint64_t work=0,query_degree=trie_read(metadata+query*24,8);
    uint64_t query_mask=trie_read(metadata+query*24+8,8);
    for(uint64_t visited=0;visited<n && sp;++visited) {
        uint32_t node=pending[--sp];
        if(node>=n) return trie_decline();
        const uint8_t *record=nodes+(size_t)node*24;
        uint32_t depth=(uint32_t)trie_read(record,4);
        if(work+1>remaining) return (struct trie_result){best,work,2};
        if(work>=4096) return trie_decline();
        ++work;
        if(depth==arity) {
            uint32_t key=(uint32_t)trie_read(record+12,4);
            if(key) {
                uint32_t terms=(uint32_t)trie_read(record+16,4);
                uint32_t leading=(uint32_t)trie_read(record+20,4);
                if(leading>=count || !terms) return trie_decline();
                uint64_t degree=trie_read(metadata+(uint64_t)leading*24,8);
                uint64_t mask=trie_read(metadata+(uint64_t)leading*24+8,8);
                if(degree<=query_degree && (mask&query_mask)==mask &&
                   (!best || terms<best_size || (terms==best_size &&
                    degree>trie_read(metadata+(uint64_t)best_leading*24,8)))) {
                    best=key;best_size=terms;best_leading=leading;
                }
            }
        } else {
            uint32_t start=(uint32_t)trie_read(record+4,4),size=(uint32_t)trie_read(record+8,4);
            if(depth>arity || (uint64_t)start+size>edge_bytes/8) return trie_decline();
            if(work+size>remaining) return (struct trie_result){best,work,2};
            if(size>4096-work) return trie_decline();
            work+=size;
            uint64_t exponent=trie_read(arena+(query*arity+depth)*w,w);
            for(uint32_t k=0;k<size;++k) {
                const uint8_t *edge=edges+((uint64_t)start+k)*8;
                if(trie_read(edge,4)<=exponent) {
                    uint32_t child=(uint32_t)trie_read(edge+4,4);
                    if(child>=n || sp>=2048) return trie_decline();
                    pending[sp++]=child;
                }
            }
        }
    }
    return (struct trie_result){best,work,1};
}

#ifndef HEX_GROEBNER_NO_LEAN
LEAN_EXPORT lean_obj_res lean_hex_groebner_lookup_trie(b_lean_obj_arg view,uint8_t width,
        uint64_t count,uint64_t query,b_lean_obj_arg arena,b_lean_obj_arg metadata,uint64_t remaining) {
    lean_object *nodes=lean_ctor_get(view,1),*edges=lean_ctor_get(view,2);
    uint64_t arity=lean_unbox(lean_ctor_get(view,0));
    uint64_t max_leading=lean_ctor_get_uint64(view,3*sizeof(void*));
    struct trie_result result=trie_lookup(arity,max_leading,width,count,query,
        lean_sarray_cptr(arena),lean_sarray_size(arena),lean_sarray_cptr(metadata),lean_sarray_size(metadata),
        lean_sarray_cptr(nodes),lean_sarray_size(nodes),lean_sarray_cptr(edges),lean_sarray_size(edges),remaining);
    lean_object *reducer=lean_box(0);
    if(result.key) {
        reducer=lean_alloc_ctor(1,1,0);
        lean_ctor_set(reducer,0,lean_uint64_to_nat((uint64_t)result.key-1));
    }
    lean_object *out=lean_alloc_ctor(0,2,1);
    lean_ctor_set(out,0,reducer);lean_ctor_set(out,1,lean_uint64_to_nat(result.work));
    lean_ctor_set_uint8(out,2*sizeof(void*),result.status);
    return out;
}
#endif
#endif
#endif
