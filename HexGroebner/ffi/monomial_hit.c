/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include <lean/lean.h>
#ifndef HEX_GROEBNER_HIT_HELPERS
#define HEX_GROEBNER_NO_LEAN
#include "row_update.c"
#endif

#ifndef HEX_GROEBNER_HIT_FOUND
#define HEX_GROEBNER_HIT_FOUND() ((void)0)
#endif

#ifndef HEX_GROEBNER_DEFERRED
#define HEX_GROEBNER_DEFERRED() ((void)0)
#endif
#ifndef HEX_GROEBNER_UNIQUE_ALIAS
#define HEX_GROEBNER_UNIQUE_ALIAS(mask) ((void)(mask))
#endif

#ifndef HEX_GROEBNER_INSERT_FOUND
#define HEX_GROEBNER_INSERT_FOUND() ((void)0)
#endif

#ifndef HEX_GROEBNER_TABLE_UNIQUE
#define HEX_GROEBNER_TABLE_UNIQUE() ((void)0)
#endif

static uint64_t hit_mix(uint64_t h) {
    h=(h^(h>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    h=(h^(h>>27))*UINT64_C(0x94d049bb133111eb);
    return h^(h>>31);
}

/* An explicitly borrowed alias may force a copy without violating the owned
   arena's linear contract. Other sharing retains the runtime's diagnostics. */
static lean_obj_res hit_extend_alias(lean_obj_arg bytes,size_t size,int alias) {
    size_t old=lean_sarray_size(bytes);
    if(lean_is_exclusive(bytes) && lean_sarray_capacity(bytes)>=size) {
        lean_sarray_set_size(bytes,size);return bytes;
    }
    size_t capacity=old<=SIZE_MAX/2?old*2:size;
    if(capacity<size) capacity=size;
    if(alias || lean_is_exclusive(bytes)) {
        int linear=lean_sarray_is_marked_linear(bytes);
        bytes=lean_copy_sarray(bytes,capacity);
        if(linear) lean_sarray_mark_linear_core(bytes);
    } else bytes=lean_copy_sarray_nonlinear(bytes,capacity);
    lean_sarray_set_size(bytes,size);return bytes;
}
static lean_obj_res hit_extend(lean_obj_arg bytes,size_t size) {
    return hit_extend_alias(bytes,size,0);
}
static lean_obj_res hit_exclusive_alias(lean_obj_arg bytes,int alias) {
    if(!alias) return lean_sarray_ensure_exclusive(bytes);
    int linear=lean_sarray_is_marked_linear(bytes);
    bytes=lean_copy_sarray(bytes,lean_sarray_capacity(bytes));
    if(linear) lean_sarray_mark_linear_core(bytes);
    return bytes;
}
static void hit_write64(uint8_t *p,uint64_t value) {
    write_le(p,4,value);write_le(p+4,4,value>>32);
}

/* Only a complete, bounded lookup or same-width, same-capacity insertion is handled here. All unsupported
   inputs and every error or growth boundary return deferred input unchanged.
   The stack workspace plus candidate comparisons visit at most 4096 coordinates;
   chain headers are limited to 4096 as well. */
static lean_obj_res hit_compute(lean_obj_arg table,uint8_t operation,
        lean_obj_arg a,lean_obj_arg b,lean_obj_arg max_count,lean_obj_arg max_bytes,
        lean_obj_arg max_work,lean_obj_arg initial_work) {
    lean_object *arity_arg=lean_ctor_get(table,0),*count_arg=lean_ctor_get(table,3);
    lean_object *bits_arg=lean_ctor_get(table,6);
    if(!lean_is_scalar(arity_arg) || !lean_is_scalar(count_arg) || !lean_is_scalar(bits_arg) ||
       !lean_is_scalar(a) || !lean_is_scalar(b) || !lean_is_scalar(max_work) ||
       !lean_is_scalar(initial_work)) goto fallback;
    uint64_t arity=lean_unbox(arity_arg),count=lean_unbox(count_arg),bits=lean_unbox(bits_arg);
    uint64_t left=lean_unbox(a),right=lean_unbox(b),work=lean_unbox(initial_work);
    uint64_t allowance=lean_unbox(max_work);
    uint8_t tag=lean_ctor_get_uint8(table,8*sizeof(void*));
    unsigned width=tag==0?1:tag==1?2:4;
    lean_object *exponents=lean_ctor_get(table,1),*metadata=lean_ctor_get(table,2);
    lean_object *index=lean_ctor_get(table,5),*workspace=lean_ctor_get(table,4);
    lean_object *heads=lean_ctor_get(index,0),*links=lean_ctor_get(index,1);
    size_t head_bytes=lean_sarray_size(heads),capacity=head_bytes/4,size;
    if(!arity || arity>2047 || count>UINT32_MAX || bits>64 || operation>2 ||
       left>=count || right>=count || work>allowance || arity>allowance-work ||
       head_bytes%4 || !capacity || (capacity&(capacity-1)) || capacity<count*2 ||
       lean_sarray_size(metadata)!=count*24 || lean_sarray_size(links)!=count*4)
        goto fallback;
    size=(size_t)arity*4+28;
    uint8_t prepared[2047*4+28];
    if(!prepare_monomial(operation,width,arity,count,left,right,
        lean_sarray_cptr(exponents),lean_sarray_size(exponents),prepared,size)) goto fallback;
    work+=arity;
    uint64_t hash=read_le(prepared+arity*4+16,4) |
        (read_le(prepared+arity*4+20,4)<<32);
    if(bits<64) hash&=(UINT64_C(1)<<bits)-1;
    size_t slot=(size_t)(hit_mix(hash)&(capacity-1));
    uint64_t start_link=read_le(lean_sarray_cptr(heads)+slot*4,4),link=start_link;
    uint64_t visits=0,coordinates=arity,found=UINT64_MAX;
    while(link && visits<count && visits<4096) {
        if(work>=allowance) goto fallback;
        ++work;++visits;
        uint64_t id=link-1;
        if(id>=count) goto fallback;
        link=read_le(lean_sarray_cptr(links)+(size_t)id*4,4);
        const uint8_t *m=lean_sarray_cptr(metadata)+(size_t)id*24+16;
        uint64_t stored=read_le(m,4) | (read_le(m+4,4)<<32);
        if(stored!=hash) continue;
        if(coordinates+arity>4096 || arity>allowance-work) goto fallback;
        coordinates+=arity;work+=arity;
        if(equal_monomial(width,arity,id,lean_sarray_cptr(exponents),
            lean_sarray_size(exponents),prepared,size)) {found=id;break;}
    }
    int append=found==UINT64_MAX;
    if(append) {
        if(link || count>=UINT32_MAX || !lean_is_scalar(max_count) || !lean_is_scalar(max_bytes) ||
           count>=lean_unbox(max_count) || count+1>capacity/2) goto fallback;
        uint64_t largest=read_le(prepared+arity*4+24,4);
        if((width==1 && largest>255) || (width==2 && largest>65535)) goto fallback;
        uint64_t needed=(count+1)*(arity*width+28)+size+head_bytes;
        if(needed>lean_unbox(max_bytes) || needed>=SIZE_MAX || work>allowance ||
           arity+2>allowance-work) goto fallback;
        work+=arity+2;found=count;
    }
    if(work-lean_unbox(initial_work)>4096) goto fallback;
    if(append) HEX_GROEBNER_INSERT_FOUND();
    HEX_GROEBNER_HIT_FOUND();
    /* Consume the table before mutating the moved workspace. Shared tables and
       caller aliases retain their own references and force a copy. */
    lean_object *fields[8],*updated;
    int exclusive=lean_is_exclusive(table);
    if(exclusive && append && lean_sarray_size(workspace)==size) {
        unsigned aliases=(workspace==exponents?1:0)|(workspace==metadata?2:0)|
            (workspace==heads?4:0)|(workspace==links?8:0);
        if(aliases) HEX_GROEBNER_UNIQUE_ALIAS(aliases);
    }
    for(unsigned i=0;i<8;++i) {
        fields[i]=lean_ctor_get(table,i);
        if(!exclusive) lean_inc(fields[i]);
    }
    if(exclusive) {HEX_GROEBNER_TABLE_UNIQUE();updated=table;}
    else {lean_dec(table);updated=lean_alloc_ctor(0,8,1);}

    if(lean_sarray_size(workspace)!=size) {
        lean_dec(fields[4]);fields[4]=lean_alloc_sarray(1,size,size);
    } else fields[4]=lean_sarray_ensure_exclusive(fields[4]);
    memcpy(lean_sarray_cptr(fields[4]),prepared,size);
    if(append) {
        size_t exponent_bytes=(size_t)count*(size_t)arity*width;
        fields[1]=hit_extend(fields[1],exponent_bytes+(size_t)arity*width);
        for(size_t i=0;i<(size_t)arity;++i)
            write_le(lean_sarray_cptr(fields[1])+exponent_bytes+i*width,width,read_le(prepared+i*4,4));
        fields[2]=hit_extend(fields[2],(size_t)(count+1)*24);
        uint8_t *m=lean_sarray_cptr(fields[2])+(size_t)count*24;
        memcpy(m,prepared+(size_t)arity*4,16);hit_write64(m+16,hash);
        lean_object *old_index=fields[5],*new_heads=lean_ctor_get(old_index,0),*new_links=lean_ctor_get(old_index,1);
        lean_inc(new_heads);lean_inc(new_links);lean_dec(old_index);
        new_heads=lean_sarray_ensure_exclusive(new_heads);
        new_links=hit_extend(new_links,(size_t)(count+1)*4);
        write_le(lean_sarray_cptr(new_heads)+slot*4,4,count+1);
        write_le(lean_sarray_cptr(new_links)+(size_t)count*4,4,start_link);
        fields[5]=lean_alloc_ctor(0,2,0);
        lean_ctor_set(fields[5],0,new_heads);lean_ctor_set(fields[5],1,new_links);
        lean_dec(fields[3]);fields[3]=lean_uint64_to_nat(count+1);
    }
    lean_dec(fields[7]);fields[7]=lean_uint64_to_nat(work);
    for(unsigned i=0;i<8;++i) lean_ctor_set(updated,i,fields[i]);
    lean_ctor_set_uint8(updated,8*sizeof(void*),tag);
    lean_object *ok=lean_alloc_ctor(1,1,0);lean_ctor_set(ok,0,lean_uint64_to_nat(found));
    lean_object *result=lean_alloc_ctor(0,2,0);
    lean_ctor_set(result,0,ok);lean_ctor_set(result,1,updated);
    lean_dec(a);lean_dec(b);lean_dec(max_count);lean_dec(max_bytes);lean_dec(max_work);lean_dec(initial_work);
    lean_object *accepted=lean_alloc_ctor(0,1,0);lean_ctor_set(accepted,0,result);
    return accepted;
fallback:
    HEX_GROEBNER_DEFERRED();
    lean_dec(a);lean_dec(b);lean_dec(max_count);lean_dec(max_bytes);lean_dec(max_work);lean_dec(initial_work);
    lean_object *deferred=lean_alloc_ctor(1,1,0);lean_ctor_set(deferred,0,table);return deferred;
}

/* MonomialTable has eight object fields and one trailing Width byte;
   MonomialIndex has two object fields. Attempt tags are accepted=0/deferred=1,
   InternResult is a two-field constructor and Except.ok has tag1.
   Object counts do not detect reordered fields or changes to the scalar area.
   Keep the complete ABI synchronized with Monomial.lean and MonomialIndex.lean. */
static int hit_layout(b_lean_obj_arg table) {
    if(lean_is_scalar(table) || !lean_is_ctor(table) ||
       lean_ctor_num_objs(table)!=8) return 0;
    lean_object *index=lean_ctor_get(table,5);
    if(lean_is_scalar(index) || !lean_is_ctor(index) ||
       lean_ctor_num_objs(index)!=2) return 0;
    unsigned positions[3]={1,2,4};
    for(unsigned i=0;i<3;++i) {
        lean_object *bytes=lean_ctor_get(table,positions[i]);
        if(lean_is_scalar(bytes) || !lean_is_sarray(bytes) ||
           lean_sarray_elem_size(bytes)!=1) return 0;
    }
    for(unsigned i=0;i<2;++i) {
        lean_object *bytes=lean_ctor_get(index,i);
        if(lean_is_scalar(bytes) || !lean_is_sarray(bytes) ||
           lean_sarray_elem_size(bytes)!=1) return 0;
    }
    return lean_ctor_get_uint8(table,8*sizeof(void*))<=2;
}

LEAN_EXPORT lean_obj_res lean_hex_groebner_combine_owned(lean_obj_arg table,uint8_t operation,
        lean_obj_arg a,lean_obj_arg b,lean_obj_arg max_count,lean_obj_arg max_bytes,
        lean_obj_arg max_work,uint8_t native) {
    if(!hit_layout(table)) goto fallback_owned;
    lean_object *arity_arg=lean_ctor_get(table,0),*count_arg=lean_ctor_get(table,3);
    lean_object *work_arg=lean_ctor_get(table,7);
    if(!native || !lean_is_scalar(arity_arg) || !lean_is_scalar(count_arg) ||
       !lean_is_scalar(work_arg) || !lean_is_scalar(a) || !lean_is_scalar(b) ||
       !lean_is_scalar(max_work) || !lean_is_scalar(max_bytes)) goto fallback_owned;
    uint64_t arity=lean_unbox(arity_arg),count=lean_unbox(count_arg),work=lean_unbox(work_arg);
    uint64_t left=lean_unbox(a),right=lean_unbox(b),allowed=lean_unbox(max_work);
    uint8_t tag=lean_ctor_get_uint8(table,8*sizeof(void*));
    unsigned width=tag==0?1:tag==1?2:4;
    lean_object *exponents=lean_ctor_get(table,1),*metadata=lean_ctor_get(table,2);
    lean_object *workspace=lean_ctor_get(table,4),*index=lean_ctor_get(table,5);
    lean_object *heads=lean_ctor_get(index,0),*links=lean_ctor_get(index,1);
    size_t head_bytes=lean_sarray_size(heads),capacity=head_bytes/4;
    if(!arity || arity>2047 || !count || count>UINT32_MAX || left>=count || right>=count ||
       lean_sarray_size(exponents)!=count*arity*width || lean_sarray_size(metadata)!=count*24 ||
       lean_sarray_size(links)!=count*4 || head_bytes%4 || capacity<count*2 ||
       (capacity&(capacity-1)) || work>allowed || arity>allowed-work) goto fallback_owned;
    uint64_t reserved=arity*4+28,ws=lean_sarray_size(workspace);
    if(ws>reserved) reserved=ws;
    uint64_t bytes=lean_sarray_size(exponents)+lean_sarray_size(metadata)+lean_sarray_size(links);
    if(head_bytes>UINT64_MAX-bytes) goto fallback_owned;
    bytes+=head_bytes;
    if(reserved>UINT64_MAX-bytes) goto fallback_owned;
    bytes+=reserved;
    if(bytes>lean_unbox(max_bytes) || bytes>=SIZE_MAX) goto fallback_owned;
    return hit_compute(table,operation,a,b,max_count,max_bytes,max_work,
        lean_uint64_to_nat(work+arity));
fallback_owned:
    HEX_GROEBNER_DEFERRED();
    lean_dec(a);lean_dec(b);lean_dec(max_count);lean_dec(max_bytes);lean_dec(max_work);
    lean_object *deferred=lean_alloc_ctor(1,1,0);lean_ctor_set(deferred,0,table);return deferred;
}

/* Bounded multi-product lookup/insertion with the exact scalar result. Input
   ids refer to the initial table. At most 64 results and 4096 charged coordinate,
   link and insertion units are admitted, without exponent widening or rehashing.
   Read-only planning preserves the complete table on every refusal. Success
   takes table/arena ownership once and appends in term order. Shared buffers
   copy at most the current table payload, as with scalar owned insertion.
   The support is borrowed and remains immutable, including arena aliases. */
#ifndef HEX_GROEBNER_PRODUCTS_FOUND
#define HEX_GROEBNER_PRODUCTS_FOUND(n) ((void)(n))
#endif
#ifndef HEX_GROEBNER_PRODUCTS_DEFERRED
#define HEX_GROEBNER_PRODUCTS_DEFERRED(work) ((void)(work))
#endif
#ifndef HEX_GROEBNER_PRODUCTS_BORROWED
#define HEX_GROEBNER_PRODUCTS_BORROWED(support) ((void)(support))
#endif
#ifndef HEX_GROEBNER_PRODUCTS_INSERTED
#define HEX_GROEBNER_PRODUCTS_INSERTED(n) ((void)(n))
#endif

/* Read-only planning keeps deferral atomic. At most 64 new rows and heads are
   virtual until the complete 4096-unit reference computation succeeds. The
   fixed scratch arenas use less than 32 KiB. An additional <=64^2 head-overlay
   comparisons are bounded independently of the ambient table size. */
typedef struct {
    uint8_t exponents[4096*4],metadata[64*24],prepared[2047*4+28],output[64*4];
    uint32_t links[64],heads[64];
    uint64_t hashes[64];
    size_t slots[64];
    unsigned inserted,changed;
} product_plan;

/* Independent rows keep the serial FNV accumulators in parallel. All input
   identifiers belong to the initial arena. Only private planning bytes change.
   The full preparation reservation is charged before the coordinate traversal. */
_Static_assert(sizeof(product_plan)+4*64*sizeof(uint64_t)+64*sizeof(const uint8_t *)<32768,
    "product planning scratch must remain below 32 KiB");
static int products_prepare(unsigned width,uint64_t arity,uint64_t count,uint64_t right,
        const uint8_t *source,const uint8_t *support,size_t start,size_t terms,
        uint8_t *prepared,size_t stride) {
    const uint8_t *left[64];
    uint64_t degree[64],mask[64],hash[64],largest[64];
    for(size_t t=0;t<terms;++t) {
        uint64_t id=read_le(support+(start+t)*4,4);
        if(id>=count) return 0;
        left[t]=source+(size_t)id*(size_t)arity*width;
        degree[t]=0;mask[t]=0;largest[t]=0;
        hash[t]=UINT64_C(14695981039346656037);
    }
    const uint8_t *right_row=source+(size_t)right*(size_t)arity*width;
    unsigned overflow=0;
    for(size_t i=0;i<(size_t)arity;++i) {
        size_t offset=i*width;
        uint64_t y=read_le(right_row+offset,width);
        uint64_t bit=UINT64_C(1)<<(i%64);
        for(size_t t=0;t<terms;++t) {
            uint64_t x=read_le(left[t]+offset,width),z=x+y;
            overflow|=z>UINT32_MAX;
            write_le(prepared+t*stride+4*i,4,z);
            degree[t]+=z;mask[t]|=z?bit:0;
            hash[t]=(hash[t]^z)*UINT64_C(1099511628211);
            if(z>largest[t]) largest[t]=z;
        }
    }
    if(overflow) return 0;
    for(size_t t=0;t<terms;++t) {
        uint8_t *meta=prepared+t*stride+(size_t)arity*4;
        hit_write64(meta,degree[t]);hit_write64(meta+8,mask[t]);
        hit_write64(meta+16,hash[t]);write_le(meta+24,4,largest[t]);
    }
    return 1;
}

/* Consumes table on success only; NULL leaves its ownership with the caller. */
static lean_object *products_hits(lean_obj_arg table,b_lean_obj_arg support,
        b_lean_obj_arg monomial,b_lean_obj_arg start_arg,b_lean_obj_arg count_arg,
        b_lean_obj_arg max_count,b_lean_obj_arg max_bytes,b_lean_obj_arg max_work,
        uint8_t native,uint64_t *visited_work) {
    *visited_work=0;
    if(!native || !hit_layout(table) || !lean_is_scalar(monomial) ||
       !lean_is_scalar(start_arg) || !lean_is_scalar(count_arg) ||
       !lean_is_scalar(max_bytes) || !lean_is_scalar(max_work)) return NULL;
    unsigned positions[4]={0,3,6,7};
    for(unsigned i=0;i<4;++i)
        if(!lean_is_scalar(lean_ctor_get(table,positions[i]))) return NULL;
    uint64_t arity=lean_unbox(lean_ctor_get(table,0));
    uint64_t count=lean_unbox(lean_ctor_get(table,3));
    uint64_t bits=lean_unbox(lean_ctor_get(table,6));
    uint64_t work=lean_unbox(lean_ctor_get(table,7)),initial=work;
    uint64_t allowed=lean_unbox(max_work),right=lean_unbox(monomial);
    if(!arity || arity>2047 || !count || count>UINT32_MAX || bits>64 ||
       right>=count || work>allowed) return NULL;
    size_t start=lean_unbox(start_arg),terms=lean_unbox(count_arg);
    size_t available=lean_sarray_size(support)/4;
    if(start>=available || !terms) return NULL;
    if(terms>available-start) terms=available-start;
    if(terms>64 || terms>4096/(3*arity+1)) return NULL;
    uint8_t tag=lean_ctor_get_uint8(table,8*sizeof(void*));
    unsigned width=tag==0?1:tag==1?2:4;
    lean_object *exponents=lean_ctor_get(table,1),*metadata=lean_ctor_get(table,2);
    lean_object *workspace=lean_ctor_get(table,4),*index=lean_ctor_get(table,5);
    lean_object *heads=lean_ctor_get(index,0),*links=lean_ctor_get(index,1);
    size_t head_bytes=lean_sarray_size(heads),capacity=head_bytes/4;
    if(lean_sarray_size(exponents)!=count*arity*width ||
       lean_sarray_size(metadata)!=count*24 || lean_sarray_size(links)!=count*4 ||
       head_bytes%4 || capacity<count*2 || (capacity&(capacity-1))) return NULL;
    size_t size=(size_t)arity*4+28;
    uint64_t reserved=lean_sarray_size(workspace);
    if(reserved<size) reserved=size;
    uint64_t bytes=count*(arity*width+28);
    if(head_bytes>UINT64_MAX-bytes) return NULL;
    bytes+=head_bytes;
    if(reserved>UINT64_MAX-bytes) return NULL;
    bytes+=reserved;
    if(bytes>lean_unbox(max_bytes) || bytes>=SIZE_MAX) return NULL;
    product_plan plan;plan.inserted=0;plan.changed=0;
    uint64_t preparation=2*arity*terms;
    if(terms>sizeof(plan.prepared)/size || preparation>allowed-work || preparation>4096) return NULL;
    *visited_work=preparation;
    if(!products_prepare(width,arity,count,right,lean_sarray_cptr(exponents),
        lean_sarray_cptr(support),start,terms,plan.prepared,size)) return NULL;
    work+=preparation;
    for(size_t term=0;term<terms;++term) {
        const uint8_t *prepared=plan.prepared+term*size;
        uint64_t hash=read_le(prepared+arity*4+16,4) |
            (read_le(prepared+arity*4+20,4)<<32);
        if(bits<64) hash&=(UINT64_C(1)<<bits)-1;
        size_t slot=(size_t)(hit_mix(hash)&(capacity-1));
        unsigned changed=0;
        while(changed<plan.changed && plan.slots[changed]!=slot) ++changed;
        uint64_t start_link=changed<plan.changed?plan.heads[changed]:
            read_le(lean_sarray_cptr(heads)+slot*4,4);
        uint64_t link=start_link,visited=0,found=UINT64_MAX,current=count+plan.inserted;
        while(link && visited<current) {
            if(work==allowed || work-initial==4096) return NULL;
            ++work;++visited;*visited_work=work-initial;
            uint64_t id=link-1,stored;
            if(id>=current) return NULL;
            if(id<count) {
                link=read_le(lean_sarray_cptr(links)+(size_t)id*4,4);
                const uint8_t *m=lean_sarray_cptr(metadata)+(size_t)id*24+16;
                stored=read_le(m,4)|(read_le(m+4,4)<<32);
            } else {
                link=plan.links[id-count];stored=plan.hashes[id-count];
            }
            if(stored!=hash) continue;
            if(arity>allowed-work || arity>4096-(work-initial)) return NULL;
            work+=arity;*visited_work=work-initial;
            int equal=id<count?equal_monomial(width,arity,id,lean_sarray_cptr(exponents),
                lean_sarray_size(exponents),prepared,size):
                equal_monomial(width,arity,id-count,plan.exponents,
                    (size_t)plan.inserted*arity*width,prepared,size);
            if(equal) {found=id;break;}
        }
        if(found==UINT64_MAX) {
            if(link || current>=UINT32_MAX || !lean_is_scalar(max_count) ||
               current>=lean_unbox(max_count) || current+1>capacity/2) return NULL;
            uint64_t largest=read_le(prepared+arity*4+24,4);
            if((width==1 && largest>255) || (width==2 && largest>65535)) return NULL;
            uint64_t needed=(current+1)*(arity*width+28)+size+head_bytes;
            if(needed>lean_unbox(max_bytes) || needed>=SIZE_MAX ||
               arity+2>allowed-work || arity+2>4096-(work-initial)) return NULL;
            if((size_t)(plan.inserted+1)*arity*width>sizeof(plan.exponents)) return NULL;
            work+=arity+2;*visited_work=work-initial;
            uint8_t *e=plan.exponents+(size_t)plan.inserted*arity*width;
            for(size_t i=0;i<arity;++i) write_le(e+i*width,width,read_le(prepared+i*4,4));
            uint8_t *m=plan.metadata+(size_t)plan.inserted*24;
            memcpy(m,prepared+arity*4,16);hit_write64(m+16,hash);
            plan.links[plan.inserted]=(uint32_t)start_link;plan.hashes[plan.inserted]=hash;
            if(changed==plan.changed) {plan.slots[changed]=slot;++plan.changed;}
            plan.heads[changed]=(uint32_t)(current+1);
            found=current;++plan.inserted;
        }
        write_le(plan.output+term*4,4,found);
    }
    /* No input has changed. Acquire field ownership once, then publish the
       complete append. A borrowed support alias forces the same copy-on-write
       protection as an independently held snapshot. */
    lean_object *alias=NULL;
    if(support==exponents || support==metadata || support==workspace || support==heads || support==links) {
        alias=(lean_object *)support;lean_inc(alias);
    }
    lean_object *fields[8],*updated;int exclusive=lean_is_exclusive(table);
    for(unsigned i=0;i<8;++i) {
        fields[i]=lean_ctor_get(table,i);if(!exclusive) lean_inc(fields[i]);
    }
    if(exclusive) updated=table;
    else {lean_dec(table);updated=lean_alloc_ctor(0,8,1);}
    if(lean_sarray_size(fields[4])!=size) {
        lean_dec(fields[4]);fields[4]=lean_alloc_sarray(1,size,size);
    } else fields[4]=hit_exclusive_alias(fields[4],support==workspace);
    memcpy(lean_sarray_cptr(fields[4]),plan.prepared+(terms-1)*size,size);
    if(plan.inserted) {
        size_t old_bytes=(size_t)count*arity*width;
        fields[1]=hit_extend_alias(fields[1],(size_t)(count+plan.inserted)*arity*width,support==exponents);
        memcpy(lean_sarray_cptr(fields[1])+old_bytes,plan.exponents,(size_t)plan.inserted*arity*width);
        fields[2]=hit_extend_alias(fields[2],(size_t)(count+plan.inserted)*24,support==metadata);
        memcpy(lean_sarray_cptr(fields[2])+(size_t)count*24,plan.metadata,(size_t)plan.inserted*24);
        lean_object *old_index=fields[5],*new_heads=lean_ctor_get(old_index,0),*new_links=lean_ctor_get(old_index,1);
        lean_inc(new_heads);lean_inc(new_links);lean_dec(old_index);
        new_heads=hit_exclusive_alias(new_heads,support==heads);
        new_links=hit_extend_alias(new_links,(size_t)(count+plan.inserted)*4,support==links);
        for(unsigned i=0;i<plan.changed;++i) write_le(lean_sarray_cptr(new_heads)+plan.slots[i]*4,4,plan.heads[i]);
        for(unsigned i=0;i<plan.inserted;++i) write_le(lean_sarray_cptr(new_links)+(size_t)(count+i)*4,4,plan.links[i]);
        fields[5]=lean_alloc_ctor(0,2,0);lean_ctor_set(fields[5],0,new_heads);lean_ctor_set(fields[5],1,new_links);
        lean_dec(fields[3]);fields[3]=lean_uint64_to_nat(count+plan.inserted);
    }
    lean_dec(fields[7]);fields[7]=lean_uint64_to_nat(work);
    for(unsigned i=0;i<8;++i) lean_ctor_set(updated,i,fields[i]);
    lean_ctor_set_uint8(updated,8*sizeof(void*),tag);
    HEX_GROEBNER_PRODUCTS_BORROWED(support);
    if(alias) lean_dec(alias);
    lean_object *ids=lean_alloc_sarray(1,terms*4,terms*4);memcpy(lean_sarray_cptr(ids),plan.output,terms*4);
    lean_object *ok=lean_alloc_ctor(1,1,0);lean_ctor_set(ok,0,ids);
    lean_object *result=lean_alloc_ctor(0,2,0);lean_ctor_set(result,0,ok);lean_ctor_set(result,1,updated);
    HEX_GROEBNER_PRODUCTS_INSERTED(plan.inserted);
    HEX_GROEBNER_PRODUCTS_FOUND(terms);
    return result;
}
LEAN_EXPORT lean_obj_res lean_hex_monomial_products_attempt(lean_obj_arg table,
        b_lean_obj_arg support,lean_obj_arg monomial,lean_obj_arg start,
        lean_obj_arg count,lean_obj_arg max_count,lean_obj_arg max_bytes,
        lean_obj_arg max_work,uint8_t native) {
    uint64_t visited_work=0;
    lean_object *result=products_hits(table,support,monomial,start,count,max_count,max_bytes,max_work,native,&visited_work);
    if(result) {lean_dec(monomial);lean_dec(start);lean_dec(count);
        lean_dec(max_count);lean_dec(max_bytes);lean_dec(max_work);
        lean_object *accepted=lean_alloc_ctor(0,1,0);lean_ctor_set(accepted,0,result);
        return accepted;
    }
    HEX_GROEBNER_PRODUCTS_DEFERRED(visited_work);
    lean_dec(monomial);lean_dec(start);lean_dec(count);
    lean_dec(max_count);lean_dec(max_bytes);lean_dec(max_work);
    lean_object *deferred=lean_alloc_ctor(1,1,0);lean_ctor_set(deferred,0,table);
    return deferred;
}
