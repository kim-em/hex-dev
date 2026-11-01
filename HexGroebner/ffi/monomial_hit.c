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
#define HEX_GROEBNER_UNIQUE_ALIAS() ((void)0)
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

static lean_obj_res hit_extend(lean_obj_arg bytes,size_t size) {
    size_t old=lean_sarray_size(bytes);
    if(lean_is_exclusive(bytes) && lean_sarray_capacity(bytes)>=size) {
        lean_sarray_set_size(bytes,size);return bytes;
    }
    size_t capacity=old<=SIZE_MAX/2?old*2:size;
    if(capacity<size) capacity=size;
    bytes=lean_copy_sarray_nonlinear(bytes,capacity);
    lean_sarray_set_size(bytes,size);return bytes;
}
static void hit_write64(uint8_t *p,uint64_t value) {
    write_le(p,4,value);write_le(p+4,4,value>>32);
}

/* Only a complete, bounded lookup or same-width, same-capacity insertion is handled here. All unsupported
   inputs and every error or growth boundary return deferred input unchanged.
   The stack workspace plus candidate comparisons visit at most4096 coordinates;
   chain headers are limited to4096 as well. */
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
    if(exclusive && append && workspace==exponents && lean_sarray_size(workspace)==size)
        HEX_GROEBNER_UNIQUE_ALIAS();
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

LEAN_EXPORT lean_obj_res lean_hex_groebner_combine_owned(lean_obj_arg table,uint8_t operation,
        lean_obj_arg a,lean_obj_arg b,lean_obj_arg max_count,lean_obj_arg max_bytes,
        lean_obj_arg max_work,uint8_t native) {
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
