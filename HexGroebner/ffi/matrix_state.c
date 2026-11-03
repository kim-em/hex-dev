/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

extern lean_obj_res lean_hex_matrix_step(lean_obj_arg);
#include "matrix_runtime.h"

#ifndef HEX_GROEBNER_CONT_SUCCESS
#define HEX_GROEBNER_CONT_SUCCESS(initial_phase,phase,result,reductions,zero_rows) ((void)(initial_phase))
#endif
#ifndef HEX_GROEBNER_CONT_INVERSE
#define HEX_GROEBNER_CONT_INVERSE() ((void)0)
#endif

#ifndef HEX_GROEBNER_CONT_PHASE
#define HEX_GROEBNER_CONT_PHASE(phase) ((void)0)
#endif

#ifndef HEX_GROEBNER_CONT_BEGIN
#define HEX_GROEBNER_CONT_BEGIN(columns,rows,count,overhead) ((void)0)
#define HEX_GROEBNER_CONT_TICK() ((void)0)
#define HEX_GROEBNER_CONT_END() ((void)0)
#endif

#ifndef HEX_GROEBNER_CONT_EXHAUSTED
#define HEX_GROEBNER_CONT_EXHAUSTED(phase,resource,width) ((void)0)
#define HEX_GROEBNER_CONT_INVALID(tag,width) ((void)0)
#define HEX_GROEBNER_CONT_DECLINE(width) ((void)0)
#define HEX_GROEBNER_CONT_EDGE(width) ((void)0)
#define HEX_GROEBNER_CONT_ALLOCATE(width) ((void)0)
#define HEX_GROEBNER_CONT_VALIDATE_WORK(site,width) ((void)0)
#endif

#if UINTPTR_MAX == UINT64_MAX

/* State: 21 objects; modulus/inverse UInt64, independent/phase UInt8.
   See MatrixState.lean. Private construction binds context and continuation.
   Owners are extracted before the old header is released. A saved snapshot
   continues to share immutable inputs; mutable buffers then copy on write. */
typedef struct {
    lean_object *v[21];
    uint64_t p,inverse,limits[7],stats[8],columns;
    uint8_t independent,phase;
    unsigned width;
} continuation;
static lean_object *cont_take(b_lean_obj_arg o,unsigned i) {
    lean_object *a=lean_ctor_get(o,i);lean_inc(a);return a;
}
static uint64_t cont_read(const uint8_t *p,unsigned w) {
    uint64_t x=p[0];
    if(w>1) x|=(uint64_t)p[1]<<8;
    if(w>2) x|=(uint64_t)p[2]<<16 | (uint64_t)p[3]<<24;
    return x;
}
static void cont_write(uint8_t *p,unsigned w,uint64_t x) {
    for(unsigned i=0;i<w;++i) {p[i]=(uint8_t)x;x>>=8;}
}
static lean_object *cont_empty(void) {return lean_alloc_sarray(1,0,0);}
static lean_object *cont_row(lean_obj_arg a,lean_obj_arg b) {
    lean_object *r=lean_alloc_ctor(0,2,0);lean_ctor_set(r,0,a);lean_ctor_set(r,1,b);return r;
}
static void cont_replace(continuation *c,unsigned i,lean_obj_arg value) {
    if(c->v[i]) lean_dec(c->v[i]);
    c->v[i]=value;
}
static void cont_unpack(continuation *c,lean_obj_arg s) {
    c->p=lean_ctor_get_uint64(s,21*sizeof(void*));
    c->inverse=lean_ctor_get_uint64(s,21*sizeof(void*)+8);
    c->independent=lean_ctor_get_uint8(s,21*sizeof(void*)+16);
    c->phase=lean_ctor_get_uint8(s,21*sizeof(void*)+17);
    for(unsigned i=0;i<21;++i) c->v[i]=cont_take(s,i);
    lean_dec(s);
    c->columns=lean_unbox(c->v[1]);c->width=c->p<=256?1:c->p<=65536?2:4;
}
static int cont_counts(continuation *c) {
    for(unsigned i=0;i<8;++i) {
        lean_object *n=lean_ctor_get(c->v[17],i);
        if(!lean_is_scalar(n) || lean_unbox(n)>(UINT64_C(1)<<62)-1) return 0;
        c->stats[i]=lean_unbox(n);
    }
    for(unsigned i=0;i<7;++i) {
        lean_object *n=lean_ctor_get(c->v[0],i);
        c->limits[i]=lean_is_scalar(n)?lean_unbox(n):UINT64_MAX/2;
    }
    return c->stats[0]<=c->limits[5] && c->stats[1]<=c->limits[2] &&
        c->stats[2]<=c->limits[3] && c->stats[3]<=c->limits[4] && c->stats[4]<=c->limits[6];
}
static void cont_save_counts(continuation *c) {
    lean_object *s=lean_alloc_ctor(0,8,0);
    for(unsigned i=0;i<8;++i) lean_ctor_set(s,i,lean_uint64_to_nat(c->stats[i]));
    cont_replace(c,17,s);
}
static lean_object *cont_pack(continuation *c) {
    lean_object *s=lean_alloc_ctor(0,21,18);
    for(unsigned i=0;i<21;++i) lean_ctor_set(s,i,c->v[i]);
    lean_ctor_set_uint64(s,21*sizeof(void*),c->p);
    lean_ctor_set_uint64(s,21*sizeof(void*)+8,c->inverse);
    lean_ctor_set_uint8(s,21*sizeof(void*)+16,c->independent);
    lean_ctor_set_uint8(s,21*sizeof(void*)+17,c->phase);return s;
}
static int cont_charge(continuation *c,unsigned stat,unsigned limit,uint64_t amount) {
    if(c->stats[stat]>c->limits[limit] || amount>c->limits[limit]-c->stats[stat]) return 0;
    c->stats[stat]+=amount;return 1;
}
static int cont_work(continuation *c,uint64_t n) {return cont_charge(c,0,5,n);}
static void cont_error(continuation *c,unsigned resource) {
    HEX_GROEBNER_CONT_EXHAUSTED(c->phase,resource,c->width);
    lean_object *e=lean_alloc_ctor(5,0,1);lean_ctor_set_uint8(e,0,(uint8_t)resource);
    lean_object *r=lean_alloc_ctor(0,1,0);lean_ctor_set(r,0,e);
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,r);
    cont_replace(c,18,some);c->phase=7;
}
static void cont_internal(continuation *c) {
    lean_object *r=lean_alloc_ctor(0,1,0);lean_ctor_set(r,0,lean_box(1));
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,r);
    cont_replace(c,18,some);c->phase=7;
}
static lean_object *cont_empty_scan(void) {
    lean_object *s=lean_alloc_ctor(0,8,8);lean_ctor_set(s,0,cont_empty());
    for(unsigned i=1;i<8;++i) lean_ctor_set(s,i,lean_box(0));
    lean_ctor_set_uint64(s,8*sizeof(void*),0);return s;
}
static lean_object *cont_empty_gather(void) {
    lean_object *s=lean_alloc_ctor(0,4,0);
    for(unsigned i=0;i<3;++i) lean_ctor_set(s,i,cont_empty());
    lean_ctor_set(s,3,lean_box(0));return s;
}
/* Enforce every buffer bound before a direct write. A failed preflight uses
   the checked Lean phase, before charges or mutable buffers have changed. */
static int cont_bounds(continuation *c) {
    if(c->phase==2) return c->columns<=65536 && c->p>=2 && c->p<UINT64_C(2147483648);
    if(c->phase==1) {
        if(!lean_is_scalar(c->v[5])) return 0;
        uint64_t cursor=lean_unbox(c->v[5]),nr=lean_array_size(c->v[2]);
        if(cursor>=nr+lean_array_size(c->v[3])) return 1;
        lean_object *row=lean_array_get_core(c->v[cursor<nr?2:3],(size_t)(cursor<nr?cursor:cursor-nr));
        if(lean_is_scalar(row) || lean_obj_tag(row)!=0 || lean_ctor_num_objs(row)!=2) return 0;
        uint64_t bytes=lean_sarray_size(lean_ctor_get(row,0)),n=bytes/4;
        /* A malformed length fails before the row loop. The size admission
           bounds charge amounts as well as reads, keeping saturated large
           limits exact. Larger well-shaped rows use the checked Lean phase. */
        if(bytes%4 || lean_sarray_size(lean_ctor_get(row,1))!=n*c->width) return 1;
        if(n>c->columns+1) {HEX_GROEBNER_CONT_DECLINE(c->width);return 0;}
        if(n==c->columns+1) HEX_GROEBNER_CONT_EDGE(c->width);
        return 1;
    }
    if(c->p<2 || c->p>=UINT64_C(2147483648) ||
       lean_sarray_size(c->v[8])!=c->columns*4 || !lean_is_scalar(c->v[6]) ||
       !lean_is_scalar(c->v[12]) || !lean_is_scalar(c->v[19])) return 0;
    if(c->phase==3) {
        if(lean_sarray_size(c->v[7])!=c->columns*c->width) return 0;
        uint64_t input=lean_unbox(c->v[6]),nr=lean_array_size(c->v[2]);
        if(input>=nr+lean_array_size(c->v[3])) return 1;
        lean_object *row=lean_array_get_core(c->v[input<nr?2:3],(size_t)(input<nr?input:input-nr));
        if(lean_is_scalar(row) || lean_obj_tag(row)!=0 || lean_ctor_num_objs(row)!=2) return 0;
        lean_object *ids=lean_ctor_get(row,0),*coeff=lean_ctor_get(row,1);
        size_t bytes=lean_sarray_size(ids),n=bytes/4;
        if(bytes%4 || n>c->columns || lean_sarray_size(coeff)!=n*c->width) return 0;
        for(size_t i=0;i<n;++i) if(cont_read(lean_sarray_cptr(ids)+4*i,4)>=c->columns) return 0;
        return 1;
    }
    if(c->phase==4) {
        lean_object *scan=c->v[13];
        return !lean_is_scalar(scan) && lean_obj_tag(scan)==0 && lean_ctor_num_objs(scan)==8 &&
            lean_sarray_size(lean_ctor_get(scan,0))==c->columns*c->width;
    }
    lean_object *gather=c->v[14],*scan=c->v[13];
    return !lean_is_scalar(gather) && lean_obj_tag(gather)==0 && lean_ctor_num_objs(gather)==4 &&
        !lean_is_scalar(scan) && lean_obj_tag(scan)==0 && lean_ctor_num_objs(scan)==8 &&
        lean_sarray_size(lean_ctor_get(gather,0))==c->columns*c->width &&
        lean_is_scalar(c->v[15]) && lean_unbox(c->v[15])<c->columns;
}
/* Validator errors carry the original input index and first failing entry. */
static void cont_invalid(continuation *c,unsigned tag,uint64_t row,uint64_t entry) {
    HEX_GROEBNER_CONT_INVALID(tag,c->width);
    lean_object *e=lean_alloc_ctor(tag,tag==2?1:2,0);
    lean_ctor_set(e,0,lean_uint64_to_nat(row));
    if(tag!=2) lean_ctor_set(e,1,lean_uint64_to_nat(entry));
    lean_object *r=lean_alloc_ctor(0,1,0);lean_ctor_set(r,0,e);
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,r);
    cont_replace(c,18,some);c->phase=7;
}
static void cont_validate(continuation *c) {
    uint64_t cursor=lean_unbox(c->v[5]),nr=lean_array_size(c->v[2]);
    if(cursor>=nr+lean_array_size(c->v[3])) {c->phase=2;return;}
    if(!cont_work(c,1)) {HEX_GROEBNER_CONT_VALIDATE_WORK(0,c->width);cont_error(c,5);return;}
    lean_object *row=lean_array_get_core(c->v[cursor<nr?2:3],(size_t)(cursor<nr?cursor:cursor-nr));
    lean_object *ids=lean_ctor_get(row,0),*coeff=lean_ctor_get(row,1);
    uint64_t bytes=lean_sarray_size(ids),size=bytes/4,coefficient_bytes=lean_sarray_size(coeff);
    if(bytes%4 || coefficient_bytes!=size*c->width) {cont_invalid(c,2,cursor,0);return;}
    if(!cont_charge(c,1,2,size)) {cont_error(c,2);return;}
    if(!cont_charge(c,3,4,bytes+coefficient_bytes)) {cont_error(c,4);return;}
    if(!cont_work(c,size)) {HEX_GROEBNER_CONT_VALIDATE_WORK(1,c->width);cont_error(c,5);return;}
    uint64_t previous=0;
    for(uint64_t i=0;i<size;++i) {
        uint64_t column=cont_read(lean_sarray_cptr(ids)+4*i,4);
        if(column>=c->columns || (i && column<=previous)) {cont_invalid(c,3,cursor,i);return;}
        uint64_t value=cont_read(lean_sarray_cptr(coeff)+c->width*i,c->width);
        if(!value || value>=c->p) {cont_invalid(c,4,cursor,i);return;}
        previous=column;
    }
    cont_replace(c,5,lean_uint64_to_nat(cursor+1));
}
/* The admitted 64-bit geometry has at most 524288 workspace bytes, so
   the model's USize addressability check succeeds before either charge. */
static void cont_workspace(continuation *c) {
    uint64_t dense_bytes=c->columns*c->width,slot_bytes=c->columns*4;
    uint64_t bytes=dense_bytes+slot_bytes;
    if(!cont_charge(c,3,4,bytes)) {cont_error(c,4);return;}
    if(!cont_work(c,bytes)) {cont_error(c,5);return;}
    lean_object *dense=lean_alloc_sarray(1,(size_t)dense_bytes,(size_t)dense_bytes);
    lean_object *slots=lean_alloc_sarray(1,(size_t)slot_bytes,(size_t)slot_bytes);
    if(dense_bytes) memset(lean_sarray_cptr(dense),0,(size_t)dense_bytes);
    if(slot_bytes) memset(lean_sarray_cptr(slots),0,(size_t)slot_bytes);
    HEX_GROEBNER_CONT_ALLOCATE(c->width);
    cont_replace(c,7,dense);cont_replace(c,8,slots);c->phase=3;
}
static int cont_target(continuation *c) {
    return lean_unbox(c->v[6])>=lean_array_size(c->v[2]);
}
static void cont_complete(continuation *c) {
    cont_replace(c,6,lean_uint64_to_nat(lean_unbox(c->v[6])+1));
    ++c->stats[5];c->phase=3;
}
static void cont_remainder(continuation *c,lean_obj_arg row) {
    lean_object *r=lean_alloc_ctor(0,3,0);lean_ctor_set(r,0,row);
    lean_ctor_set(r,1,lean_box(0));lean_inc(c->v[16]);lean_ctor_set(r,2,c->v[16]);
    c->v[11]=lean_array_push(c->v[11],r);
}
static void cont_zero(continuation *c) {
    if(c->independent && cont_target(c)) cont_remainder(c,cont_row(cont_empty(),cont_empty()));
    ++c->stats[7];cont_complete(c);
}
static int cont_inverse(continuation *c,uint64_t a,uint64_t *inverse) {
    uint64_t exponent=c->p-2,value=1;
    if(a==1) {*inverse=1;return 1;}
    HEX_GROEBNER_CONT_INVERSE();
    while(exponent) {
        if(exponent&1) {
            if(!cont_work(c,1)) {cont_error(c,5);return 0;}
            value=value*a%c->p;
        }
        exponent>>=1;
        if(exponent) {
            if(!cont_work(c,1)) {cont_error(c,5);return 0;}
            a=a*a%c->p;
        }
    }
    *inverse=value;return 1;
}
static void cont_install(continuation *c,lean_obj_arg row,uint64_t column,uint64_t inverse) {
    int target=cont_target(c);
    if(c->independent && target) cont_remainder(c,row);
    else {
        uint64_t id=lean_array_size(c->v[9]);
        lean_object *native=lean_alloc_ctor(0,3,0);
        lean_ctor_set(native,0,cont_take(row,0));lean_ctor_set(native,1,cont_take(row,1));
        lean_inc(c->v[16]);lean_ctor_set(native,2,c->v[16]);
        if(!lean_is_scalar(c->v[20])) {
            lean_object *cache=lean_ctor_get(c->v[20],0);
            uint8_t active=lean_ctor_get_uint8(cache,sizeof(void*));
            lean_object *prepared=NULL,*dense_row;
            uint64_t n=lean_sarray_size(lean_ctor_get(native,0))/4;
            const uint8_t *ids=lean_sarray_cptr(lean_ctor_get(native,0));
            uint64_t span=n ? cont_read(ids+(size_t)(n-1)*4,4)-cont_read(ids,4)+1 : 0;
            if(n>=128 && n<=4096 && n<span && 3*span<=4*n) {
                lean_object *work=lean_uint64_to_nat(c->limits[5]-c->stats[0]);
                lean_object *bytes=lean_uint64_to_nat(c->limits[4]-c->stats[3]);
                prepared=lean_hex_prepare_dense(c->p,c->v[1],native,work,bytes);
                lean_dec(work);lean_dec(bytes);
                dense_row=cont_take(prepared,0);
                c->stats[0]+=lean_unbox(lean_ctor_get(prepared,1));
                c->stats[3]+=lean_unbox(lean_ctor_get(prepared,2));
                lean_dec(prepared);
            } else {
                dense_row=lean_alloc_ctor(0,2,8);lean_inc(native);
                lean_ctor_set(dense_row,0,native);lean_ctor_set(dense_row,1,cont_empty());
                lean_ctor_set_uint32(dense_row,2*sizeof(void*),0);
                lean_ctor_set_uint32(dense_row,2*sizeof(void*)+4,0);
            }
            active=active || lean_sarray_size(lean_ctor_get(dense_row,1))!=0;
            lean_object *rows=cont_take(cache,0);lean_dec(c->v[20]);
            rows=lean_array_push(rows,dense_row);
            cache=lean_alloc_ctor(0,1,1);lean_ctor_set(cache,0,rows);
            lean_ctor_set_uint8(cache,sizeof(void*),active);
            c->v[20]=lean_alloc_ctor(1,1,0);lean_ctor_set(c->v[20],0,cache);
        }
        c->v[10]=lean_array_push(c->v[10],native);
        lean_object *pivot=lean_alloc_ctor(0,3,9);lean_ctor_set(pivot,0,row);
        lean_ctor_set(pivot,1,lean_box(0));lean_inc(c->v[16]);lean_ctor_set(pivot,2,c->v[16]);
        lean_ctor_set_uint64(pivot,3*sizeof(void*),inverse);
        lean_ctor_set_uint8(pivot,3*sizeof(void*)+8,(uint8_t)target);
        c->v[9]=lean_array_push(c->v[9],pivot);
        c->v[8]=lean_sarray_ensure_exclusive(c->v[8]);
        cont_write(lean_sarray_cptr(c->v[8])+column*4,4,id+1);
        if(!target) cont_replace(c,12,lean_uint64_to_nat(lean_unbox(c->v[12])+1));
    }
    cont_complete(c);
}
static void cont_input(continuation *c) {
    uint64_t input=lean_unbox(c->v[6]),nr=lean_array_size(c->v[2]);
    if(input>=nr+lean_array_size(c->v[3])) {c->phase=6;return;}
    if(!cont_work(c,1)) {cont_error(c,5);return;}
    lean_object *row=lean_array_get_core(c->v[input<nr?2:3],(size_t)(input<nr?input:input-nr));
    lean_object *ids=lean_ctor_get(row,0),*coeff=lean_ctor_get(row,1);
    uint64_t size=lean_sarray_size(ids)/4;
    lean_object *sugar=input<lean_array_size(c->v[4])?lean_array_get_core(c->v[4],(size_t)input):lean_box(0);
    lean_inc(sugar);cont_replace(c,16,sugar);
    if(!size) {cont_zero(c);return;}
    uint64_t first=cont_read(lean_sarray_cptr(ids),4);
    if(input<nr && !cont_read(lean_sarray_cptr(c->v[8])+first*4,4)) {
        uint64_t inverse;
        if(!cont_inverse(c,cont_read(lean_sarray_cptr(coeff),c->width),&inverse)) return;
        if(!cont_charge(c,2,3,size)) {cont_error(c,3);return;}
        if(!cont_charge(c,3,4,size*(4+c->width))) {cont_error(c,4);return;}
        lean_object *output;
        if(inverse==1) {lean_inc(row);output=row;}
        else {
            if(!cont_work(c,size)) {cont_error(c,5);return;}
            lean_object *scaled=lean_alloc_sarray(1,(size_t)(size*c->width),(size_t)(size*c->width));
            for(uint64_t i=0;i<size;++i) cont_write(lean_sarray_cptr(scaled)+i*c->width,c->width,
                cont_read(lean_sarray_cptr(coeff)+i*c->width,c->width)*inverse%c->p);
            lean_inc(ids);output=cont_row(ids,scaled);
        }
        cont_install(c,output,first,inverse);return;
    }
    if(!cont_work(c,size)) {cont_error(c,5);return;}
    lean_object *dense=lean_sarray_ensure_exclusive(c->v[7]);c->v[7]=cont_empty();
    for(uint64_t i=0;i<size;++i) {
        uint64_t col=cont_read(lean_sarray_cptr(ids)+i*4,4);
        cont_write(lean_sarray_cptr(dense)+col*c->width,c->width,
            cont_read(lean_sarray_cptr(coeff)+i*c->width,c->width));
    }
    lean_object *scan=lean_alloc_ctor(0,8,8);lean_ctor_set(scan,0,dense);
    lean_ctor_set(scan,1,lean_uint64_to_nat(first));
    lean_ctor_set(scan,2,lean_uint64_to_nat(cont_read(lean_sarray_cptr(ids)+(size-1)*4,4)));
    lean_ctor_set(scan,3,lean_uint64_to_nat(first));
    for(unsigned i=4;i<7;++i) lean_ctor_set(scan,i,lean_box(0));
    lean_inc(c->v[16]);lean_ctor_set(scan,7,c->v[16]);lean_ctor_set_uint64(scan,8*sizeof(void*),0);
    cont_replace(c,13,scan);
    cont_replace(c,19,lean_uint64_to_nat((c->columns*(c->columns+2)+4095)/4096+1));c->phase=4;
}
/* Preserve the scan cursor/last/prepayment fields while moving its accumulator. */
static lean_object *cont_scan_dense(continuation *c) {
    lean_object *old=c->v[13],*dense=cont_take(old,0),*scan=lean_alloc_ctor(0,8,8);
    lean_ctor_set(scan,0,cont_empty());
    for(unsigned i=1;i<8;++i) lean_ctor_set(scan,i,cont_take(old,i));
    lean_ctor_set_uint64(scan,8*sizeof(void*),lean_ctor_get_uint64(old,8*sizeof(void*)));
    cont_replace(c,13,scan);return dense;
}
static void cont_scan(continuation *c) {
    uint64_t quanta=lean_unbox(c->v[19]);
    if(!quanta) {cont_internal(c);return;}
    cont_replace(c,19,lean_uint64_to_nat(quanta-1));
    lean_object *remaining=lean_uint64_to_nat(c->limits[5]-c->stats[0]);
    lean_object *out;
    lean_object *cache=lean_is_scalar(c->v[20])?NULL:lean_ctor_get(c->v[20],0);
    if(cache && lean_ctor_get_uint8(cache,sizeof(void*))) out=lean_hex_dense_transition(c->p,c->v[1],c->v[8],
        lean_ctor_get(cache,0),c->v[13],lean_box(4096),remaining,lean_box(0),0);
    else out=lean_hex_scan_transition(c->p,c->v[8],c->v[10],c->v[13],
        lean_box(4096),remaining,lean_box(0),0);
    c->v[13]=NULL;lean_dec(remaining);
    uint8_t status=lean_ctor_get_uint8(out,5*sizeof(void*));
    uint64_t work=lean_unbox(lean_ctor_get(out,2)),reductions=lean_unbox(lean_ctor_get(out,3));
    if(!cont_work(c,work)) {
        lean_dec(out);c->v[13]=cont_empty_scan();cont_error(c,5);return;
    }
    c->v[13]=cont_take(out,0);lean_dec(out);
    c->stats[6]+=reductions;
    if(status==2) {cont_error(c,5);return;}
    if(status==3) {cont_error(c,6);return;}
    if(status!=0 && status!=1) {cont_internal(c);return;}
    if(status!=1) {if(quanta==1) cont_internal(c);return;}
    cont_replace(c,16,cont_take(c->v[13],7));
    uint64_t leading=lean_unbox(lean_ctor_get(c->v[13],4));
    if(!leading) {cont_replace(c,7,cont_scan_dense(c));cont_zero(c);return;}
    uint64_t column=leading-1,inverse=1;
    if(!(c->independent && cont_target(c))) {
        lean_object *dense=lean_ctor_get(c->v[13],0);
        if(!cont_inverse(c,cont_read(lean_sarray_cptr(dense)+column*c->width,c->width),&inverse)) return;
    }
    uint64_t last=lean_unbox(lean_ctor_get(c->v[13],2));
    if(!cont_work(c,last+1-column)) {cont_error(c,5);return;}
    lean_object *gather=lean_alloc_ctor(0,4,0);lean_ctor_set(gather,0,cont_scan_dense(c));
    lean_ctor_set(gather,1,cont_empty());lean_ctor_set(gather,2,cont_empty());
    lean_ctor_set(gather,3,lean_uint64_to_nat(column));cont_replace(c,14,gather);
    cont_replace(c,15,lean_uint64_to_nat(column));
    cont_replace(c,19,lean_uint64_to_nat((last+1-column+4095)/4096+1));
    c->inverse=inverse;c->phase=5;
}
static void cont_gather(continuation *c) {
    uint64_t quanta=lean_unbox(c->v[19]);
    if(!quanta) {cont_internal(c);return;}
    cont_replace(c,19,lean_uint64_to_nat(quanta-1));
    lean_object *stop=lean_uint64_to_nat(lean_unbox(lean_ctor_get(c->v[13],2))+1);
    lean_object *entries=lean_uint64_to_nat(c->limits[3]-c->stats[2]);
    lean_object *bytes=lean_uint64_to_nat(c->limits[4]-c->stats[3]);
    lean_object *work=lean_uint64_to_nat(c->limits[5]-c->stats[0]);
    lean_object *out=lean_hex_gather(c->p,c->v[14],stop,lean_box(4096),entries,bytes,work,c->inverse);
    c->v[14]=NULL;lean_dec(stop);lean_dec(entries);lean_dec(bytes);lean_dec(work);
    uint8_t status=lean_ctor_get_uint8(out,4*sizeof(void*));
    uint64_t ne=lean_unbox(lean_ctor_get(out,1)),nb=lean_unbox(lean_ctor_get(out,2)),nw=lean_unbox(lean_ctor_get(out,3));
    unsigned failure=0;
    if(!cont_charge(c,2,3,ne)) failure=3;
    else if(!cont_charge(c,3,4,nb)) failure=4;
    else if(!cont_work(c,nw)) failure=5;
    if(failure) {lean_dec(out);c->v[14]=cont_empty_gather();cont_error(c,failure);return;}
    c->v[14]=cont_take(out,0);lean_dec(out);
    if(status==2 || status==3 || status==4) {cont_error(c,status+1);return;}
    if(status==5) {
        lean_object *r=lean_alloc_ctor(0,1,0);lean_ctor_set(r,0,lean_box(0));
        lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,r);
        cont_replace(c,18,some);c->phase=7;return;
    }
    if(status!=0 && status!=1) {cont_internal(c);return;}
    if(status!=1) {if(quanta==1) cont_internal(c);return;}
    lean_object *state=c->v[14];
    cont_replace(c,7,cont_take(state,0));
    lean_object *row=cont_row(cont_take(state,1),cont_take(state,2));
    lean_object *gather=lean_alloc_ctor(0,4,0);lean_ctor_set(gather,0,cont_empty());
    lean_ctor_set(gather,1,cont_empty());lean_ctor_set(gather,2,cont_empty());lean_ctor_set(gather,3,lean_box(0));
    cont_replace(c,14,gather);cont_install(c,row,lean_unbox(c->v[15]),c->inverse);
}

/* Each call performs at most cap*(8c+2r+4224) ordinary phase units;
   cache mode uses 8c+3r+65536, including bounded pivot preparation, plus at most one copy
   of each shared buffer/array: conservatively 16c bytes and 2r object entries (3r with caches).
   Here c is columns and r is input rows. This is a hard shape-dependent bound,
   not a count of machine instructions. Nat metadata retains its ordinary bit
   complexity. The private shape
   check admits <=65536 columns and input rows; larger states take no transition
   here. Checks and final ordering use the exported Lean phase. The native workspace
   phase charges bytes before allocating bounded zeroed buffers. Validation
   examines at most c+1 entries per native phase, with larger well-shaped rows
   handled by the checked Lean phase,
   so malformed rows and arbitrary Nat resource limits retain their exact
   failures and counters. Scan and gather each advance at most 4096 steps. */
LEAN_EXPORT lean_obj_res lean_hex_matrix_advance(lean_obj_arg state,b_lean_obj_arg steps) {
    if(lean_is_scalar(state) || lean_obj_tag(state)!=0 || lean_ctor_num_objs(state)!=21) return state;
    lean_object *columns=lean_ctor_get(state,1);
    if(!lean_is_scalar(columns) || lean_unbox(columns)>65536) return state;
    uint64_t rows=lean_array_size(lean_ctor_get(state,2))+lean_array_size(lean_ctor_get(state,3));
    if(rows>65536) return state;
    uint64_t overhead=lean_ctor_get_uint64(state,21*sizeof(void*))==INT32_MAX &&
        lean_ctor_get_uint8(lean_ctor_get(state,0),7*sizeof(void*))?65536:4224;
    uint64_t cols=lean_unbox(columns),cap=UINT64_C(1048576)/(8*cols+(overhead==65536?3:2)*rows+overhead);
    if(!cap) cap=1;
    uint64_t count=lean_is_scalar(steps)?lean_unbox(steps):cap;
    if(count>cap) count=cap;
    if(!count) return state;
    HEX_GROEBNER_CONT_BEGIN(cols,rows,count,overhead);
    continuation c;cont_unpack(&c,state);
    uint8_t initial_phase=c.phase;
    int fast=cont_counts(&c),dirty=0;
    for(uint64_t i=0;i<count && c.phase!=7;++i) {
        HEX_GROEBNER_CONT_TICK();
        if(fast && (c.phase>=1 && c.phase<=5) && cont_bounds(&c)) {
            HEX_GROEBNER_CONT_PHASE(c.phase);
            if(c.phase==1) cont_validate(&c);
            else if(c.phase==2) cont_workspace(&c);
            else if(c.phase==3) cont_input(&c);
            else if(c.phase==4) cont_scan(&c);
            else cont_gather(&c);
            dirty=1;
        } else {
            if(dirty) cont_save_counts(&c);
            state=lean_hex_matrix_step(cont_pack(&c));cont_unpack(&c,state);
            fast=cont_counts(&c);dirty=0;
        }
    }
    if(dirty) cont_save_counts(&c);
    HEX_GROEBNER_CONT_END();
    HEX_GROEBNER_CONT_SUCCESS(initial_phase,c.phase,c.v[18],c.stats[6],c.stats[7]);
    return cont_pack(&c);
}

#else
LEAN_EXPORT lean_obj_res lean_hex_matrix_advance(lean_obj_arg state,b_lean_obj_arg steps) {
    (void)steps;return state;
}
#endif
