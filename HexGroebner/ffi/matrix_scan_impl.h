/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
/* Included once for the scalar implementation and once for the AVX2 implementation. */
HEX_SCAN_ATTRIBUTE
static lean_obj_res HEX_SCAN_NAME(uint64_t p,
        b_lean_obj_arg slots,b_lean_obj_arg pivots,lean_obj_arg initial,
        b_lean_obj_arg quantum_arg,b_lean_obj_arg work_arg,b_lean_obj_arg trace_arg,
        uint8_t provenance) {
    unsigned w=HEX_SCAN_WIDTH;
    lean_object *dense=lean_ctor_get(initial,0);
    size_t db=lean_sarray_size(dense), count=lean_array_size(pivots);
    uint64_t columns=db/w;
    uint64_t quantum=bounded_nat(quantum_arg,4097);
    uint64_t col=bounded_nat(lean_ctor_get(initial,1),UINT64_C(4294967296));
    uint64_t last=bounded_nat(lean_ctor_get(initial,2),UINT64_C(4294967296));
    uint64_t charged=bounded_nat(lean_ctor_get(initial,3),UINT64_C(4294967296));
    uint64_t leading=bounded_nat(lean_ctor_get(initial,4),UINT64_C(4294967296));
    uint64_t pending=bounded_nat(lean_ctor_get(initial,5),UINT64_C(4294967296));
    uint64_t entry=bounded_nat(lean_ctor_get(initial,6),UINT64_C(4294967296));
    uint64_t factor=lean_ctor_get_uint64(initial,8*sizeof(void*));
    if(p<2 || p>=UINT64_C(2147483648) || quantum>4096 || db%w ||
       columns>UINT32_MAX || columns>SIZE_MAX/4 || lean_sarray_size(slots)!=columns*4 ||
       col>columns || (columns && last>=columns) || leading>columns ||
       pending>count || count>UINT32_MAX || charged>columns || entry>UINT32_MAX ||
       (!pending && entry) || (pending && col>=columns) || (!columns && last) || factor>=p)
        return result(initial,lean_alloc_array(0,0),0,0,0,4);
    uint64_t work_limit=bounded_nat(work_arg,UINT64_C(1)<<45);
    uint64_t trace_limit=bounded_nat(trace_arg,4096);
    uint64_t event_capacity=quantum<trace_limit?quantum:trace_limit;
    if(event_capacity>8) event_capacity=8;
    lean_object *events=lean_alloc_array(0,provenance?(size_t)event_capacity:0);
    lean_object *sugar=lean_ctor_get(initial,7);
    lean_inc(dense);lean_inc(sugar);
    lean_object *alias=NULL;
    if(dense==slots) {alias=dense;lean_inc(alias);}
    lean_dec(initial);
    dense=lean_sarray_ensure_exclusive(dense);
    uint8_t *data=lean_sarray_cptr(dense);
    const uint8_t *slot_bytes=lean_sarray_cptr(slots);
    uint64_t work=0,reductions=0,traces=0;
    uint8_t status=0;
    uint64_t reciprocal=0;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    if(w<4) reciprocal=UINT64_C(4294967296)/p;
    else {reciprocal=UINT64_MAX/p;if(UINT64_MAX%p==p-1) ++reciprocal;}
#endif
#if HEX_SCAN_VECTOR
    uint32_t reduction=w<4?(uint32_t)(UINT64_C(4294967296)/p):hex_mont32_inverse((uint32_t)p);
#endif
    for(uint64_t tick=0;tick<quantum;++tick) {
        if(pending) {
            lean_object *pivot=lean_array_cptr(pivots)[pending-1];
            uint64_t size;
            if(!geometry(pivot,w,&size) || entry>size) {status=4;break;}
            if(entry==size) {
                ++reductions;
                if(provenance) {
                    if(traces>=trace_limit) {status=3;break;}
                    lean_object *event=lean_alloc_ctor(0,2,0);
                    lean_ctor_set(event,0,lean_uint64_to_nat(pending-1));
                    lean_ctor_set(event,1,lean_box_uint64(factor));
                    events=lean_array_push(events,event);++traces;
                }
                pending=0;entry=0;++col;
            } else {
                const uint8_t *cs=lean_sarray_cptr(lean_ctor_get(pivot,0));
                const uint8_t *vs=lean_sarray_cptr(lean_ctor_get(pivot,1));
                uint64_t updates=size-entry;
                if(updates>quantum-tick) updates=quantum-tick;
#if HEX_SCAN_VECTOR
                if(updates>=8) {
                    uint32_t multiplier=w<4?(uint32_t)factor:(uint32_t)((factor<<32)%p);
                    for(uint64_t k=0;k<updates;++k) {
                        if(updates-k>=8 && hex_scan8(data,cs,vs,(size_t)entry,columns,
                                (uint32_t)p,multiplier,reduction,w)) {
                            entry+=8;k+=7;continue;
                        }
                        if(!scalar_update(data,cs,vs,w,columns,entry,p,factor,reciprocal)) {status=4;break;}
                        ++entry;
                    }
                } else
#endif
                {
                    for(uint64_t k=0;k<updates;++k) {
                        if(!scalar_update(data,cs,vs,w,columns,entry,p,factor,reciprocal)) {status=4;break;}
                        ++entry;
                    }
                }
                if(status==4) break;
                tick+=updates-1;
            }
        } else {
            if(col>=columns || col>last) {status=1;break;}
            if(col>=charged) {
                uint64_t stop=col+64<last+1?col+64:last+1;
                uint64_t charge=stop-col;
                if(work+charge>work_limit) {status=2;break;}
                work+=charge;charged=stop;
            }
            uint64_t a=rd(data+(size_t)col*w,w);
            if(a>=p) {status=4;break;}
            uint64_t slot=rd(slot_bytes+(size_t)col*4,4);
            if(!a || !slot) {if(a && !leading) leading=col+1;++col;}
            else {
                if(slot>count) {status=4;break;}
                lean_object *pivot=lean_array_cptr(pivots)[slot-1];
                uint64_t size;
                if(!geometry(pivot,w,&size)) {status=4;break;}
                const uint8_t *cs=lean_sarray_cptr(lean_ctor_get(pivot,0));
                const uint8_t *vs=lean_sarray_cptr(lean_ctor_get(pivot,1));
                if(rd(cs,4)!=col || rd(vs,w)!=1) {status=4;break;}
                uint64_t end=rd(cs+(size_t)(size-1)*4,4);
                if(end>=columns) {status=4;break;}
                if(end>last) last=end;
                lean_object *label=lean_ctor_get(pivot,2);
                if(lean_nat_dec_lt(sugar,label)) {lean_inc(label);lean_dec(sugar);sugar=label;}
                if(work+size>work_limit) {status=2;break;}
                work+=size;pending=slot;entry=0;factor=a;
            }
        }
    }
    if(alias) lean_dec(alias);
    lean_object *state=lean_alloc_ctor(0,8,8);
    lean_ctor_set(state,0,dense);lean_ctor_set(state,1,lean_uint64_to_nat(col));
    lean_ctor_set(state,2,lean_uint64_to_nat(last));lean_ctor_set(state,3,lean_uint64_to_nat(charged));
    lean_ctor_set(state,4,lean_uint64_to_nat(leading));lean_ctor_set(state,5,lean_uint64_to_nat(pending));
    lean_ctor_set(state,6,lean_uint64_to_nat(entry));lean_ctor_set(state,7,sugar);
    lean_ctor_set_uint64(state,8*sizeof(void*),factor);
    return result(state,events,work,reductions,traces,status);
}
