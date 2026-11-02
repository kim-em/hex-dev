/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

extern lean_obj_res lean_hex_scan_transition(uint64_t,b_lean_obj_arg,b_lean_obj_arg,
    lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,uint8_t);
extern lean_obj_res lean_hex_gather(uint64_t,lean_obj_arg,b_lean_obj_arg,
    b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,uint64_t);

#ifndef HEX_GROEBNER_MATRIX_ACCEPTED
#define HEX_GROEBNER_MATRIX_ACCEPTED() ((void)0)
#endif
#ifndef HEX_GROEBNER_MATRIX_DEFERRED
#define HEX_GROEBNER_MATRIX_DEFERRED() ((void)0)
#endif

#define MATRIX_QUANTUM UINT64_C(1048576)

typedef struct {
    uint64_t limits[7],stats[8],p,columns;
    unsigned width;
    lean_object *dense,*slots,*pivots,*native_pivots,*remainders;
    uint64_t rank;
} matrix_context;

static uint64_t matrix_read(const uint8_t *p,unsigned w) {
    uint64_t x=p[0];
    if(w>1) x|=(uint64_t)p[1]<<8;
    if(w>2) x|=(uint64_t)p[2]<<16 | (uint64_t)p[3]<<24;
    return x;
}
static void matrix_write(uint8_t *p,unsigned w,uint64_t x) {
    p[0]=(uint8_t)x;
    if(w>1) p[1]=(uint8_t)(x>>8);
    if(w>2) {p[2]=(uint8_t)(x>>16);p[3]=(uint8_t)(x>>24);}
}
static int matrix_charge(uint64_t *count,uint64_t amount,uint64_t limit) {
    if(*count>limit || amount>limit-*count) return 0;
    *count+=amount;return 1;
}
static int matrix_work(matrix_context *c,uint64_t n) {
    uint64_t cap=c->limits[5]<MATRIX_QUANTUM?c->limits[5]:MATRIX_QUANTUM;
    return matrix_charge(&c->stats[0],n,cap);
}
static int matrix_bytes(matrix_context *c,uint64_t n) {
    return matrix_charge(&c->stats[3],n,c->limits[4]);
}
static lean_object *matrix_empty(void) {
    return lean_mk_empty_array_with_capacity(lean_box(0));
}
static lean_object *matrix_zeros(size_t n) {
    lean_object *a=lean_alloc_sarray(1,n,n);
    memset(lean_sarray_cptr(a),0,n);return a;
}
static lean_object *matrix_take(b_lean_obj_arg o,unsigned field) {
    lean_object *x=lean_ctor_get(o,field);lean_inc(x);return x;
}
static lean_object *matrix_row(lean_obj_arg columns,lean_obj_arg coefficients) {
    lean_object *row=lean_alloc_ctor(0,2,0);
    lean_ctor_set(row,0,columns);lean_ctor_set(row,1,coefficients);return row;
}
static int matrix_inverse(matrix_context *c,uint64_t a,uint64_t *inverse) {
    if(a==1) {*inverse=1;return 1;}
    uint64_t exponent=c->p-2,value=1;
    while(exponent) {
        if(exponent&1) {
            if(!matrix_work(c,1)) return 0;
            value=(value*a)%c->p;
        }
        exponent>>=1;
        if(exponent) {
            if(!matrix_work(c,1)) return 0;
            a=(a*a)%c->p;
        }
    }
    *inverse=value;return 1;
}
static void matrix_cleanup(matrix_context *c) {
    if(c->dense) lean_dec(c->dense);
    if(c->slots) lean_dec(c->slots);
    if(c->pivots) lean_dec(c->pivots);
    if(c->native_pivots) lean_dec(c->native_pivots);
    if(c->remainders) lean_dec(c->remainders);
}
static int matrix_install(matrix_context *c,lean_obj_arg row,uint64_t column,
        uint64_t inverse,uint64_t sugar,uint8_t from_target) {
    if(column>=c->columns) {lean_dec(row);return 0;}
    size_t id=lean_array_size(c->pivots);
    lean_object *native=lean_alloc_ctor(0,3,0);
    lean_ctor_set(native,0,matrix_take(row,0));
    lean_ctor_set(native,1,matrix_take(row,1));
    lean_ctor_set(native,2,lean_uint64_to_nat(sugar));
    c->native_pivots=lean_array_push(c->native_pivots,native);
    lean_object *pivot=lean_alloc_ctor(0,3,9);
    lean_ctor_set(pivot,0,row);lean_ctor_set(pivot,1,lean_box(0));
    lean_ctor_set(pivot,2,lean_uint64_to_nat(sugar));
    lean_ctor_set_uint64(pivot,3*sizeof(void*),inverse);
    lean_ctor_set_uint8(pivot,3*sizeof(void*)+8,from_target);
    c->pivots=lean_array_push(c->pivots,pivot);
    matrix_write(lean_sarray_cptr(c->slots)+(size_t)column*4,4,id+1);
    if(!from_target) ++c->rank;
    return 1;
}
static void matrix_remainder(matrix_context *c,lean_obj_arg row,uint64_t sugar) {
    lean_object *out=lean_alloc_ctor(0,3,0);
    lean_ctor_set(out,0,row);lean_ctor_set(out,1,lean_box(0));
    lean_ctor_set(out,2,lean_uint64_to_nat(sugar));
    c->remainders=lean_array_push(c->remainders,out);
}

/* The accumulator moves into each existing bounded scan call. Borrowed input
   rows and pivot buffers remain immutable. Only the returned owned accumulator
   is recovered; intermediate result/state headers are released immediately. */
static int matrix_scan(matrix_context *c,uint64_t first,uint64_t *last,
        uint64_t *leading,uint64_t *sugar) {
    lean_object *state=lean_alloc_ctor(0,8,8);
    lean_ctor_set(state,0,c->dense);c->dense=NULL;
    lean_ctor_set(state,1,lean_uint64_to_nat(first));
    lean_ctor_set(state,2,lean_uint64_to_nat(*last));
    lean_ctor_set(state,3,lean_uint64_to_nat(first));
    for(unsigned i=4;i<7;++i) lean_ctor_set(state,i,lean_box(0));
    lean_ctor_set(state,7,lean_uint64_to_nat(*sugar));
    lean_ctor_set_uint64(state,8*sizeof(void*),0);
    uint64_t cap=c->limits[5]<MATRIX_QUANTUM?c->limits[5]:MATRIX_QUANTUM;
    uint64_t calls=(c->columns*(c->columns+2)+4095)/4096+1;
    for(uint64_t call=0;call<calls;++call) {
        lean_object *remaining=lean_uint64_to_nat(cap-c->stats[0]);
        lean_object *out=lean_hex_scan_transition(c->p,c->slots,c->native_pivots,
            state,lean_box(4096),remaining,lean_box(0),0);
        state=NULL;lean_dec(remaining);
        uint8_t status=lean_ctor_get_uint8(out,5*sizeof(void*));
        uint64_t work=lean_unbox(lean_ctor_get(out,2));
        uint64_t reductions=lean_unbox(lean_ctor_get(out,3));
        if(!matrix_work(c,work)) {lean_dec(out);return 0;}
        c->stats[6]+=reductions;
        if(status==1) {
            lean_object *next=lean_ctor_get(out,0);
            c->dense=matrix_take(next,0);
            *last=lean_unbox(lean_ctor_get(next,2));
            *leading=lean_unbox(lean_ctor_get(next,4));
            *sugar=lean_unbox(lean_ctor_get(next,7));
            lean_dec(out);return 1;
        }
        if(status!=0) {lean_dec(out);return 0;}
        state=matrix_take(out,0);lean_dec(out);
    }
    lean_dec(state);return 0;
}
static lean_object *matrix_gather(matrix_context *c,uint64_t column,uint64_t last,
        uint64_t inverse) {
    if(!matrix_work(c,last+1-column)) return NULL;
    lean_object *state=lean_alloc_ctor(0,4,0);
    lean_ctor_set(state,0,c->dense);c->dense=NULL;
    lean_ctor_set(state,1,matrix_zeros(0));lean_ctor_set(state,2,matrix_zeros(0));
    lean_ctor_set(state,3,lean_uint64_to_nat(column));
    uint64_t cap=c->limits[5]<MATRIX_QUANTUM?c->limits[5]:MATRIX_QUANTUM;
    uint64_t calls=(last+1-column+4095)/4096+1;
    for(uint64_t call=0;call<calls;++call) {
        lean_object *stop=lean_uint64_to_nat(last+1);
        lean_object *entries=lean_uint64_to_nat(c->limits[3]-c->stats[2]);
        lean_object *bytes=lean_uint64_to_nat(c->limits[4]-c->stats[3]);
        lean_object *work=lean_uint64_to_nat(cap-c->stats[0]);
        lean_object *out=lean_hex_gather(c->p,state,stop,lean_box(4096),entries,bytes,work,inverse);
        state=NULL;lean_dec(stop);lean_dec(entries);lean_dec(bytes);lean_dec(work);
        uint8_t status=lean_ctor_get_uint8(out,4*sizeof(void*));
        if(!matrix_charge(&c->stats[2],lean_unbox(lean_ctor_get(out,1)),c->limits[3]) ||
           !matrix_bytes(c,lean_unbox(lean_ctor_get(out,2))) ||
           !matrix_work(c,lean_unbox(lean_ctor_get(out,3)))) {lean_dec(out);return NULL;}
        if(status==1) {
            lean_object *next=lean_ctor_get(out,0);
            c->dense=matrix_take(next,0);
            lean_object *row=matrix_row(matrix_take(next,1),matrix_take(next,2));
            lean_dec(out);return row;
        }
        if(status!=0) {lean_dec(out);return NULL;}
        state=matrix_take(out,0);lean_dec(out);
    }
    lean_dec(state);return NULL;
}

/* ABI: PrimeField is its unboxed uint64 modulus (prime 2 <= p < 2^31).
   All five object arguments are borrowed: MatrixLimits has seven Nat fields,
   columns is Nat, rows are Lean Arrays of SparseRow(two ByteArrays), sugars is
   Array Nat. independent is uint8 Bool. Limits above Nat's scalar range saturate
   above every possible accepted total; sugars must be scalar Nats.
   Only a 64-bit ABI with <=4096 columns/1024 reducers/64 targets is admitted.
   Distinct reducer leading columns and the conservative 2^20 work bound are
   checked before allocation; canonical row validation precedes elimination.
   Dense workspace is owned; inputs, including overlapping arrays, are immutable.
   Some(Result(Except.ok(Prod(Echelon(rows,rank,emptyTrace),remainders)),stats))
   contains exact reference rows and eight Nat counters, using the layouts in
   Elimination.lean. None releases all local owners and permits portable
   continuation outside C. Charged speculative work before a decline is bounded
   by min(parent remaining work,2^20); such a decline implies reference failure.
   Scan/gather symbols come from HexGroebnerMatrixNative. Lake links its complete
   imported shared library; keep that carrier dependency and these ABIs intact. */
LEAN_EXPORT lean_obj_res lean_hex_groebner_eliminate_matrix(uint64_t p,
        b_lean_obj_arg limits,b_lean_obj_arg column_arg,b_lean_obj_arg reducers,
        b_lean_obj_arg targets,b_lean_obj_arg sugars,uint8_t independent) {
    matrix_context c={0};
    if(sizeof(void*)!=8 || p<2 || p>=UINT64_C(2147483648) ||
       !lean_is_scalar(column_arg)) goto defer;
    c.p=p;c.width=p<=256?1:p<=65536?2:4;c.columns=lean_unbox(column_arg);
    size_t nr=lean_array_size(reducers),nt=lean_array_size(targets);
    if(c.columns>4096 || nr>1024 || nt>64) goto defer;
    size_t rows=nr+nt,ns=lean_array_size(sugars);
    if(ns && ns!=rows) goto defer;
    for(unsigned i=0;i<7;++i) {
        lean_object *x=lean_ctor_get(limits,i);
        c.limits[i]=lean_is_scalar(x)?lean_unbox(x):UINT64_MAX/2;
    }
    if(c.columns>c.limits[0] || rows>c.limits[1]) goto defer;
    for(size_t i=0;i<ns;++i) if(!lean_is_scalar(lean_array_cptr(sugars)[i])) goto defer;
    uint64_t workspace=c.columns*(c.width+4);
    if(c.limits[5]<2*rows+workspace || c.limits[4]<workspace) goto defer;
    uint64_t entries=0;
    for(size_t i=0;i<rows;++i) {
        lean_object *row=lean_array_cptr(i<nr?reducers:targets)[i<nr?i:i-nr];
        size_t cb=lean_sarray_size(lean_ctor_get(row,0));
        size_t vb=lean_sarray_size(lean_ctor_get(row,1));
        size_t n=cb/4;
        if(cb%4 || n>MATRIX_QUANTUM/2 || entries>MATRIX_QUANTUM/2-n ||
           vb!=n*c.width) goto defer;
        entries+=n;
    }
    uint64_t bound=rows*65+2*entries+workspace+
        nt*(entries+(nt+3)*c.columns+64)+c.columns;
    if(bound>MATRIX_QUANTUM) goto defer;
    uint8_t seen[512]={0};
    for(size_t i=0;i<nr;++i) {
        lean_object *cs=lean_ctor_get(lean_array_cptr(reducers)[i],0);
        if(!lean_sarray_size(cs)) continue;
        uint64_t col=matrix_read(lean_sarray_cptr(cs),4);
        if(col>=c.columns || (seen[col/8]&(1u<<(col%8)))) goto defer;
        seen[col/8]|=(uint8_t)(1u<<(col%8));
    }
    /* Validate all borrowed rows before allocating elimination state. */
    for(size_t i=0;i<rows;++i) {
        lean_object *row=lean_array_cptr(i<nr?reducers:targets)[i<nr?i:i-nr];
        lean_object *cs=lean_ctor_get(row,0),*vs=lean_ctor_get(row,1);
        size_t n=lean_sarray_size(cs)/4;
        if(!matrix_work(&c,1) ||
           !matrix_charge(&c.stats[1],n,c.limits[2]) ||
           !matrix_bytes(&c,n*(4+c.width)) || !matrix_work(&c,n)) goto defer;
        uint64_t previous=0;
        for(size_t j=0;j<n;++j) {
            uint64_t col=matrix_read(lean_sarray_cptr(cs)+j*4,4);
            uint64_t value=matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width);
            if(col>=c.columns || (j && col<=previous) || !value || value>=p) goto defer;
            previous=col;
        }
    }
    if(!matrix_bytes(&c,workspace) || !matrix_work(&c,workspace)) goto defer;
    c.dense=matrix_zeros((size_t)c.columns*c.width);
    c.slots=matrix_zeros((size_t)c.columns*4);
    c.pivots=matrix_empty();c.native_pivots=matrix_empty();c.remainders=matrix_empty();
    for(size_t i=0;i<rows;++i) {
        uint8_t target=i>=nr;
        lean_object *row=lean_array_cptr(target?targets:reducers)[target?i-nr:i];
        lean_object *cs=lean_ctor_get(row,0),*vs=lean_ctor_get(row,1);
        size_t n=lean_sarray_size(cs)/4;
        uint64_t sugar=ns?lean_unbox(lean_array_cptr(sugars)[i]):0;
        if(!matrix_work(&c,1)) goto defer;
        if(!n) {
            if(independent && target)
                matrix_remainder(&c,matrix_row(matrix_zeros(0),matrix_zeros(0)),sugar);
            ++c.stats[7];++c.stats[5];continue;
        }
        uint64_t first=matrix_read(lean_sarray_cptr(cs),4);
        if(!target) {
            uint64_t inverse;
            if(!matrix_inverse(&c,matrix_read(lean_sarray_cptr(vs),c.width),&inverse) ||
               !matrix_charge(&c.stats[2],n,c.limits[3]) ||
               !matrix_bytes(&c,n*(4+c.width))) goto defer;
            lean_object *output;
            if(inverse==1) {lean_inc(row);output=row;}
            else {
                if(!matrix_work(&c,n)) goto defer;
                lean_object *coeff=lean_alloc_sarray(1,n*c.width,n*c.width);
                for(size_t j=0;j<n;++j) {
                    uint64_t value=matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width);
                    matrix_write(lean_sarray_cptr(coeff)+j*c.width,c.width,(value*inverse)%p);
                }
                output=matrix_row(matrix_take(row,0),coeff);
            }
            if(!matrix_install(&c,output,first,inverse,sugar,0)) goto defer;
        } else {
            if(!matrix_work(&c,n)) goto defer;
            for(size_t j=0;j<n;++j) {
                uint64_t col=matrix_read(lean_sarray_cptr(cs)+j*4,4);
                matrix_write(lean_sarray_cptr(c.dense)+(size_t)col*c.width,c.width,
                    matrix_read(lean_sarray_cptr(vs)+j*c.width,c.width));
            }
            uint64_t last=matrix_read(lean_sarray_cptr(cs)+(n-1)*4,4),leading=0;
            if(!matrix_scan(&c,first,&last,&leading,&sugar)) goto defer;
            if(leading) {
                uint64_t col=leading-1,inverse=1;
                if(col>=c.columns || last>=c.columns || col>last) goto defer;
                if(!independent && !matrix_inverse(&c,
                    matrix_read(lean_sarray_cptr(c.dense)+(size_t)col*c.width,c.width),&inverse))
                    goto defer;
                lean_object *output=matrix_gather(&c,col,last,inverse);
                if(!output) goto defer;
                if(independent) matrix_remainder(&c,output,sugar);
                else if(!matrix_install(&c,output,col,inverse,sugar,1)) goto defer;
            } else {
                if(independent)
                    matrix_remainder(&c,matrix_row(matrix_zeros(0),matrix_zeros(0)),sugar);
                ++c.stats[7];
            }
        }
        ++c.stats[5];
    }
    lean_object *ordered=matrix_empty();
    if(!independent) {
        if(!matrix_work(&c,c.columns)) {lean_dec(ordered);goto defer;}
        for(size_t col=0;col<(size_t)c.columns;++col) {
            uint64_t slot=matrix_read(lean_sarray_cptr(c.slots)+col*4,4);
            if(slot) {
                lean_object *pivot=lean_array_cptr(c.pivots)[slot-1];lean_inc(pivot);
                ordered=lean_array_push(ordered,pivot);
            }
        }
    }
    lean_object *echelon=lean_alloc_ctor(0,3,0);
    lean_ctor_set(echelon,0,ordered);lean_ctor_set(echelon,1,lean_uint64_to_nat(c.rank));
    lean_ctor_set(echelon,2,matrix_empty());
    lean_object *pair=lean_alloc_ctor(0,2,0);
    lean_ctor_set(pair,0,echelon);lean_ctor_set(pair,1,c.remainders);c.remainders=NULL;
    lean_object *ok=lean_alloc_ctor(1,1,0);lean_ctor_set(ok,0,pair);
    lean_object *stats=lean_alloc_ctor(0,8,0);
    for(unsigned i=0;i<8;++i) lean_ctor_set(stats,i,lean_uint64_to_nat(c.stats[i]));
    lean_object *result=lean_alloc_ctor(0,2,0);
    lean_ctor_set(result,0,ok);lean_ctor_set(result,1,stats);
    lean_object *some=lean_alloc_ctor(1,1,0);lean_ctor_set(some,0,result);
    matrix_cleanup(&c);HEX_GROEBNER_MATRIX_ACCEPTED();return some;
defer:
    matrix_cleanup(&c);HEX_GROEBNER_MATRIX_DEFERRED();return lean_box(0);
}
