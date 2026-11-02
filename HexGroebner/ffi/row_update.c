/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */

#ifndef HEX_GROEBNER_NO_LEAN
#include <lean/lean.h>
#endif
#include <stdint.h>
#include <stddef.h>
#include <string.h>

/* Implements Native.subtractPortable exactly. Logical arrays are byte arrays,
   with explicit little-endian u32 columns and 1/2/4-byte modular residues.
   All sizes/offsets are checked before access. The public matrix boundary
   already validates complete rows; these checks also protect direct calls.
   `dense` is owned; columns and coefficients are borrowed and may alias it.
   No retained pointer outlives this call. Invalid input returns Option.none;
   no partially updated buffer is returned. Calls process <=4096 entries. */

static inline uint64_t read_le(const uint8_t *p, unsigned width) {
    if (width == 1) return p[0];
    uint64_t value = (uint64_t)p[0] | ((uint64_t)p[1] << 8);
    if (width == 4) value |= ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24);
    return value;
}

static inline void write_le(uint8_t *p, unsigned width, uint64_t value) {
    p[0] = (uint8_t)value;
    if (width != 1) p[1] = (uint8_t)(value >> 8);
    if (width == 4) {
        p[2] = (uint8_t)(value >> 16);
        p[3] = (uint8_t)(value >> 24);
    }
}

/* Geometry validation is shared by the Lean wrapper and the standalone probe. */
static inline unsigned row_shape(uint64_t modulus, size_t dense_bytes, size_t column_bytes,
                          size_t coefficient_bytes, size_t start, size_t count,
                          uint64_t factor) {
    if (modulus < 2 || modulus >= UINT64_C(2147483648) ||
        factor >= modulus || count > 4096) return 0;
    unsigned width = modulus <= 256 ? 1 : modulus <= 65536 ? 2 : 4;
    size_t rows = column_bytes / 4;
    /* rows*width cannot overflow: width<=4 and rows=floor(column_bytes/4). */
    if (column_bytes % 4 || coefficient_bytes != rows * width ||
        dense_bytes % width || start > rows || count > rows - start) return 0;
    return width;
}

/* Buffers have the validated geometry and out does not alias either input.
   A failed residue/index check may leave partial internal work in out; callers
   discard it and never return a partial buffer as a successful result. */
static inline int update_bytes(uint64_t modulus, unsigned width, uint8_t *out,
                        size_t dense_bytes, const uint8_t *cols, const uint8_t *coeffs,
                        size_t start, size_t count, uint64_t factor) {
    size_t dense_elements = dense_bytes / width;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
    uint64_t reciprocal;
    if (width < 4) {
        /* factor*b < 2^32, so a 32-bit Barrett reciprocal is sufficient. */
        reciprocal = UINT64_C(4294967296) / modulus;
    } else {
        reciprocal = UINT64_MAX / modulus;
        if (UINT64_MAX % modulus == modulus - 1) ++reciprocal;
    }
#endif
    for (size_t k = 0; k < count; ++k) {
        size_t i = start + k;
        uint64_t column = read_le(cols + 4 * i, 4);
        if (column >= dense_elements) return 0;
        size_t offset = (size_t)column * width;
        uint64_t b = read_le(coeffs + i * width, width);
        uint64_t a = read_le(out + offset, width);
        if (a >= modulus || b >= modulus) return 0;
        uint64_t product = factor * b;
#if defined(__SIZEOF_INT128__) && !defined(HEX_GROEBNER_NO_UINT128)
        uint64_t quotient = width < 4 ? (product * reciprocal) >> 32 :
            (uint64_t)(((__uint128_t)product * reciprocal) >> 64);
        product -= quotient * modulus;
        if (product >= modulus) product -= modulus;
#else
        product %= modulus;
#endif
        /* a and product are canonical and below 2^31. Unsigned subtraction
           wraps precisely when a < product; only that case has its top bit
           set. Adding p under this mask gives the canonical difference. */
        uint64_t difference = a - product;
        difference += modulus & (UINT64_C(0) - (difference >> 63));
        write_le(out + offset, width, difference);
    }
    return 1;
}

/* Monomial preparation uses one reusable, owned buffer. The trailing metadata
   is degree:u64, support-mask:u64, FNV-hash:u64, maximum-coordinate:u32. */
static inline int monomial_shape(unsigned operation, unsigned width, uint64_t arity,
        uint64_t count, uint64_t left, uint64_t right, size_t source_bytes,
        size_t workspace_bytes) {
    if (operation > 2 || (width != 1 && width != 2 && width != 4) ||
        arity == 0 || arity > 4096 || left >= count || right >= count) return 0;
    if (count > SIZE_MAX / arity / width) return 0;
    return source_bytes == (size_t)count * (size_t)arity * width &&
        workspace_bytes == (size_t)arity * 4 + 28;
}

static inline int prepare_monomial(unsigned operation, unsigned width, uint64_t arity,
        uint64_t count, uint64_t left, uint64_t right, const uint8_t *source,
        size_t source_bytes, uint8_t *workspace, size_t workspace_bytes) {
    if (!monomial_shape(operation, width, arity, count, left, right,
                        source_bytes, workspace_bytes)) return 0;
    uint64_t degree = 0, mask = 0, hash = UINT64_C(14695981039346656037), largest = 0;
    for (size_t i = 0; i < (size_t)arity; ++i) {
        uint64_t x = read_le(source + ((size_t)left * (size_t)arity + i) * width, width);
        uint64_t y = read_le(source + ((size_t)right * (size_t)arity + i) * width, width);
        if ((operation == 1 && x + y > UINT32_MAX) || (operation == 2 && y > x)) return 0;
        uint64_t z = operation == 0 ? (x > y ? x : y) : operation == 1 ? x + y : x - y;
        write_le(workspace + 4 * i, 4, z);
        degree += z;
        if (z) mask |= UINT64_C(1) << (i % 64);
        hash = (hash ^ z) * UINT64_C(1099511628211);
        if (z > largest) largest = z;
    }
    size_t offset = (size_t)arity * 4;
    write_le(workspace + offset, 4, degree);
    write_le(workspace + offset + 4, 4, degree >> 32);
    write_le(workspace + offset + 8, 4, mask);
    write_le(workspace + offset + 12, 4, mask >> 32);
    write_le(workspace + offset + 16, 4, hash);
    write_le(workspace + offset + 20, 4, hash >> 32);
    write_le(workspace + offset + 24, 4, largest);
    return 1;
}

static inline int equal_monomial(unsigned width, uint64_t arity, uint64_t id,
        const uint8_t *source, size_t source_bytes, const uint8_t *candidate,
        size_t candidate_bytes) {
    if ((width != 1 && width != 2 && width != 4) || arity == 0 || arity > 4096) return 0;
    size_t stride = (size_t)arity * width;
    if (source_bytes % stride || id >= source_bytes / stride ||
        candidate_bytes != (size_t)arity * 4 + 28) return 0;
    for (size_t i = 0; i < (size_t)arity; ++i)
        if (read_le(source + (size_t)id * stride + i * width, width) !=
            read_le(candidate + i * 4, 4)) return 0;
    return 1;
}


/* Exact bounded comparison. Subtraction-based checks avoid start+count wrap. */
static inline int equal_bytes(const uint8_t *left,size_t left_size,const uint8_t *right,
        size_t right_size,size_t start,size_t count) {
    if(count>4096 || start>left_size || start>right_size ||
       count>left_size-start || count>right_size-start) return 0;
    if(!count || left==right) return 1;
    return memcmp(left+start,right+start,count)==0;
}

/* Exact cached-product validation against the current arena, independent of
   hash values and insertion history. All inputs are borrowed and may alias. */
static inline int equal_products(unsigned width,uint64_t arity,uint64_t count,
        uint64_t multiplier,uint64_t start,uint64_t terms,const uint8_t *arena,
        size_t arena_bytes,const uint8_t *base,size_t base_bytes,
        const uint8_t *result,size_t result_bytes) {
    if((width!=1 && width!=2 && width!=4) || !arity || arity>4096 ||
       terms>4096/arity || multiplier>=count || base_bytes%4 ||
       result_bytes!=base_bytes || start>base_bytes/4 || terms>base_bytes/4-start)
        return 0;
    size_t stride=(size_t)arity*width;
    if(count>SIZE_MAX/stride || arena_bytes!=(size_t)count*stride) return 0;
    for(size_t i=(size_t)start;i<(size_t)(start+terms);++i) {
        uint64_t a=read_le(base+4*i,4),b=read_le(result+4*i,4);
        if(a>=count || b>=count) return 0;
        for(size_t j=0;j<(size_t)arity;++j) {
            uint64_t x=read_le(arena+(size_t)a*stride+j*width,width);
            uint64_t y=read_le(arena+(size_t)multiplier*stride+j*width,width);
            uint64_t z=read_le(arena+(size_t)b*stride+j*width,width);
            if(x+y!=z) return 0;
        }
    }
    return 1;
}

/* Read-only comparisons share the packed representation and a bounded call.
   Result 3 declines unsupported geometry without touching any source byte. */
static inline uint8_t compare_monomials(unsigned op,unsigned w,uint64_t n,uint64_t left,uint64_t right,
        const uint8_t *arena,size_t bytes) {
    if(op>2 || (w!=1 && w!=2 && w!=4) || n>4096 ||
       left>UINT32_MAX || right>UINT32_MAX) return 3;
    if(!n) return 1;
    /* At most 2^32 rows of at most 16384 bytes: this product fits u64
       even on a 32-bit host. Only accessed complete row spans are required. */
    uint64_t row_bytes=n*w,stop=((left>right?left:right)+1)*row_bytes;
    if(stop>bytes) return 3;
    const uint8_t *a=arena+left*row_bytes,*b=arena+right*row_bytes;
    if(op==0 && w==1) {int c=memcmp(a,b,n);return c<0?0:c>0?2:1;}
    for(size_t k=0;k<n;++k) {
        size_t i=op==1?n-1-k:k;
        uint64_t x=read_le(a+i*w,w),y=read_le(b+i*w,w);
        if(op==2) {if(x>y) return 0;}
        else if(x!=y) return op==1?(y<x?0:2):(x<y?0:2);
    }
    return 1;
}

#ifndef HEX_GROEBNER_NO_LEAN
static inline lean_object *some_buffer(lean_object *data) {
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, data);
    return result;
}


LEAN_EXPORT uint8_t lean_hex_groebner_equal_products(uint8_t width,
        uint64_t arity,uint64_t count,uint64_t multiplier,uint64_t start,uint64_t terms,
        b_lean_obj_arg arena,b_lean_obj_arg base,b_lean_obj_arg result) {
    return (uint8_t)equal_products(width,arity,count,multiplier,start,terms,
        lean_sarray_cptr(arena),lean_sarray_size(arena),
        lean_sarray_cptr(base),lean_sarray_size(base),
        lean_sarray_cptr(result),lean_sarray_size(result));
}

LEAN_EXPORT uint8_t lean_hex_groebner_equal_bytes(b_lean_obj_arg left,
        b_lean_obj_arg right,b_lean_obj_arg start_arg,b_lean_obj_arg count_arg) {
    if(!lean_is_scalar(count_arg)) return 0;
    size_t count=lean_unbox(count_arg);
    if(count>4096) return 0;
    size_t left_size=lean_sarray_size(left),right_size=lean_sarray_size(right),start;
    if(lean_is_scalar(start_arg)) start=lean_unbox(start_arg);
    else {
        lean_object *limit=lean_usize_to_nat(left_size<right_size?left_size:right_size);
        int valid=lean_nat_dec_le(start_arg,limit);lean_dec(limit);
        if(!valid) return 0;
        start=lean_usize_of_nat(start_arg);
    }
    return (uint8_t)equal_bytes(lean_sarray_cptr(left),left_size,
        lean_sarray_cptr(right),right_size,start,count);
}

LEAN_EXPORT lean_obj_res lean_hex_groebner_subtract_row(
        uint64_t modulus, lean_obj_arg dense,
        b_lean_obj_arg columns, b_lean_obj_arg coefficients,
        b_lean_obj_arg start_arg, b_lean_obj_arg count_arg, uint64_t factor) {
    /* Admissible starts are <=floor(SIZE_MAX/4), hence scalar Nats on both
       word sizes. Non-scalar counts exceed the 4096-entry call bound. */
    if (!lean_is_scalar(start_arg) || !lean_is_scalar(count_arg)) {
        lean_dec(dense);
        return lean_box(0);
    }
    size_t start = lean_unbox(start_arg);
    size_t count = lean_unbox(count_arg);
    size_t dense_bytes = lean_sarray_size(dense);
    unsigned width = row_shape(modulus, dense_bytes, lean_sarray_size(columns),
                               lean_sarray_size(coefficients), start, count, factor);
    if (!width) {
        lean_dec(dense);
        return lean_box(0);
    }
    if (count == 0) return some_buffer(dense);
    /* Retain a borrowed alias before requesting unique storage. That keeps
       original row reads stable even for an exclusively owned aliased input. */
    lean_object *alias = NULL;
    if (dense == columns || dense == coefficients) {
        alias = dense;
        lean_inc(alias);
    }
    dense = lean_sarray_ensure_exclusive(dense);
    int ok = update_bytes(modulus, width, lean_sarray_cptr(dense), dense_bytes,
                           lean_sarray_cptr(columns), lean_sarray_cptr(coefficients),
                           start, count, factor);
    if (alias) lean_dec(alias);
    if (!ok) {
        lean_dec(dense);
        return lean_box(0);
    }
    return some_buffer(dense);
}

LEAN_EXPORT lean_obj_res lean_hex_groebner_prepare_monomial(
        uint8_t operation, uint8_t width, uint64_t arity, uint64_t count,
        uint64_t left, uint64_t right, b_lean_obj_arg source, lean_obj_arg workspace) {
    size_t source_bytes = lean_sarray_size(source), workspace_bytes = lean_sarray_size(workspace);
    if (!monomial_shape(operation, width, arity, count, left, right, source_bytes, workspace_bytes)) {
        lean_dec(workspace);
        return lean_box(0);
    }
    lean_object *alias = NULL;
    if (source == workspace) {
        alias = workspace;
        lean_inc(alias);
    }
    workspace = lean_sarray_ensure_exclusive(workspace);
    int ok = prepare_monomial(operation, width, arity, count, left, right,
        lean_sarray_cptr(source), source_bytes, lean_sarray_cptr(workspace), workspace_bytes);
    if (alias) lean_dec(alias);
    if (!ok) {
        lean_dec(workspace);
        return lean_box(0);
    }
    return some_buffer(workspace);
}

LEAN_EXPORT uint8_t lean_hex_groebner_equal_monomial(
        uint8_t width, uint64_t arity, uint64_t id,
        b_lean_obj_arg source, b_lean_obj_arg candidate) {
    return (uint8_t)equal_monomial(width, arity, id,
        lean_sarray_cptr(source), lean_sarray_size(source),
        lean_sarray_cptr(candidate), lean_sarray_size(candidate));
}

LEAN_EXPORT uint8_t lean_hex_groebner_compare_monomials(uint8_t operation,uint8_t width,
        uint64_t arity,uint64_t left,uint64_t right,b_lean_obj_arg arena) {
    return compare_monomials(operation,width,arity,left,right,
        lean_sarray_cptr(arena),lean_sarray_size(arena));
}

static lean_obj_res monomial_search_result(uint64_t id,uint64_t link,uint64_t work,uint8_t status) {
    lean_object *r=lean_alloc_ctor(0,3,1);
    lean_ctor_set(r,0,lean_uint64_to_nat(id));lean_ctor_set(r,1,lean_uint64_to_nat(link));
    lean_ctor_set(r,2,lean_uint64_to_nat(work));lean_ctor_set_uint8(r,3*sizeof(void*),status);
    return r;
}
LEAN_EXPORT lean_obj_res lean_hex_groebner_search_monomial(uint8_t width,
        uint64_t arity,uint64_t count,uint64_t hash,uint64_t link,uint64_t quantum,
        b_lean_obj_arg exponents,b_lean_obj_arg metadata,b_lean_obj_arg links,
        b_lean_obj_arg candidate,b_lean_obj_arg allowance) {
    if((width!=1 && width!=2 && width!=4) || !arity || arity>4096 || count>UINT32_MAX ||
       link>UINT32_MAX || quantum>4096 || quantum*arity>4096 ||
       lean_sarray_size(exponents)!=count*arity*width || lean_sarray_size(metadata)!=count*24 ||
       lean_sarray_size(links)!=count*4 || lean_sarray_size(candidate)!=arity*4+28)
        return monomial_search_result(0,link,0,4);
    uint64_t allowed=8193;
    if(lean_is_scalar(allowance)) {uint64_t n=lean_unbox(allowance);if(n<allowed) allowed=n;}
    uint64_t work=0;
    const uint8_t *es=lean_sarray_cptr(exponents),*ms=lean_sarray_cptr(metadata);
    const uint8_t *ls=lean_sarray_cptr(links),*cs=lean_sarray_cptr(candidate);
    for(uint64_t i=0;i<quantum;++i) {
        if(!link) return monomial_search_result(0,0,work,2);
        if(work+1>allowed) return monomial_search_result(0,link,work,3);
        ++work;
        uint64_t id=link-1;
        if(id>=count) return monomial_search_result(0,link,work,4);
        link=read_le(ls+(size_t)id*4,4);
        const uint8_t *m=ms+(size_t)id*24+16;
        uint64_t actual=read_le(m,4) | (read_le(m+4,4)<<32);
        if(actual!=hash) continue;
        if(work+arity>allowed) return monomial_search_result(0,link,work,3);
        work+=arity;
        if(equal_monomial(width,arity,id,es,lean_sarray_size(exponents),cs,lean_sarray_size(candidate)))
            return monomial_search_result(id,link,work,1);
    }
    return monomial_search_result(0,link,work,0);
}

#endif

#include "trie_lookup.h"

#ifndef HEX_GROEBNER_NO_LEAN
/* Reserve once, preserving marked-linear ownership on exclusive growth or an
   explicitly supported borrowed/output alias. Other sharing uses ordinary COW. */
static lean_object *remap_reserve(lean_obj_arg bytes,size_t size,int alias) {
    size_t old=lean_sarray_size(bytes);
    if(!alias && lean_is_exclusive(bytes) && lean_sarray_capacity(bytes)>=size) return bytes;
    size_t capacity=old<=SIZE_MAX/2?old*2:size;
    if(capacity<size) capacity=size;
    if(alias || lean_is_exclusive(bytes)) {
        int linear=lean_sarray_is_marked_linear(bytes);
        bytes=lean_copy_sarray(bytes,capacity);
        if(linear) lean_sarray_mark_linear_core(bytes);
    } else bytes=lean_copy_sarray_nonlinear(bytes,capacity);
    return bytes;
}

/* Native.Columns.remapPortable: borrowed little-endian u32 buffers and an
   owned output prefix. Validate and write <=4096 entries past the logical end;
   commit the new size only on success. Invalid input never changes a borrowed
   buffer or the observable prefix. Borrowed/output aliases retain their owner. */
LEAN_EXPORT lean_obj_res lean_hex_groebner_remap_columns(
        b_lean_obj_arg positions,b_lean_obj_arg support,
        b_lean_obj_arg start_arg,b_lean_obj_arg count_arg,lean_obj_arg output) {
    size_t pb=lean_sarray_size(positions),sb=lean_sarray_size(support);
    size_t start=0,count=0,old=lean_sarray_size(output);
    const uint8_t *ps=lean_sarray_cptr(positions),*ss=lean_sarray_cptr(support);
    lean_object *alias=NULL,*result;
    uint8_t *target;
    if(pb%4 || !lean_is_scalar(start_arg) || !lean_is_scalar(count_arg)) goto invalid;
    start=lean_unbox(start_arg);count=lean_unbox(count_arg);
    if(count>4096 || start>sb/4 || count>sb/4-start || count*4>SIZE_MAX-old) goto invalid;
    if(count) {
        if(output==positions || output==support) {alias=output;lean_inc(alias);}
        output=remap_reserve(output,old+count*4,alias!=NULL);
        target=lean_sarray_cptr(output)+old;
        for(size_t i=0;i<count;++i) {
            uint64_t id=read_le(ss+(start+i)*4,4),value;
            if(id>=pb/4) goto invalid;
            value=read_le(ps+(size_t)id*4,4);
            if(!value) goto invalid;
            write_le(target+i*4,4,value-1);
        }
        lean_sarray_set_size(output,old+count*4);
    }
    if(alias) lean_dec(alias);
    result=lean_alloc_ctor(1,1,0);lean_ctor_set(result,0,output);return result;
invalid:
    if(alias) lean_dec(alias);
    lean_dec(output);return lean_box(0);
}
static uint64_t column_hash(uint64_t h) {
    h=(h^(h>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    h=(h^(h>>27))*UINT64_C(0x94d049bb133111eb);
    return h^(h>>31);
}

/* Exact bounded probing. Empty value zero is distinct from key ID zero.
   Only a successful lookup commits appended bytes; borrowed aliases survive. */
LEAN_EXPORT lean_obj_res lean_hex_groebner_remap_index(
        b_lean_obj_arg slots,b_lean_obj_arg support,b_lean_obj_arg start_arg,
        b_lean_obj_arg count_arg,b_lean_obj_arg probes_arg,lean_obj_arg output) {
    size_t pb=lean_sarray_size(slots),sb=lean_sarray_size(support),capacity=pb/8;
    size_t start=0,count=0,probes=0,old=lean_sarray_size(output);
    const uint8_t *ps=lean_sarray_cptr(slots),*ss=lean_sarray_cptr(support);
    uint8_t *target;
    lean_object *alias=NULL,*result;
    if(pb%8 || !capacity || (capacity&(capacity-1)) || !lean_is_scalar(start_arg) ||
       !lean_is_scalar(count_arg) || !lean_is_scalar(probes_arg)) goto invalid_index;
    start=lean_unbox(start_arg);count=lean_unbox(count_arg);probes=lean_unbox(probes_arg);
    if(probes>64 || count>4096 || start>sb/4 || count>sb/4-start || count*4>SIZE_MAX-old)
        goto invalid_index;
    if(count) {
        if(output==slots || output==support) {alias=output;lean_inc(alias);}
        output=remap_reserve(output,old+count*4,alias!=NULL);
        target=lean_sarray_cptr(output)+old;
        for(size_t i=0;i<count;++i) {
            uint64_t id=read_le(ss+(start+i)*4,4),value=0;
            size_t bucket=(size_t)(column_hash(id)&(capacity-1));
            for(size_t j=0;j<probes;++j) {
                uint64_t v=read_le(ps+bucket*8+4,4);
                if(!v) goto invalid_index;
                if(read_le(ps+bucket*8,4)==id) {value=v;break;}
                bucket=(bucket+1)&(capacity-1);
            }
            if(!value) goto invalid_index;
            write_le(target+i*4,4,value-1);
        }
        lean_sarray_set_size(output,old+count*4);
    }
    if(alias) lean_dec(alias);
    result=lean_alloc_ctor(1,1,0);lean_ctor_set(result,0,output);return result;
invalid_index:
    if(alias) lean_dec(alias);
    lean_dec(output);return lean_box(0);
}

LEAN_EXPORT lean_obj_res lean_hex_groebner_append_zeros(lean_obj_arg output,b_lean_obj_arg count_arg) {
    size_t old=lean_sarray_size(output),count;
    lean_object *result;
    if(!lean_is_scalar(count_arg)) {lean_dec(output);return lean_box(0);}
    count=lean_unbox(count_arg);
    if(count>4096 || count>SIZE_MAX-old) {lean_dec(output);return lean_box(0);}
    if(count) {
        output=remap_reserve(output,old+count,0);
        memset(lean_sarray_cptr(output)+old,0,count);
        lean_sarray_set_size(output,old+count);
    }
    result=lean_alloc_ctor(1,1,0);lean_ctor_set(result,0,output);return result;
}
#endif
