#!/usr/bin/env python3
"""Run compiled matrix conformance against four native implementations.

Use HEX_GROEBNER_SANITIZE=1 for ASan/UBSan, and optionally retain the generated
project with HEX_GROEBNER_NATIVE_LOG_DIR. HEX_GROEBNER_TEST_LOADER and
HEX_GROEBNER_TEST_LIBRARY_PATH select a matching libc loader on Nix hosts.
The ELF --wrap bindings include call counters so an unused instrumented object
cannot produce a false passing sanitizer check.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
VARIANTS = {"Native": [], "Scalar": ["-DHEX_GROEBNER_NO_AVX2"],
            "Remainder": ["-DHEX_GROEBNER_NO_UINT128"],
            "ScalarRemainder": ["-DHEX_GROEBNER_NO_AVX2", "-DHEX_GROEBNER_NO_UINT128"]}


def sanitizer_libraries(cc: str) -> list[str]:
    override = os.environ.get("HEX_GROEBNER_SANITIZER_LIBRARIES")
    if override:
        return override.split(os.pathsep)
    arch = platform.machine()
    for name in (f"libclang_rt.asan-{arch}.so", "libclang_rt.asan.so"):
        clang = subprocess.check_output([cc, f"-print-file-name={name}"], text=True).strip()
        if Path(clang).is_file():
            return [clang]
    libraries = [subprocess.check_output([cc, f"-print-file-name={name}"], text=True).strip()
                 for name in ("libasan.so", "libubsan.so")]
    if not all(Path(name).is_file() for name in libraries):
        raise RuntimeError("set HEX_GROEBNER_SANITIZER_LIBRARIES to the compiler's ASan/UBSan libraries")
    return libraries


def run() -> None:
    if platform.system() != "Linux":
        print("compiled matrix variants require ELF --wrap; ordinary Lean and standalone C checks still apply")
        return
    started = time.monotonic()
    retained = os.environ.get("HEX_GROEBNER_NATIVE_LOG_DIR")
    directory = Path(retained).resolve() if retained else Path(tempfile.mkdtemp(prefix="hexgroebner-matrix-"))
    directory.mkdir(parents=True, exist_ok=True)
    cc = os.environ.get("CC", "cc")
    sanitize = os.environ.get("HEX_GROEBNER_SANITIZE", "0") == "1"
    libraries = sanitizer_libraries(cc) if sanitize else []
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        manifest["name"] = "GroebnerMatrixChecks"
        manifest["packagesDir"] = str(ROOT / ".lake/packages")
        for package in manifest["packages"]:
            package["inherited"] = True
        manifest["packages"].append(dict(type="path", name="Hex", dir=str(ROOT),
                                         inherited=False, configFile="lakefile.lean",
                                         manifestFile="lake-manifest.json", scope=""))
        (directory / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        (directory / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
        # The included source gets private names; only our counted wrappers use --wrap.
        source = ROOT / "HexGroebner/ffi/matrix_scan.c"
        (directory / "probe.c").write_text('''#define lean_hex_groebner_subtract_row hex_test_unused_subtract
#define lean_hex_groebner_remap_columns hex_test_remap
#define lean_hex_groebner_remap_index hex_test_remap_index
#define lean_hex_groebner_append_zeros hex_test_append_zeros
#define lean_hex_groebner_prepare_monomial hex_test_unused_prepare
#define lean_hex_groebner_equal_monomial hex_test_unused_monomial_equal
#define lean_hex_groebner_search_monomial hex_test_search_monomial
#define lean_hex_groebner_equal_bytes hex_test_equal_bytes
#define lean_hex_groebner_equal_products hex_test_equal_products
#define lean_hex_groebner_compare_monomials hex_test_compare
#define lean_hex_groebner_validate_trie hex_test_validate
#define lean_hex_groebner_lookup_trie hex_test_trie
#include ROW_SOURCE
#undef lean_hex_groebner_compare_monomials
#undef lean_hex_groebner_validate_trie
#undef lean_hex_groebner_lookup_trie
#undef lean_hex_groebner_subtract_row
#undef lean_hex_groebner_remap_columns
#undef lean_hex_groebner_remap_index
#undef lean_hex_groebner_append_zeros
#undef lean_hex_groebner_prepare_monomial
#undef lean_hex_groebner_equal_monomial
#undef lean_hex_groebner_search_monomial
#undef lean_hex_groebner_equal_bytes
#undef lean_hex_groebner_equal_products
static uint64_t remap_calls=0;
__typeof__(hex_test_remap) __wrap_lean_hex_groebner_remap_columns;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_remap_columns(
 b_lean_obj_arg positions,b_lean_obj_arg support,b_lean_obj_arg start,
 b_lean_obj_arg count,lean_obj_arg output) {
 ++remap_calls;return hex_test_remap(positions,support,start,count,output);
}
static uint64_t index_calls=0,zero_calls=0;
__typeof__(hex_test_remap_index) __wrap_lean_hex_groebner_remap_index;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_remap_index(
 b_lean_obj_arg slots,b_lean_obj_arg support,b_lean_obj_arg start,
 b_lean_obj_arg count,b_lean_obj_arg probes,lean_obj_arg output) {
 ++index_calls;return hex_test_remap_index(slots,support,start,count,probes,output);
}
__typeof__(hex_test_append_zeros) __wrap_lean_hex_groebner_append_zeros;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_append_zeros(lean_obj_arg output,b_lean_obj_arg count) {
 ++zero_calls;return hex_test_append_zeros(output,count);
}
LEAN_EXPORT lean_obj_res hex_test_index_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(index_calls));
}
LEAN_EXPORT lean_obj_res hex_test_zero_append_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(zero_calls));
}
LEAN_EXPORT lean_obj_res hex_test_remap_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(remap_calls));
}
LEAN_EXPORT lean_obj_res hex_test_remap_aliases(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned linear=0;linear<2;++linear) for(unsigned mode=0;mode<4;++mode) {
  lean_object *positions=lean_alloc_sarray(1,12,12),*support=lean_alloc_sarray(1,12,12);
  for(unsigned i=0;i<3;++i) {
   write_le(lean_sarray_cptr(positions)+4*i,4,i+1);
   write_le(lean_sarray_cptr(support)+4*i,4,i);
  }
  lean_object *out=mode==0?support:positions;
  size_t prefix=12;
  if(mode>=2) {out=lean_alloc_sarray(1,4,mode==2?4:32);write_le(lean_sarray_cptr(out),4,37);prefix=4;}
  if(linear) lean_sarray_mark_linear_core(out);
  /* Alias cases have one output owner also used as a borrowed argument.
     Other cases exercise exclusive growth and exclusive reserved capacity. */
  lean_object *result=hex_test_remap(positions,support,lean_box(0),lean_box(3),out);
  ok=ok && lean_obj_tag(result)==1;
  if(lean_obj_tag(result)==1) {
   lean_object *bytes=lean_ctor_get(result,0);ok=ok && lean_sarray_size(bytes)==prefix+12;
   if(linear) ok=ok && lean_sarray_is_marked_linear(bytes);
   if(lean_sarray_size(bytes)==prefix+12) {
    if(mode<2) for(unsigned i=0;i<3;++i) ok=ok && read_le(lean_sarray_cptr(bytes)+4*i,4)==i+mode;
    else ok=ok && read_le(lean_sarray_cptr(bytes),4)==37;
    for(unsigned i=0;i<3;++i) ok=ok && read_le(lean_sarray_cptr(bytes)+prefix+4*i,4)==i;
   }
  }
  lean_dec(result);
  if(mode!=1) lean_dec(positions);
  if(mode!=0) lean_dec(support);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
LEAN_EXPORT lean_obj_res hex_test_index_aliases(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned linear=0;linear<2;++linear) for(unsigned mode=0;mode<4;++mode)
 for(unsigned test=0;test<4;++test) {
  int fail=test==1 || test==2,observe=test>=2;
  /* Marked sharing outside an explicitly supported borrowed alias violates
     the runtime linearity contract; test ordinary COW there instead. */
  if(linear && observe && mode>=2) continue;
  lean_object *slots=lean_alloc_sarray(1,128,128),*support=lean_alloc_sarray(1,12,12);
  memset(lean_sarray_cptr(slots),0,128);
  for(unsigned i=0;i<3;++i) {
   size_t bucket=(size_t)(column_hash(i)&15);
   while(read_le(lean_sarray_cptr(slots)+bucket*8+4,4)) bucket=(bucket+1)&15;
   write_le(lean_sarray_cptr(slots)+bucket*8,4,i);
   write_le(lean_sarray_cptr(slots)+bucket*8+4,4,i+1);
   write_le(lean_sarray_cptr(support)+4*i,4,fail && i==2?777:i);
  }
  uint8_t slot_snapshot[128],support_snapshot[12],output_snapshot[128];
  memcpy(slot_snapshot,lean_sarray_cptr(slots),128);memcpy(support_snapshot,lean_sarray_cptr(support),12);
  lean_object *out=mode==0?support:slots;size_t old=lean_sarray_size(out);
  if(mode>=2) {out=lean_alloc_sarray(1,4,mode==2?4:32);write_le(lean_sarray_cptr(out),4,37);old=4;}
  memcpy(output_snapshot,lean_sarray_cptr(out),old);lean_object *keeper=out;
  if(linear) lean_sarray_mark_linear_core(out);
  if(observe) lean_inc(keeper);
  lean_object *result=hex_test_remap_index(slots,support,lean_box(0),lean_box(3),lean_box(64),out);
  ok=ok && (lean_obj_tag(result)==(fail?0:1));
  if(!fail && lean_obj_tag(result)==1) {
   lean_object *bytes=lean_ctor_get(result,0);
   ok=ok && lean_is_exclusive(bytes) && lean_sarray_size(bytes)==old+12;
   if(linear) ok=ok && lean_sarray_is_marked_linear(bytes);
   if(lean_sarray_size(bytes)==old+12) {
    ok=ok && memcmp(lean_sarray_cptr(bytes),output_snapshot,old)==0;
    for(unsigned i=0;i<3;++i) ok=ok && read_le(lean_sarray_cptr(bytes)+old+4*i,4)==i;
   }
   if(observe) ok=ok && lean_sarray_cptr(bytes)!=lean_sarray_cptr(keeper);
  }
  if(observe) {
   ok=ok && lean_is_exclusive(keeper) && lean_sarray_size(keeper)==old;
   ok=ok && memcmp(lean_sarray_cptr(keeper),output_snapshot,old)==0;lean_dec(keeper);
  }
  if(mode!=1) ok=ok && lean_is_exclusive(slots) && memcmp(lean_sarray_cptr(slots),slot_snapshot,128)==0;
  if(mode!=0) ok=ok && lean_is_exclusive(support) && memcmp(lean_sarray_cptr(support),support_snapshot,12)==0;
  lean_dec(result);if(mode!=1) lean_dec(slots);if(mode!=0) lean_dec(support);
 }
 for(unsigned capacity=4;capacity<=32;capacity*=8) for(unsigned shared=0;shared<2;++shared) {
  lean_object *bytes=lean_alloc_sarray(1,4,capacity);memset(lean_sarray_cptr(bytes),37,4);
  lean_object *keeper=bytes;
  if(shared) lean_inc(keeper);else lean_sarray_mark_linear_core(bytes);
  lean_object *result=hex_test_append_zeros(bytes,lean_box(12));ok=ok && lean_obj_tag(result)==1;
  if(lean_obj_tag(result)==1) {
   bytes=lean_ctor_get(result,0);ok=ok && lean_is_exclusive(bytes) && lean_sarray_size(bytes)==16;
   if(!shared) ok=ok && lean_sarray_is_marked_linear(bytes);
   if(shared) ok=ok && lean_sarray_cptr(bytes)!=lean_sarray_cptr(keeper);
   for(unsigned i=0;i<16;++i) ok=ok && lean_sarray_cptr(bytes)[i]==(i<4?37:0);
  }
  if(shared) {
   ok=ok && lean_is_exclusive(keeper) && lean_sarray_size(keeper)==4;
   for(unsigned i=0;i<4;++i) ok=ok && lean_sarray_cptr(keeper)[i]==37;lean_dec(keeper);
  }
  lean_dec(result);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
static uint64_t fused_success=0,fused_insert=0,fused_unique=0,fused_deferred=0,unique_alias=0,unique_alias_mask=0;
#define HEX_GROEBNER_DEFERRED() (++fused_deferred)
#define HEX_GROEBNER_UNIQUE_ALIAS(mask) (++unique_alias,unique_alias_mask|=(mask))
#define HEX_GROEBNER_TABLE_UNIQUE() (++fused_unique)
#define HEX_GROEBNER_INSERT_FOUND() (++fused_insert)
#define HEX_GROEBNER_HIT_FOUND() (++fused_success)
#define HEX_GROEBNER_HIT_HELPERS
#define lean_hex_groebner_combine_owned hex_test_combine_owned
#include HITCODE
#undef lean_hex_groebner_combine_owned
LEAN_EXPORT lean_obj_res hex_test_owned_runtime(lean_obj_arg world) {
 (void)world;int ok=1;
 for(size_t capacity=1;capacity<=8;capacity*=8) {
  lean_object *bytes=lean_alloc_sarray(1,1,capacity);lean_sarray_cptr(bytes)[0]=37;
  lean_sarray_mark_linear_core(bytes);bytes=hit_extend(bytes,2);
  ok=ok && lean_sarray_is_marked_linear(bytes) && lean_sarray_size(bytes)==2 &&
      lean_sarray_cptr(bytes)[0]==37;lean_dec(bytes);
 }
 lean_object *fake=lean_alloc_ctor(0,7,0);
 for(unsigned i=0;i<7;++i) lean_ctor_set(fake,i,lean_box(0));
 lean_object *result=hex_test_combine_owned(fake,0,lean_box(0),lean_box(0),
   lean_box(100),lean_box(10000),lean_box(10000),1);
 ok=ok && lean_obj_tag(result)==1 && lean_ctor_get(result,0)==fake;
 lean_dec(result);
 fake=lean_alloc_ctor(0,8,1);
 for(unsigned i=0;i<8;++i) lean_ctor_set(fake,i,lean_box(0));
 lean_object *index=lean_alloc_ctor(0,1,0);lean_ctor_set(index,0,lean_box(0));
 lean_ctor_set(fake,5,index);lean_ctor_set_uint8(fake,8*sizeof(void*),0);
 result=hex_test_combine_owned(fake,0,lean_box(0),lean_box(0),lean_box(100),
   lean_box(10000),lean_box(10000),1);
 ok=ok && lean_obj_tag(result)==1 && lean_ctor_get(result,0)==fake;lean_dec(result);
 return lean_io_result_mk_ok(lean_box(ok));
}
static uint64_t mersenne_vectors=0,zero_scans=0;
#define HEX_GROEBNER_ZERO_SCAN_USED() (++zero_scans)
#define HEX_GROEBNER_MERSENNE_USED() (++mersenne_vectors)
#define hex_scan8 hex_test_scan8_base
#define hex_scan8_m31 hex_test_scan8_m31_base
#include HEADER
#undef hex_scan8
#undef hex_scan8_m31
static uint64_t vector_contiguous=0,vector_gather=0;
static uint32_t vector_widths=0;
#if HEX_GROEBNER_AVX2
static __typeof__(hex_test_scan8_base) hex_test_scan8_counted;
__attribute__((target("avx2"),always_inline))
static inline unsigned hex_test_scan8_counted(uint8_t *dense,const uint8_t *columns,
 const uint8_t *coefficients,size_t entry,uint64_t column_count,uint32_t p,
 uint32_t multiplier,uint32_t reduction,unsigned width) {
 unsigned n=hex_test_scan8_base(dense,columns,coefficients,entry,column_count,p,multiplier,reduction,width);
 if(n) {uint32_t first,last;memcpy(&first,columns+entry*4,4);memcpy(&last,columns+(entry+7)*4,4);
  if(last-first==7) ++vector_contiguous;else ++vector_gather;
  unsigned group=width==1?0:width==2?1:2;
  vector_widths|=1u<<(2*group+(last-first!=7));}
 return n;
}
__attribute__((target("avx2"),always_inline))
static inline unsigned hex_test_scan8_m31_counted(uint8_t *dense,const uint8_t *columns,
 const uint8_t *coefficients,size_t entry,uint64_t column_count,uint32_t p,
 uint32_t multiplier,uint32_t reduction,unsigned width) {
 unsigned n=hex_test_scan8_m31_base(dense,columns,coefficients,entry,column_count,p,multiplier,reduction,width);
 if(n) {uint32_t first,last;memcpy(&first,columns+entry*4,4);memcpy(&last,columns+(entry+7)*4,4);
  if(last-first==7) ++vector_contiguous;else ++vector_gather;
  unsigned group=3;
  vector_widths|=1u<<(2*group+(last-first!=7));}
 return n;
}
#define hex_scan8 hex_test_scan8_counted
#define hex_scan8_m31 hex_test_scan8_m31_counted
#endif
#define lean_hex_scan_transition hex_test_scan
#define lean_hex_gather hex_test_gather
#include SOURCE
#undef lean_hex_scan_transition
#undef lean_hex_gather
static uint64_t whole_accepted=0,whole_deferred=0,whole_joint=0,whole_independent=0;
#define HEX_GROEBNER_MATRIX_ACCEPTED() (++whole_accepted,independent?++whole_independent:++whole_joint)
#define HEX_GROEBNER_MATRIX_DEFERRED() (++whole_deferred)
#define lean_hex_groebner_eliminate_matrix hex_test_whole
#include WHOLECODE
#undef lean_hex_groebner_eliminate_matrix
static uint64_t scan_calls=0,gather_calls=0,byte_calls=0,product_calls=0;
static uint64_t search_calls=0;
__typeof__(hex_test_combine_owned) __wrap_lean_hex_groebner_combine_owned;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_combine_owned(lean_obj_arg table,uint8_t operation,
 lean_obj_arg a,lean_obj_arg b,lean_obj_arg max_count,lean_obj_arg max_bytes,
 lean_obj_arg max_work,uint8_t native) {
 return hex_test_combine_owned(table,operation,a,b,max_count,max_bytes,max_work,native);
}
LEAN_EXPORT lean_obj_res hex_test_deferred_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(fused_deferred));
}
LEAN_EXPORT lean_obj_res hex_test_alias_mask(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(unique_alias_mask));
}
LEAN_EXPORT lean_obj_res hex_test_alias_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(unique_alias));
}
LEAN_EXPORT lean_obj_res hex_test_unique_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(fused_unique));
}
LEAN_EXPORT lean_obj_res hex_test_insert_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(fused_insert));
}
LEAN_EXPORT lean_obj_res hex_test_accept_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(fused_success));
}
__typeof__(hex_test_search_monomial) __wrap_lean_hex_groebner_search_monomial;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_search_monomial(uint8_t width,
 uint64_t arity,uint64_t count,uint64_t hash,uint64_t link,uint64_t quantum,
 b_lean_obj_arg exponents,b_lean_obj_arg metadata,b_lean_obj_arg links,
 b_lean_obj_arg candidate,b_lean_obj_arg allowance) {
 ++search_calls;
 return hex_test_search_monomial(width,arity,count,hash,link,quantum,exponents,metadata,links,candidate,allowance);
}
LEAN_EXPORT lean_obj_res hex_test_search_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(search_calls));
}
__typeof__(hex_test_whole) __wrap_lean_hex_groebner_eliminate_matrix;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_eliminate_matrix(uint64_t p,
 b_lean_obj_arg limits,b_lean_obj_arg columns,b_lean_obj_arg reducers,
 b_lean_obj_arg targets,b_lean_obj_arg sugars,uint8_t independent) {
 return hex_test_whole(p,limits,columns,reducers,targets,sugars,independent);
}
LEAN_EXPORT lean_obj_res hex_test_whole_modes(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(whole_joint));
 lean_ctor_set(out,1,lean_box_uint64(whole_independent));return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res hex_test_whole_counts(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(whole_accepted));
 lean_ctor_set(out,1,lean_box_uint64(whole_deferred));return lean_io_result_mk_ok(out);
}
static uint64_t comparison_calls=0,comparison_declines=0;
__typeof__(hex_test_compare) __wrap_lean_hex_groebner_compare_monomials;
LEAN_EXPORT uint8_t __wrap_lean_hex_groebner_compare_monomials(uint8_t operation,uint8_t width,
 uint64_t arity,uint64_t left,uint64_t right,b_lean_obj_arg arena) {
 ++comparison_calls;
 uint8_t result=hex_test_compare(operation,width,arity,left,right,arena);
 if(result==3) ++comparison_declines;
 return result;
}
LEAN_EXPORT lean_obj_res hex_test_comparison_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(comparison_calls));
}
LEAN_EXPORT lean_obj_res hex_test_comparison_declines(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(comparison_declines));
}
static uint64_t trie_calls=0,trie_declines=0;
__typeof__(hex_test_validate) __wrap_lean_hex_groebner_validate_trie;
LEAN_EXPORT uint8_t __wrap_lean_hex_groebner_validate_trie(b_lean_obj_arg arity,
 b_lean_obj_arg nodes,b_lean_obj_arg edges,uint64_t max_leading) {
 return hex_test_validate(arity,nodes,edges,max_leading);
}

__typeof__(hex_test_trie) __wrap_lean_hex_groebner_lookup_trie;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_lookup_trie(b_lean_obj_arg view,uint8_t width,
 uint64_t count,uint64_t query,b_lean_obj_arg arena,b_lean_obj_arg metadata,uint64_t remaining) {
 ++trie_calls;
 lean_object *result=hex_test_trie(view,width,count,query,arena,metadata,remaining);
 if(lean_ctor_get_uint8(result,2*sizeof(void*))==3) ++trie_declines;
 return result;
}
LEAN_EXPORT lean_obj_res hex_test_trie_counts(lean_obj_arg world) {
 (void)world;lean_object *pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(pair,0,lean_box_uint64(trie_calls));
 lean_ctor_set(pair,1,lean_box_uint64(trie_declines));
 return lean_io_result_mk_ok(pair);
}

__typeof__(hex_test_equal_products) __wrap_lean_hex_groebner_equal_products;
LEAN_EXPORT uint8_t __wrap_lean_hex_groebner_equal_products(uint8_t width,
 uint64_t arity,uint64_t count,uint64_t multiplier,uint64_t start,uint64_t terms,
 b_lean_obj_arg arena,b_lean_obj_arg base,b_lean_obj_arg result) {
 ++product_calls;return hex_test_equal_products(width,arity,count,multiplier,start,terms,arena,base,result);
}
LEAN_EXPORT lean_obj_res hex_test_product_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(product_calls));
}
__typeof__(hex_test_equal_bytes) __wrap_lean_hex_groebner_equal_bytes;
LEAN_EXPORT uint8_t __wrap_lean_hex_groebner_equal_bytes(b_lean_obj_arg left,
 b_lean_obj_arg right,b_lean_obj_arg start,b_lean_obj_arg count) {
 ++byte_calls;return hex_test_equal_bytes(left,right,start,count);
}
__typeof__(hex_test_scan) __wrap_lean_hex_scan_transition;
__typeof__(hex_test_gather) __wrap_lean_hex_gather;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_scan_transition(uint64_t p,
 b_lean_obj_arg slots,b_lean_obj_arg pivots,lean_obj_arg initial,
 b_lean_obj_arg quantum,b_lean_obj_arg work,b_lean_obj_arg trace,uint8_t provenance) {
 ++scan_calls;return hex_test_scan(p,slots,pivots,initial,quantum,work,trace,provenance);
}
LEAN_EXPORT lean_obj_res __wrap_lean_hex_gather(uint64_t p,lean_obj_arg initial,
 b_lean_obj_arg stop,b_lean_obj_arg quantum,b_lean_obj_arg entries,
 b_lean_obj_arg bytes,b_lean_obj_arg work,uint64_t factor) {
 ++gather_calls;return hex_test_gather(p,initial,stop,quantum,entries,bytes,work,factor);
}
LEAN_EXPORT lean_obj_res hex_test_zero_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(zero_scans));
}
LEAN_EXPORT lean_obj_res hex_test_mersenne_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(mersenne_vectors));
}
LEAN_EXPORT lean_obj_res hex_test_byte_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(byte_calls));
}
LEAN_EXPORT lean_obj_res hex_test_counts(lean_obj_arg world) {
 (void)world;lean_object *pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(pair,0,lean_box_uint64(scan_calls));
 lean_ctor_set(pair,1,lean_box_uint64(gather_calls));
 return lean_io_result_mk_ok(pair);
}
LEAN_EXPORT lean_obj_res hex_test_vector_counts(lean_obj_arg world) {
 (void)world;lean_object *pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(pair,0,lean_box_uint64(vector_contiguous));
 lean_ctor_set(pair,1,lean_box_uint64(vector_gather));
 return lean_io_result_mk_ok(pair);
}
LEAN_EXPORT lean_obj_res hex_test_widths(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint32(vector_widths));
}
LEAN_EXPORT lean_obj_res hex_test_avx2(lean_obj_arg world) {
 (void)world;
#if HEX_GROEBNER_AVX2
 return lean_io_result_mk_ok(lean_box(hex_avx2_available()));
#else
 return lean_io_result_mk_ok(lean_box(0));
#endif
}
'''.replace("WHOLECODE", json.dumps(str(ROOT / "HexGroebner/ffi/matrix_eliminate.c"))).replace("HITCODE", json.dumps(str(ROOT / "HexGroebner/ffi/monomial_hit.c"))).replace("ROW_SOURCE", json.dumps(str(ROOT / "HexGroebner/ffi/row_update.c"))).replace("SOURCE", json.dumps(str(source))).replace("HEADER", json.dumps(str(source.parent / "matrix_simd.h"))))
        config = '''import Lake
open Lake DSL System
package GroebnerMatrixChecks
require Hex from ROOT

def probeO (pkg : Package) (name : String) (flags : Array String) : FetchM (Job FilePath) := do
  let source ← inputTextFile (pkg.dir / "probe.c")
  let scan ← inputTextFile (FilePath.mk SCAN)
  let simd ← inputTextFile (FilePath.mk SIMD)
  let body ← inputTextFile (FilePath.mk BODY)
  let row ← inputTextFile (FilePath.mk ROW)
  let trie ← inputTextFile (FilePath.mk TRIE)
  let hit ← inputTextFile (FilePath.mk HITCODE)
  let whole ← inputTextFile (FilePath.mk WHOLECODE)
  let inputs := ((source.zipWith (fun s _ => s) scan).zipWith (fun s _ => s) simd).zipWith (fun s _ => s) body
  let inputs := (inputs.zipWith (fun s _ => s) row).zipWith (fun s _ => s) trie
  let inputs := inputs.zipWith (fun s _ => s) hit
  let inputs := inputs.zipWith (fun s _ => s) whole
  buildO (pkg.dir / defaultBuildDir / (name ++ ".o")) inputs
    #["-isystem", (← getLeanIncludeDir).toString] flags
    (compiler := FilePath.mk COMPILER)
    (extraDepTrace := do addPureTrace COMPILER "compiler"; pure BuildTrace.nil)
'''.replace("ROOT", json.dumps(str(ROOT))).replace("SCAN", json.dumps(str(source))).replace(
            "SIMD", json.dumps(str(source.parent / "matrix_simd.h"))).replace(
            "BODY", json.dumps(str(source.parent / "matrix_scan_impl.h"))).replace(
            "ROW", json.dumps(str(source.parent / "row_update.c"))).replace("COMPILER", json.dumps(cc)).replace("TRIE", json.dumps(str(source.parent / "trie_lookup.h"))).replace("HITCODE", json.dumps(str(source.parent / "monomial_hit.c"))).replace("WHOLECODE", json.dumps(str(source.parent / "matrix_eliminate.c")))
        flags = ["-O3", "-g", "-Wall", "-Wextra", "-Werror", "-fPIC", "-DLEAN_EXPORTING"]
        if sanitize:
            flags += ["-fsanitize=address,undefined", "-fno-sanitize-recover=undefined", "-fno-omit-frame-pointer"]
        link_args = ["-Wl,--wrap=lean_hex_groebner_remap_index", "-Wl,--wrap=lean_hex_groebner_append_zeros", "-Wl,--wrap=lean_hex_groebner_remap_columns", "-Wl,--wrap=lean_hex_scan_transition", "-Wl,--wrap=lean_hex_gather",
                     "-Wl,--wrap=lean_hex_groebner_equal_bytes",
                     "-Wl,--wrap=lean_hex_groebner_equal_products",
                     "-Wl,--wrap=lean_hex_groebner_eliminate_matrix",
                     "-Wl,--wrap=lean_hex_groebner_combine_owned",
                     "-Wl,--wrap=lean_hex_groebner_search_monomial",
                     "-Wl,--wrap=lean_hex_groebner_compare_monomials", "-Wl,--wrap=lean_hex_groebner_lookup_trie", "-Wl,--wrap=lean_hex_groebner_validate_trie"] + libraries
        targets = []
        for variant, extra in VARIANTS.items():
            module = "Check" + variant
            target = "check" + variant
            targets.append(target)
            (directory / (module + ".lean")).write_text('''import HexGroebner.NativeChecks
@[extern "hex_test_remap_count"] opaque remapCount : IO UInt64
@[extern "hex_test_index_count"] opaque indexCount : IO UInt64
@[extern "hex_test_zero_append_count"] opaque zeroAppendCount : IO UInt64
@[extern "hex_test_remap_aliases"] opaque remapAliases : IO Bool
@[extern "hex_test_index_aliases"] opaque indexAliases : IO Bool
@[extern "hex_test_comparison_count"] opaque comparisonCount : IO UInt64
@[extern "hex_test_comparison_declines"] opaque comparisonDeclines : IO UInt64
@[extern "hex_test_trie_counts"] opaque trieCounts : IO (UInt64 × UInt64)
@[extern "hex_test_counts"] opaque counts : IO (UInt64 × UInt64)
@[extern "hex_test_whole_modes"] opaque wholeModes : IO (UInt64 × UInt64)
@[extern "hex_test_whole_counts"] opaque wholeCounts : IO (UInt64 × UInt64)
@[extern "hex_test_byte_count"] opaque byteCount : IO UInt64
@[extern "hex_test_search_count"] opaque searchCount : IO UInt64
@[extern "hex_test_accept_count"] opaque acceptedCount : IO UInt64
@[extern "hex_test_insert_count"] opaque insertCount : IO UInt64
@[extern "hex_test_unique_count"] opaque uniqueCount : IO UInt64
@[extern "hex_test_owned_runtime"] opaque ownedRuntime : IO Bool
@[extern "hex_test_deferred_count"] opaque deferredCount : IO UInt64
@[extern "hex_test_alias_mask"] opaque aliasMask : IO UInt64
@[extern "hex_test_alias_count"] opaque aliasCount : IO UInt64
@[extern "hex_test_product_count"] opaque productCount : IO UInt64
@[extern "hex_test_vector_counts"] opaque vectorCounts : IO (UInt64 × UInt64)
@[extern "hex_test_avx2"] opaque avx2 : IO Bool
@[extern "hex_test_widths"] opaque widths : IO UInt32
@[extern "hex_test_zero_count"] opaque zeroCount : IO UInt64
@[extern "hex_test_mersenne_count"] opaque mersenneCount : IO UInt64
def main : IO Unit := do
  if !(← indexAliases) then throw (IO.userError "exclusive index/zero ownership mismatch")
  if !(← remapAliases) then throw (IO.userError "exclusive borrowed column-map alias mismatch")
  if !(← ownedRuntime) then throw (IO.userError "native layout or linear resize mismatch")
  IO.println "native constructor layout and marked-linear growth passed"
  let beforeOwned ← uniqueCount
  let beforeAlias ← aliasCount
  Hex.Groebner.NativeChecks.runOwned
  let afterOwned ← uniqueCount
  let afterAlias ← aliasCount
  if afterOwned ≤ beforeOwned || afterAlias ≤ beforeAlias || (← aliasMask) != 15 then
    throw (IO.userError "exclusive alias insertion was not exercised")
  IO.println s!"exclusive owned comparisons: reuses={afterOwned-beforeOwned}, aliased insertions={afterAlias-beforeAlias}"
  Hex.Groebner.NativeChecks.run
  let modes ← wholeModes
  if modes.1 == 0 || modes.2 == 0 then throw (IO.userError "native joint/independent matrices not covered")
  IO.println s!"whole matrix joint/independent accepted: {modes}"
  let indexBefore ← indexCount
  let zeroAppendBefore ← zeroAppendCount
  if indexBefore == 0 || zeroAppendBefore == 0 then throw (IO.userError "packed index/zero native checks unused")
  let remapBefore ← remapCount
  if remapBefore == 0 then throw (IO.userError "native column remapping not exercised")
  let wholeBefore ← wholeCounts
  let primitiveCompared ← byteCount
  let primitiveProducts ← productCount
  let beforeZero ← zeroCount
  let comparedBefore ← comparisonCount
  let declinedBefore ← comparisonDeclines
  let trieBefore ← trieCounts
  let primitiveUnique ← uniqueCount
  let primitiveInserts ← insertCount
  let primitiveAccepted ← acceptedCount
  let primitiveDeferred ← deferredCount
  Hex.Groebner.NativeChecks.runF4
  let wholeAfter ← wholeCounts
  if wholeAfter.1 ≤ wholeBefore.1 || wholeAfter.2 ≤ wholeBefore.2 then throw (IO.userError "F4 did not exercise accepted/deferred whole matrices")
  IO.println s!"whole matrix accepted/deferred: {wholeAfter}; F4 accepted/deferred: {wholeAfter.1-wholeBefore.1}/{wholeAfter.2-wholeBefore.2}"
  let f4Unique ← uniqueCount
  if f4Unique ≤ primitiveUnique then throw (IO.userError "F4 did not exercise exclusive table reuse")
  let f4Inserts ← insertCount
  if f4Inserts ≤ primitiveInserts then throw (IO.userError "F4 did not exercise native monomial insertion")
  let f4Accepted ← acceptedCount
  if f4Accepted-f4Inserts ≤ primitiveAccepted-primitiveInserts then
    throw (IO.userError "F4 did not exercise non-inserting monomial lookup")
  let f4Searches ← searchCount
  let f4Deferred ← deferredCount
  let trieAfter ← trieCounts
  if trieAfter.1 ≤ trieBefore.1 || trieAfter.2 != trieBefore.2 then
    throw (IO.userError "F4 did not obtain valid native trie answers")
  IO.println s!"trie calls/declines: {trieAfter}; F4 calls: {trieAfter.1-trieBefore.1}"
  let afterZero ← zeroCount
  let comparedAfter ← comparisonCount
  let declinedAfter ← comparisonDeclines
  let accepted := (comparedAfter-comparedBefore)-(declinedAfter-declinedBefore)
  if accepted == 0 || declinedAfter != declinedBefore then
    throw (IO.userError "F4 did not obtain bounded native comparison answers")
  IO.println s!"native monomial calls: {comparedAfter}, declines: {declinedAfter}; F4 accepted: {accepted}, F4 declines: {declinedAfter-declinedBefore}"
  IO.println s!"packed interning: searches={f4Searches}, accepted={f4Accepted}, lookups={f4Accepted-f4Inserts}, insertions={f4Inserts}, unique={f4Unique}, deferrals={f4Deferred}, F4 deferrals={f4Deferred-primitiveDeferred}"
  let f4Compared ← byteCount
  let f4Products ← productCount
  if f4Products ≤ primitiveProducts then throw (IO.userError "F4 did not exercise arena product validation")
  if f4Compared ≤ primitiveCompared then throw (IO.userError "F4 did not exercise cache comparison")
  Hex.Groebner.NativeChecks.runCache
  let cacheCompared ← byteCount
  let cacheProducts ← productCount
  if cacheProducts ≤ f4Products then throw (IO.userError "cache checks did not exercise arena product validation")
  if cacheCompared ≤ f4Compared then throw (IO.userError "cache checks did not exercise byte binding")
  let beforeMersenne ← mersenneCount
  Hex.Groebner.NativeChecks.runMersenneF4
  let mersenne ← mersenneCount
  let indexAfter ← indexCount
  let zeroAppendAfter ← zeroAppendCount
  if indexAfter ≤ indexBefore || zeroAppendAfter ≤ zeroAppendBefore then
    throw (IO.userError "F4/cache checks did not exercise packed index/zero kernels")
  IO.println s!"native index remaps: total={indexAfter}, F4/cache={indexAfter-indexBefore}; zero appends={zeroAppendAfter}"
  let remapAfter ← remapCount
  if remapAfter ≤ remapBefore then throw (IO.userError "F4/cache checks did not exercise native column remapping")
  IO.println s!"native column remaps: total={remapAfter}, F4/cache={remapAfter-remapBefore}"
  let (scan,gather) ← counts
  let compared ← byteCount
  if scan == 0 || gather == 0 || compared == 0 then throw (IO.userError "test override was not called")
  let available ← avx2
  let (contiguous,gathered) ← vectorCounts
  let covered ← widths
  IO.println s!"native call counts: scan={scan}, gather={gather}; AVX2={available}, contiguous={contiguous}, strided={gathered}, width paths={covered}, byte comparisons={compared}, product validations={cacheProducts}, Mersenne vectors={mersenne}, zero blocks={afterZero}, F4 zero blocks={afterZero-beforeZero}"
  if VECTOR && available && afterZero ≤ beforeZero then
    throw (IO.userError "complete F4 did not exercise zero blocks")
  if VECTOR && available && mersenne ≤ beforeMersenne then
    throw (IO.userError "complete F4 did not exercise Mersenne vectors")
  if VECTOR && available && (contiguous == 0 || gathered == 0 || covered != 255) then
    throw (IO.userError "an AVX2 path was not exercised")
  if VECTOR && (← IO.getEnv "HEX_GROEBNER_REQUIRE_AVX2") == some "1" && !available then
    throw (IO.userError "AVX2 coverage required but unavailable")
'''.replace("VECTOR", "true" if variant in ("Native", "Remainder") else "false"))
            config += f'''\ntarget probe{variant} pkg : FilePath := probeO pkg "{variant}" #{json.dumps(flags + extra)}
lean_exe {target} where
  root := `{module}
  moreLinkObjs := #[probe{variant}]
  moreLinkArgs := #{json.dumps(link_args)}
'''
        (directory / "lakefile.lean").write_text(config)
        print("matrix variants compiler:", subprocess.check_output([cc, "--version"], text=True).splitlines()[0], flush=True)
        subprocess.run(["lake", "build", *targets], cwd=directory, check=True)
        env = dict(os.environ, ASAN_OPTIONS=os.environ.get("ASAN_OPTIONS", "detect_leaks=0"),
                   UBSAN_OPTIONS=os.environ.get("UBSAN_OPTIONS", "halt_on_error=1"),
                   LEAN_ABORT_ON_NONLINEAR="1")
        loader = os.environ.get("HEX_GROEBNER_TEST_LOADER")
        for target in targets:
            command = [str(directory / ".lake/build/bin" / target)]
            preload = libraries + ([os.environ["LD_PRELOAD"]] if os.environ.get("LD_PRELOAD") else [])
            if loader:
                library_path = os.environ.get("HEX_GROEBNER_TEST_LIBRARY_PATH")
                if library_path is None:
                    raise RuntimeError("HEX_GROEBNER_TEST_LOADER requires HEX_GROEBNER_TEST_LIBRARY_PATH")
                command = [loader, "--library-path", library_path, "--preload", os.pathsep.join(preload), *command]
                env.pop("LD_PRELOAD", None)
            elif preload:
                env["LD_PRELOAD"] = os.pathsep.join(preload)
            print(target, "ASan/UBSan" if sanitize else "ordinary", flush=True)
            subprocess.run(command, env=env, check=True)
        print(f"compiled matrix variants: {time.monotonic()-started:.2f}s elapsed", flush=True)
    finally:
        if not retained:
            shutil.rmtree(directory)


if __name__ == "__main__":
    run()
