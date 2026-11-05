#!/usr/bin/env python3
"""Run compiled matrix conformance against six native implementations.

Use HEX_GROEBNER_SANITIZE=1 for ASan/UBSan, and optionally retain the generated
project with HEX_GROEBNER_NATIVE_LOG_DIR. HEX_GROEBNER_TEST_LOADER and
HEX_GROEBNER_TEST_LIBRARY_PATH select a matching libc loader on Nix hosts.
HEX_GROEBNER_MATRIX_PROFILE selects regular, forced or packed; the latter two
compile the test-only backend controls with dedicated drivers.
HEX_GROEBNER_MATRIX_VARIANTS restricts the comma-separated implementation list.
The ELF --wrap bindings include call counters so an unused instrumented object
cannot produce a false passing sanitizer check.
"""
from __future__ import annotations

import json
import hashlib
import sys
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
VARIANTS = {"Native": [], "AVX2": ["-DHEX_GROEBNER_NO_AVX512"],
            "AVX2Remainder": ["-DHEX_GROEBNER_NO_AVX512", "-DHEX_GROEBNER_NO_UINT128"],
            "Scalar": ["-DHEX_GROEBNER_NO_AVX2"],
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


def profile_main(profile: str) -> str:
    if profile == "forced":
        return FORCED_MAIN
    if profile == "packed":
        return PACKED_MAIN
    raise ValueError("regular profile keeps its complete driver")


FORCED_MAIN = """import HexGroebner.NativeChecks
import HexGroebner.SparseBinaryConformance
@[extern "hex_test_sparse_counts"] opaque sparseCounts : IO (UInt64 × UInt64 × UInt64 × UInt64 × UInt64)
@[extern "hex_test_sparse_offsets"] opaque sparseOffsets (enabled : Bool) : IO Unit

def main : IO UInt32 := do
  let before ← sparseCounts
  let seed ← Hex.Groebner.NativeChecks.readSeed
  for offsets in [false,true] do
    sparseOffsets offsets
    match Hex.Groebner.SparseBinaryConformance.checkRandom (seed+(if offsets then 7 else 0)) with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    let smallBefore ← sparseCounts
    if !Hex.Groebner.SparseBinaryConformance.runtimeChecks (seed+(if offsets then 7 else 0)) true then
      throw (IO.userError "forced sparse F2 runtime mismatch")
    if (← sparseCounts).1 < smallBefore.1+18 then
      throw (IO.userError "forced sparse F2 small-frame hooks unused")
  sparseOffsets false
  if !Hex.Groebner.SparseBinaryConformance.shapeChecks ||
      !Hex.Groebner.SparseBinaryConformance.cardinalityChecks ||
      !Hex.Groebner.SparseBinaryConformance.malformedChecks then
    throw (IO.userError "forced sparse F2 shape/cardinality/malformed mismatch")
  let after ← sparseCounts
  if after.1 ≤ before.1 || after.2.1 ≤ before.2.1 || after.2.2.1 ≤ before.2.2.1 ||
      after.2.2.2.1 ≤ before.2.2.2.1 then throw (IO.userError "forced sparse F2 hooks unused")
  IO.println s!"PASS forced sparse F2 small/large/budget/malformed/offset/ownership: {after}"
  return 0
"""
PACKED_MAIN = """import HexGroebner.NativeChecks
import HexGroebner.SparseBinaryConformance
import HexGroebner.EliminationConformance
@[extern "hex_test_binary_groups"] opaque binaryGroups : IO UInt64
@[extern "hex_test_sparse_counts"] opaque sparseCounts : IO (UInt64 × UInt64 × UInt64 × UInt64 × UInt64)

def main : IO UInt32 := do
  let sparseBefore ← sparseCounts
  let seed ← Hex.Groebner.NativeChecks.readSeed
  match Hex.Groebner.SparseBinaryConformance.checkSelection seed true with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  let before ← binaryGroups
  let some expected := Hex.Groebner.EliminationConformance.binaryGroupBoundary seed true |
    throw (IO.userError "packed-only boundary mismatch")
  if (← binaryGroups) != before+expected.toUInt64 then
    throw (IO.userError "packed-only table count mismatch")
  if (← sparseCounts).1 != sparseBefore.1 then
    throw (IO.userError "packed-only control selected sparse")
  IO.println "PASS packed-only physical/payload boundaries, budgets and ownership"
  return 0
"""


def run() -> None:
    if platform.system() != "Linux":
        print("compiled matrix variants require ELF --wrap; ordinary Lean and standalone C checks still apply")
        return
    sys.path.insert(0, str(ROOT))
    from scripts.bench.groebner_checks import source_identity
    identity = source_identity()
    started = time.monotonic()
    profile = os.environ.get("HEX_GROEBNER_MATRIX_PROFILE", "regular")
    if profile not in {"regular", "forced", "packed"}:
        raise ValueError("unknown matrix conformance profile")
    selected = os.environ.get("HEX_GROEBNER_MATRIX_VARIANTS")
    names = selected.split(",") if selected else list(VARIANTS)
    if not names or len(names) != len(set(names)) or any(name not in VARIANTS for name in names):
        raise ValueError("unknown or duplicate matrix variants")
    variants = {name: VARIANTS[name] for name in names}
    defines = {"regular": [], "forced": ["-DHEX_GROEBNER_FORCE_SPARSE_BINARY"],
               "packed": ["-DHEX_GROEBNER_KEEP_PACKED_BINARY"]}[profile]
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
        (directory / "probe.c").write_text('''#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include RUNTIME_HEADER
#define lean_hex_groebner_subtract_row hex_test_unused_subtract
#define lean_hex_groebner_remap_columns hex_test_remap
#define lean_hex_groebner_remap_index hex_test_remap_index
#define lean_hex_groebner_clear_support hex_test_clear_support
#define lean_hex_groebner_queue_support hex_test_queue_support
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
#undef lean_hex_groebner_clear_support
#undef lean_hex_groebner_queue_support
#undef lean_hex_groebner_append_zeros
#undef lean_hex_groebner_prepare_monomial
#undef lean_hex_groebner_equal_monomial
#undef lean_hex_groebner_search_monomial
#undef lean_hex_groebner_equal_bytes
#undef lean_hex_groebner_equal_products
static uint64_t pivot_pushes=0,pivot_shared=0,pivot_shared_entries=0;
lean_obj_res __real_lean_array_push(lean_obj_arg,lean_obj_arg);
LEAN_EXPORT lean_obj_res __wrap_lean_array_push(lean_obj_arg a,lean_obj_arg value) {
 if(!lean_is_scalar(value) && lean_obj_tag(value)==0 && lean_ctor_num_objs(value)==3 &&
    !lean_is_scalar(lean_ctor_get(value,0)) && !lean_is_scalar(lean_ctor_get(value,1)) &&
    lean_is_sarray(lean_ctor_get(value,0)) && lean_is_sarray(lean_ctor_get(value,1))) {
  ++pivot_pushes;if(!lean_is_exclusive(a)) {++pivot_shared; pivot_shared_entries+=lean_array_size(a);}
 }
 return __real_lean_array_push(a,value);
}
LEAN_EXPORT lean_obj_res hex_test_reset_pivot_owners(lean_obj_arg world) {
 (void)world;pivot_pushes=pivot_shared=pivot_shared_entries=0;
 return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_pivot_owners(lean_obj_arg world) {
 (void)world;lean_object *inner=lean_alloc_ctor(0,2,0),*outer=lean_alloc_ctor(0,2,0);
 lean_ctor_set(inner,0,lean_box_uint64(pivot_shared));lean_ctor_set(inner,1,lean_box_uint64(pivot_shared_entries));
 lean_ctor_set(outer,0,lean_box_uint64(pivot_pushes));lean_ctor_set(outer,1,inner);
 return lean_io_result_mk_ok(outer);
}
LEAN_EXPORT lean_obj_res hex_test_copy_bytes(b_lean_obj_arg input,lean_obj_arg world) {
 (void)world;size_t n=lean_sarray_size(input);
 lean_object *copy=lean_alloc_sarray(1,n,n);
 for(size_t i=0;i<n;++i) lean_sarray_cptr(copy)[i]=lean_sarray_cptr(input)[i];
 return lean_io_result_mk_ok(copy);
}
static uint64_t subtract_calls=0;
__typeof__(hex_test_unused_subtract) __wrap_lean_hex_groebner_subtract_row;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_subtract_row(
 uint64_t modulus,lean_obj_arg dense,b_lean_obj_arg columns,b_lean_obj_arg coefficients,
 b_lean_obj_arg start,b_lean_obj_arg count,uint64_t factor) {
 ++subtract_calls;return hex_test_unused_subtract(modulus,dense,columns,coefficients,start,count,factor);
}
LEAN_EXPORT lean_obj_res hex_test_subtract_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(subtract_calls));
}
static uint64_t remap_calls=0;
__typeof__(hex_test_remap) __wrap_lean_hex_groebner_remap_columns;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_remap_columns(
 b_lean_obj_arg positions,b_lean_obj_arg support,b_lean_obj_arg start,
 b_lean_obj_arg count,lean_obj_arg output) {
 ++remap_calls;return hex_test_remap(positions,support,start,count,output);
}
static uint64_t support_calls=0,support_copies=0,clear_calls=0;
__typeof__(hex_test_queue_support) __wrap_lean_hex_groebner_queue_support;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_queue_support(uint64_t count,
 b_lean_obj_arg ids,b_lean_obj_arg start,b_lean_obj_arg terms,
 lean_obj_arg bits,lean_obj_arg pending) {
 ++support_calls;if(!lean_is_exclusive(bits))++support_copies;return hex_test_queue_support(count,ids,start,terms,bits,pending);
}
__typeof__(hex_test_clear_support) __wrap_lean_hex_groebner_clear_support;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_groebner_clear_support(lean_obj_arg bits,
 b_lean_obj_arg queue,b_lean_obj_arg start,b_lean_obj_arg terms) {
 ++clear_calls;if(!lean_is_exclusive(bits))++support_copies;
 return hex_test_clear_support(bits,queue,start,terms);
}
LEAN_EXPORT lean_obj_res hex_test_support_copies(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(support_copies));
}
LEAN_EXPORT lean_obj_res hex_test_support_clears(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(clear_calls));
}
LEAN_EXPORT lean_obj_res hex_test_support_aliases(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned linear=0;linear<2;++linear) for(unsigned alias=0;alias<2;++alias)
 for(unsigned shared=0;shared<2;++shared) for(unsigned fail=0;fail<2;++fail) {
  if(linear && shared) continue;
  lean_object *ids=lean_alloc_sarray(1,8,8);
  write_le(lean_sarray_cptr(ids),4,33);write_le(lean_sarray_cptr(ids)+4,4,fail?64:0);
  lean_object *bits=alias?ids:lean_alloc_sarray(1,8,8);
  if(!alias)memset(lean_sarray_cptr(bits),0,8);
  uint8_t ids_saved[8],bits_saved[8],expected[8];
  memcpy(ids_saved,lean_sarray_cptr(ids),8);memcpy(bits_saved,lean_sarray_cptr(bits),8);
  memcpy(expected,bits_saved,8);expected[4]|=2;expected[0]|=1;
  lean_object *keeper=bits,*pending=lean_alloc_array(0,4);
  if(linear)lean_sarray_mark_linear_core(bits);
  if(shared)lean_inc(keeper);
  lean_object *result=hex_test_queue_support(64,ids,lean_box(0),lean_box(2),bits,pending);
  ok=ok && lean_obj_tag(result)==(fail?0:1);
  if(!fail && lean_obj_tag(result)==1) {
   lean_object *pair=lean_ctor_get(result,0),*actual=lean_ctor_get(pair,0),*queued=lean_ctor_get(pair,1);
   ok=ok && lean_is_exclusive(actual) && lean_sarray_size(actual)==8;
   ok=ok && memcmp(lean_sarray_cptr(actual),expected,8)==0;
   ok=ok && lean_array_size(queued)==(alias?1:2) && lean_unbox(lean_array_get_core(queued,0))==33;
   if(!alias && lean_array_size(queued)==2)ok=ok && lean_unbox(lean_array_get_core(queued,1))==0;
   if(linear)ok=ok && lean_sarray_is_marked_linear(actual);
  }
  if(shared) {
   ok=ok && memcmp(lean_sarray_cptr(keeper),bits_saved,8)==0;lean_dec(keeper);
  }
  if(!alias) {
   ok=ok && memcmp(lean_sarray_cptr(ids),ids_saved,8)==0;lean_dec(ids);
  }
  lean_dec(result);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
LEAN_EXPORT lean_obj_res hex_test_support_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(support_calls));
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
 ++zero_calls;if(lean_sarray_size(output) && !lean_is_exclusive(output))++support_copies;
 return hex_test_append_zeros(output,count);
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
 for(unsigned linear=0;linear<2;++linear) for(unsigned mode=0;mode<4;++mode)
 for(unsigned test=0;test<4;++test) {
  int fail=test==1 || test==2,observe=test>=2;
  /* A marked output may be a borrowed alias, but cannot have another owner. */
  if(linear && observe) continue;
  lean_object *positions=lean_alloc_sarray(1,12,12),*support=lean_alloc_sarray(1,12,12);
  for(unsigned i=0;i<3;++i) {
   write_le(lean_sarray_cptr(positions)+4*i,4,i+1);
   write_le(lean_sarray_cptr(support)+4*i,4,fail && i==2?777:i);
  }
  uint8_t position_snapshot[12],support_snapshot[12],output_snapshot[12];
  memcpy(position_snapshot,lean_sarray_cptr(positions),12);
  memcpy(support_snapshot,lean_sarray_cptr(support),12);
  lean_object *out=mode==0?support:positions;size_t old=12;
  if(mode>=2) {out=lean_alloc_sarray(1,4,mode==2?4:32);write_le(lean_sarray_cptr(out),4,37);old=4;}
  memcpy(output_snapshot,lean_sarray_cptr(out),old);lean_object *keeper=out;
  if(linear) lean_sarray_mark_linear_core(out);
  if(observe) lean_inc(keeper);
  lean_object *result=hex_test_remap(positions,support,lean_box(0),lean_box(3),out);
  ok=ok && lean_obj_tag(result)==(fail?0:1);
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
  if(mode!=1) ok=ok && lean_is_exclusive(positions) &&
    memcmp(lean_sarray_cptr(positions),position_snapshot,12)==0;
  if(mode!=0) ok=ok && lean_is_exclusive(support) &&
    memcmp(lean_sarray_cptr(support),support_snapshot,12)==0;
  lean_dec(result);if(mode!=1) lean_dec(positions);if(mode!=0) lean_dec(support);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
LEAN_EXPORT lean_obj_res hex_test_index_aliases(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned linear=0;linear<2;++linear) for(unsigned mode=0;mode<4;++mode)
 for(unsigned test=0;test<4;++test) {
  int fail=test==1 || test==2,observe=test>=2;
  /* A marked output may be a borrowed alias, but cannot have another owner. */
  if(linear && observe) continue;
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
   for(unsigned i=0;i<4;++i) ok=ok && lean_sarray_cptr(keeper)[i]==37;
   lean_dec(keeper);
  }
  lean_dec(result);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
static uint64_t batch_hits=0,batch_terms=0,batch_deferrals=0,batch_waste=0,batch_bound_errors=0;
static uint64_t batch_insertions=0;
static const uint8_t *product_snapshot=NULL;
static size_t product_snapshot_size=0;
static void check_product_borrow(b_lean_obj_arg support) {
 if(product_snapshot) {
  assert(lean_sarray_size(support)==product_snapshot_size);
  assert(memcmp(lean_sarray_cptr(support),product_snapshot,product_snapshot_size)==0);
 }
}
#define HEX_GROEBNER_PRODUCTS_BORROWED(support) check_product_borrow(support)
#define HEX_GROEBNER_PRODUCTS_INSERTED(n) (batch_insertions+=(n))
#define HEX_GROEBNER_PRODUCTS_DEFERRED(w) (++batch_deferrals,batch_waste+=(w),batch_bound_errors+=((w)>4096))
#define HEX_GROEBNER_PRODUCTS_FOUND(n) (++batch_hits,batch_terms+=(n))
static uint64_t fused_success=0,fused_insert=0,fused_unique=0,fused_deferred=0,unique_alias=0,unique_alias_mask=0;
#define HEX_GROEBNER_DEFERRED() (++fused_deferred)
#define HEX_GROEBNER_UNIQUE_ALIAS(mask) (++unique_alias,unique_alias_mask|=(mask))
#define HEX_GROEBNER_TABLE_UNIQUE() (++fused_unique)
#define HEX_GROEBNER_INSERT_FOUND() (++fused_insert)
#define HEX_GROEBNER_HIT_FOUND() (++fused_success)
#define HEX_GROEBNER_HIT_HELPERS
#define lean_hex_monomial_products_attempt hex_test_products_attempt
#define lean_hex_groebner_combine_owned hex_test_combine_owned
#include HITCODE
#undef lean_hex_groebner_combine_owned
#undef lean_hex_monomial_products_attempt
/* Build an RC=1 table directly: no Lean variable can retain a snapshot and
   accidentally turn the tested operation into the shared-table branch. */
LEAN_EXPORT lean_obj_res hex_test_product_aliases(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned mode=0;mode<11;++mode) for(unsigned linear=0;linear<2;++linear)
 for(unsigned spare=0;spare<2;++spare) for(unsigned observe=0;observe<3;++observe) {
  /* Multiple owning fields deliberately share arenas only when unmarked. */
  if(linear && (mode>=6 || observe==2)) continue;
  unsigned count=mode==7 || mode==10?8:3;
  size_t sizes[5]={count*4,count*24,32,128,count*4};lean_object *arenas[5];
  for(unsigned i=0;i<5;++i) {
   arenas[i]=lean_alloc_sarray(1,sizes[i],sizes[i]+(spare?128:0));
   memset(lean_sarray_cptr(arenas[i]),0,sizes[i]);
  }
  for(unsigned i=0;i<count;++i) {
   write_le(lean_sarray_cptr(arenas[0])+4*i,4,i);
   uint8_t *m=lean_sarray_cptr(arenas[1])+24*i;
   hit_write64(m,i);hit_write64(m+8,i?1:0);hit_write64(m+16,0);
   write_le(lean_sarray_cptr(arenas[4])+4*i,4,i);
  }
  write_le(lean_sarray_cptr(arenas[3]),4,count);
  write_le(lean_sarray_cptr(arenas[3])+4,4,1);
  write_le(lean_sarray_cptr(arenas[2]),4,1);
  /* Intra-table aliases: exponents/links have identical complete contents;
     each workspace alias is also a valid pre-existing scratch buffer. */
  if(mode==6) {lean_dec(arenas[4]);arenas[4]=arenas[0];lean_inc(arenas[4]);}
  if(mode>=7) {
   unsigned source=mode==7?0:mode==8?1:mode==9?3:4;
   lean_dec(arenas[2]);arenas[2]=arenas[source];lean_inc(arenas[2]);sizes[2]=sizes[source];
  }
  unsigned support_arena=mode?mode<=5?mode-1:0:5;
  lean_object *support;
  size_t start=0;
  if(support_arena==5) {support=lean_alloc_sarray(1,4,4);write_le(lean_sarray_cptr(support),4,1);}
  else {
   support=arenas[support_arena];
   start=support_arena==0 || support_arena==3 || support_arena==4?1:support_arena==1?6:0;
  }
  uint8_t snapshots[5][256],support_copy[256];
  for(unsigned i=0;i<5;++i) memcpy(snapshots[i],lean_sarray_cptr(arenas[i]),sizes[i]);
  size_t support_size=lean_sarray_size(support);memcpy(support_copy,lean_sarray_cptr(support),support_size);
  if(linear) for(unsigned i=0;i<5;++i) lean_sarray_mark_linear_core(arenas[i]);
  if(observe==1 && mode) lean_inc(support);
  if(observe==2) for(unsigned i=0;i<5;++i) lean_inc(arenas[i]);
  lean_object *index=lean_alloc_ctor(0,2,0);
  lean_ctor_set(index,0,arenas[3]);lean_ctor_set(index,1,arenas[4]);
  lean_object *table=lean_alloc_ctor(0,8,1);
  lean_ctor_set(table,0,lean_box(1));lean_ctor_set(table,1,arenas[0]);lean_ctor_set(table,2,arenas[1]);
  lean_ctor_set(table,3,lean_box(count));lean_ctor_set(table,4,arenas[2]);lean_ctor_set(table,5,index);
  lean_ctor_set(table,6,lean_box(0));lean_ctor_set(table,7,lean_box(0));
  lean_ctor_set_uint8(table,8*sizeof(void*),2);
  assert(lean_is_exclusive(table));
  uint8_t prepared[32];
  assert(prepare_monomial(1,4,1,count,1,count-1,snapshots[0],count*4,prepared,32));
  uint64_t visited=0;product_snapshot=support_copy;product_snapshot_size=support_size;
  lean_object *result=products_hits(table,support,lean_box(count-1),lean_box(start),lean_box(1),
    lean_box(100),lean_box(10000),lean_box(10000),1,&visited);
  product_snapshot=NULL;
  ok=ok && result!=NULL;
  assert(result!=NULL);
  lean_object *updated=lean_ctor_get(result,1),*ids=lean_ctor_get(lean_ctor_get(result,0),0);
  ok=ok && updated==table && lean_is_exclusive(updated) && lean_obj_tag(lean_ctor_get(result,0))==1;
  ok=ok && lean_unbox(lean_ctor_get(updated,0))==1 && lean_unbox(lean_ctor_get(updated,3))==count+1;
  ok=ok && lean_unbox(lean_ctor_get(updated,6))==0 && lean_unbox(lean_ctor_get(updated,7))==2*count+5;
  ok=ok && lean_ctor_get_uint8(updated,8*sizeof(void*))==2 && visited==2*count+5;
  ok=ok && lean_sarray_size(ids)==4 && read_le(lean_sarray_cptr(ids),4)==count;
  lean_object *new_index=lean_ctor_get(updated,5);
  lean_object *out[5]={lean_ctor_get(updated,1),lean_ctor_get(updated,2),lean_ctor_get(updated,4),
    lean_ctor_get(new_index,0),lean_ctor_get(new_index,1)};
  uint8_t expected_exponents[40],expected_metadata[240],expected_heads[128],expected_links[40];
  memcpy(expected_exponents,snapshots[0],count*4);write_le(expected_exponents+count*4,4,count);
  memcpy(expected_metadata,snapshots[1],count*24);memcpy(expected_metadata+count*24,prepared+4,16);
  hit_write64(expected_metadata+count*24+16,0);
  memcpy(expected_heads,snapshots[3],128);write_le(expected_heads,4,count+1);
  memcpy(expected_links,snapshots[4],count*4);write_le(expected_links+count*4,4,count);
  const uint8_t *expected[5]={expected_exponents,expected_metadata,prepared,expected_heads,expected_links};
  size_t output_sizes[5]={(count+1)*4,(count+1)*24,32,128,(count+1)*4};
  for(unsigned i=0;i<5;++i) {
   ok=ok && lean_is_exclusive(out[i]) && lean_sarray_size(out[i])==output_sizes[i];
   if(lean_sarray_size(out[i])==output_sizes[i]) ok=ok && memcmp(lean_sarray_cptr(out[i]),expected[i],output_sizes[i])==0;
   if(linear) ok=ok && lean_sarray_is_marked_linear(out[i]);
   if(!mode && !observe && spare && (i==0 || i==1 || i==4)) ok=ok && out[i]==arenas[i];
  }
  if(!mode) {ok=ok && memcmp(lean_sarray_cptr(support),support_copy,support_size)==0;lean_dec(support);}
  if(observe==1 && mode) {
   ok=ok && memcmp(lean_sarray_cptr(support),support_copy,support_size)==0;
   if(linear) ok=ok && lean_sarray_is_marked_linear(support);
   lean_dec(support);
  }
  if(observe==2) for(unsigned i=0;i<5;++i) {
   ok=ok && lean_sarray_size(arenas[i])==sizes[i] && memcmp(lean_sarray_cptr(arenas[i]),snapshots[i],sizes[i])==0;
   lean_dec(arenas[i]);
  }
  lean_dec(result);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
static lean_object *test_product_table(void) {
 lean_object *es=lean_alloc_sarray(1,32,32),*meta=lean_alloc_sarray(1,192,192);
 lean_object *workspace=lean_alloc_sarray(1,32,32),*heads=lean_alloc_sarray(1,256,256),*links=lean_alloc_sarray(1,32,32);
 memset(lean_sarray_cptr(heads),0,256);memset(lean_sarray_cptr(workspace),0,32);
 for(unsigned i=0;i<8;++i) write_le(lean_sarray_cptr(es)+4*i,4,i);
 for(unsigned i=0;i<8;++i) {
  uint8_t prepared[32];assert(prepare_monomial(0,4,1,8,i,i,lean_sarray_cptr(es),32,prepared,32));
  memcpy(lean_sarray_cptr(meta)+24*i,prepared+4,24);
  uint64_t hash=read_le(prepared+20,4)|(read_le(prepared+24,4)<<32);
  size_t slot=(size_t)(hit_mix(hash)&63);
  uint64_t previous=read_le(lean_sarray_cptr(heads)+slot*4,4);
  write_le(lean_sarray_cptr(links)+i*4,4,previous);write_le(lean_sarray_cptr(heads)+slot*4,4,i+1);
 }
 lean_object *index=lean_alloc_ctor(0,2,0);lean_ctor_set(index,0,heads);lean_ctor_set(index,1,links);
 lean_object *table=lean_alloc_ctor(0,8,1);
 lean_ctor_set(table,0,lean_box(1));lean_ctor_set(table,1,es);lean_ctor_set(table,2,meta);
 lean_ctor_set(table,3,lean_box(8));lean_ctor_set(table,4,workspace);lean_ctor_set(table,5,index);
 lean_ctor_set(table,6,lean_box(64));lean_ctor_set(table,7,lean_box(0));lean_ctor_set_uint8(table,8*sizeof(void*),2);
 return table;
}
static int test_product_tables_equal(b_lean_obj_arg a,b_lean_obj_arg b) {
 for(unsigned i=0;i<8;++i) {
  lean_object *x=lean_ctor_get(a,i),*y=lean_ctor_get(b,i);
  if(i==1 || i==2 || i==4) {if(!lean_sarray_eq(x,y))return 0;}
  else if(i==5) {
   if(!lean_sarray_eq(lean_ctor_get(x,0),lean_ctor_get(y,0)) ||
      !lean_sarray_eq(lean_ctor_get(x,1),lean_ctor_get(y,1)))return 0;
  } else if(!lean_nat_dec_eq(x,y))return 0;
 }
 return lean_ctor_get_uint8(a,8*sizeof(void*))==lean_ctor_get_uint8(b,8*sizeof(void*));
}
LEAN_EXPORT lean_obj_res hex_test_product_exclusive(lean_obj_arg world) {
 (void)world;int ok=1;
 for(unsigned insert=0;insert<2;++insert) {
  lean_object *table=test_product_table(),*expected=test_product_table();
  lean_object *support=lean_alloc_sarray(1,12,12);unsigned right=insert?7:0;
  for(unsigned i=0;i<3;++i) write_le(lean_sarray_cptr(support)+i*4,4,insert?(i==1?2:1):i);
  unsigned ids[3];
  /* Independent owned scalar operations supply complete table expectations;
     add each product's separate operand-validation charge before the call. */
  for(unsigned i=0;i<3;++i) {
   uint64_t work=lean_unbox(lean_ctor_get(expected,7))+1;
   lean_dec(lean_ctor_get(expected,7));lean_ctor_set(expected,7,lean_uint64_to_nat(work));
   lean_object *attempt=hit_compute(expected,1,lean_box(read_le(lean_sarray_cptr(support)+i*4,4)),
     lean_box(right),lean_box(100),lean_box(10000),lean_box(10000),lean_box(work));
   assert(lean_obj_tag(attempt)==0);lean_object *result=lean_ctor_get(attempt,0);
   ids[i]=lean_unbox(lean_ctor_get(lean_ctor_get(result,0),0));expected=lean_ctor_get(result,1);
   lean_inc(expected);lean_dec(attempt);assert(lean_is_exclusive(expected));
  }
  uint64_t visited=0;assert(lean_is_exclusive(table));
  lean_object *result=products_hits(table,support,lean_box(right),lean_box(0),lean_box(3),
    lean_box(100),lean_box(10000),lean_box(10000),1,&visited);
  assert(result!=NULL);lean_object *actual=lean_ctor_get(result,1);
  lean_object *output=lean_ctor_get(lean_ctor_get(result,0),0);
  ok=ok && actual==table && lean_is_exclusive(actual) && test_product_tables_equal(actual,expected);
  ok=ok && lean_sarray_size(output)==12 && lean_unbox(lean_ctor_get(actual,3))==(insert?10:8);
  for(unsigned i=0;i<3;++i) ok=ok && read_le(lean_sarray_cptr(output)+i*4,4)==ids[i];
  if(insert) {
   lean_object *index=lean_ctor_get(actual,5),*heads=lean_ctor_get(index,0);
   unsigned changed=0;
   for(unsigned slot=0;slot<64;++slot) if(read_le(lean_sarray_cptr(heads)+4*slot,4)>8)++changed;
   ok=ok && changed==2;
  }
  lean_dec(result);lean_dec(expected);lean_dec(support);
 }
 return lean_io_result_mk_ok(lean_box(ok));
}
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
static uint64_t mersenne_vectors=0,zero_scans=0,packets16=0;
static uint32_t widths16=0;
#define HEX_GROEBNER_AVX512_USED(w,c) (++packets16,widths16|=1u<<(2*((w)==1?0:(w)==2?1:2)+!(c)))
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
static uint64_t dense_prepares=0,dense_scans=0,dense_updates=0,dense_admitted=0;
#define HEX_GROEBNER_DENSE_USED() (++dense_updates)
#define lean_hex_prepare_dense hex_test_prepare_dense
#define lean_hex_dense_transition hex_test_dense_transition
#define lean_hex_scan_transition hex_test_scan
#define lean_hex_gather hex_test_gather
#include SOURCE
#undef lean_hex_scan_transition
#undef lean_hex_gather
#undef lean_hex_prepare_dense
#undef lean_hex_dense_transition
__typeof__(hex_test_prepare_dense) __wrap_lean_hex_prepare_dense;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_prepare_dense(uint64_t p,b_lean_obj_arg columns,
 b_lean_obj_arg source,b_lean_obj_arg work,b_lean_obj_arg bytes) {
 ++dense_prepares;
 lean_object *result=hex_test_prepare_dense(p,columns,source,work,bytes);
 if(lean_sarray_size(lean_ctor_get(lean_ctor_get(result,0),1))) ++dense_admitted;
 return result;
}
__typeof__(hex_test_dense_transition) __wrap_lean_hex_dense_transition;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_dense_transition(uint64_t p,b_lean_obj_arg columns,
 b_lean_obj_arg slots,b_lean_obj_arg pivots,lean_obj_arg initial,b_lean_obj_arg quantum,
 b_lean_obj_arg work,b_lean_obj_arg trace,uint8_t provenance) {
 ++dense_scans;return hex_test_dense_transition(p,columns,slots,pivots,initial,quantum,work,trace,provenance);
}
LEAN_EXPORT lean_obj_res hex_test_dense_admitted(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(dense_admitted));
}
LEAN_EXPORT lean_obj_res hex_test_dense_counts(lean_obj_arg world) {
 (void)world;lean_object *tail=lean_alloc_ctor(0,2,0),*out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(dense_scans));lean_ctor_set(tail,1,lean_box_uint64(dense_updates));
 lean_ctor_set(out,0,lean_box_uint64(dense_prepares));lean_ctor_set(out,1,tail);
 return lean_io_result_mk_ok(out);
}

static uint64_t delayed_frames=0,delayed_updates=0,delayed_overflows=0,delayed_vectors=0;
static int delayed_offset_enabled=0;
static uint64_t delayed_quantum=UINT64_C(1)<<34,delayed_refused_work=0;
#define HEX_GROEBNER_DELAYED_QUANTUM delayed_quantum
#define HEX_GROEBNER_DELAYED_DEFERRED(work) (delayed_refused_work+=(work))
#define HEX_GROEBNER_DELAYED_FRAME() (++delayed_frames)
static uint64_t delayed_packet_widths[3]={0};
#define HEX_GROEBNER_DELAYED_UPDATE(width) do { ++delayed_updates; if(width) { ++delayed_vectors; ++delayed_packet_widths[(width)==1?0:(width)==2?1:2]; } } while(0)
#define HEX_GROEBNER_DELAYED_RESET(context) do { \
 matrix_context *ctx=(context); \
 if(delayed_offset_enabled) memset(lean_sarray_cptr(ctx->dense),0,(size_t)ctx->columns*8); \
 else for(uint64_t col=0;col<ctx->columns;++col) assert(delayed_read(ctx,col)==0); \
} while(0)
#define HEX_GROEBNER_DELAYED_TARGET(context) do { \
 if(delayed_offset_enabled) { \
  matrix_context *ctx=(context); \
  uint64_t offset; \
  if(ctx->width==4) offset=(ctx->p-2)*ctx->p; \
  else { \
   uint64_t room=(ctx->columns+1)*(ctx->p-1)*(ctx->p-1)+(ctx->p-1); \
   offset=((UINT64_MAX-room)/ctx->p)*ctx->p; \
  } \
  for(uint64_t col=0;col<ctx->columns;++col) delayed_write(ctx,col,delayed_read(ctx,col)+offset); \
  ++delayed_overflows; \
 } \
} while(0)
static uint64_t sparse_frames=0,sparse_updates=0,sparse_zero_checks=0,sparse_done_checks=0;
static uint64_t sparse_quantum=UINT64_C(1)<<34,sparse_refused_work=0;
static int sparse_offset_enabled=0;
#define HEX_GROEBNER_SPARSE_QUANTUM sparse_quantum
#define HEX_GROEBNER_SPARSE_FRAME() (++sparse_frames)
#define HEX_GROEBNER_SPARSE_UPDATE() (++sparse_updates)
#define HEX_GROEBNER_SPARSE_DEFERRED(work) (sparse_refused_work+=(work))
#define HEX_GROEBNER_SPARSE_RESET(context) do { matrix_context *ctx=(context); if(sparse_offset_enabled) memset(lean_sarray_cptr(ctx->dense),0,(size_t)ctx->columns*8); else for(uint64_t col=0;col<ctx->columns;++col) assert(delayed_read(ctx,col)==0); ++sparse_zero_checks; } while(0)
#define HEX_GROEBNER_SPARSE_TARGET(context) do { if(sparse_offset_enabled) { matrix_context *ctx=(context); for(uint64_t col=0;col<ctx->columns;++col) delayed_write(ctx,col,delayed_read(ctx,col)+(UINT64_MAX-UINT64_C(1))); } } while(0)
#define HEX_GROEBNER_SPARSE_DONE(context) do { matrix_context *ctx=(context); for(uint64_t col=0;col<ctx->columns;++col) assert(sparse_offset_enabled?(delayed_read(ctx,col)&1)==0:delayed_read(ctx,col)==0); ++sparse_done_checks; } while(0)
static uint64_t whole_accepted=0,whole_deferred=0,whole_joint=0,whole_independent=0;
static uint64_t binary_frames=0,binary_scans=0,binary_bytes=0;
static uint64_t binary_groups=0,binary_installed=0,binary_initialized=0;
#define HEX_GROEBNER_BINARY_ROW_INSTALLED(packed) (++binary_installed,binary_initialized+=(packed))
#define HEX_GROEBNER_BINARY_GROUPS(n) (binary_groups+=(n))
static uint64_t binary_tables=0;
#define HEX_GROEBNER_BINARY_TABLE_USED() (++binary_tables)
static uint64_t binary_projects=0;
#define HEX_GROEBNER_BINARY_PROJECT_USED() (++binary_projects)
static uint64_t binary_sparse=0,binary_words=0,binary_high_words=0;
#define HEX_GROEBNER_BINARY_SCAN_USED() (++binary_scans)
#define HEX_GROEBNER_BINARY_PIVOTS_USED(n) (++binary_frames,binary_bytes+=lean_sarray_size(c.binary_rows)+lean_sarray_size(c.binary_meta)+(c.project_rows?lean_sarray_size(c.project_rows):0)+(c.project_meta?lean_sarray_size(c.project_meta):0)+(c.project_table?lean_sarray_size(c.project_table):0))
#define HEX_GROEBNER_BINARY_SPARSE_USED() (++binary_sparse)
#define HEX_GROEBNER_BINARY_WORD_USED(id) (++binary_words,(id)>=1024?++binary_high_words:0)
#define HEX_GROEBNER_MATRIX_ACCEPTED() (++whole_accepted,independent?++whole_independent:++whole_joint)
#define HEX_GROEBNER_MATRIX_DEFERRED() (++whole_deferred)
#define HEX_GROEBNER_BINARY_POISON 1
#define lean_hex_groebner_eliminate_matrix hex_test_whole
static uint64_t continuation_phases[8]={0},continuation_successes=0;
/* cont_counts can leave its scalar cache partial for arbitrary Nat counters.
   Inspect that cache only while fast is true; the isolated F4 window uses it. */
static uint64_t continuation_reduced=0,continuation_zero=0,continuation_inverses=0;
#define HEX_GROEBNER_CONT_INVERSE() (++continuation_inverses)
#define HEX_GROEBNER_CONT_SUCCESS(initial,phase,result,reductions,zero_rows) do { \
 if((initial)!=7 && (phase)==7 && !lean_is_scalar(result) && lean_obj_tag(result)==1) { \
  lean_object *answer=lean_ctor_get(result,0); \
  if(!lean_is_scalar(answer) && lean_obj_tag(answer)==1) { ++continuation_successes; continuation_reduced+=fast && (reductions)>0; continuation_zero+=fast && (zero_rows)>0; } \
 } \
} while(0)
static uint64_t cont_exhausted[8][7]={{0}},cont_invalid_masks[6]={0};
static uint64_t cont_validation_work[2]={0};
#define HEX_GROEBNER_CONT_VALIDATE_WORK(s,w) (cont_validation_work[s]|=UINT64_C(1)<<(w))
static uint64_t cont_declined_mask=0,cont_edge_mask=0,cont_allocated_mask=0;
#define HEX_GROEBNER_CONT_EXHAUSTED(p,r,w) (cont_exhausted[p][r]|=UINT64_C(1)<<(w))
#define HEX_GROEBNER_CONT_INVALID(t,w) (cont_invalid_masks[t]|=UINT64_C(1)<<(w))
#define HEX_GROEBNER_CONT_DECLINE(w) (cont_declined_mask|=UINT64_C(1)<<(w))
#define HEX_GROEBNER_CONT_EDGE(w) (cont_edge_mask|=UINT64_C(1)<<(w))
#define HEX_GROEBNER_CONT_ALLOCATE(w) (cont_allocated_mask|=UINT64_C(1)<<(w))

static uint64_t cont_count=0,cont_factor=0,cont_ticks=0,cont_max_ticks=0,cont_max_units=0,cont_violations=0;
#define HEX_GROEBNER_CONT_BEGIN(c,r,n,o) do {cont_count=(n);cont_factor=8*(c)+((o)==65536?3:2)*(r)+(o);cont_ticks=0;} while(0)
#define HEX_GROEBNER_CONT_TICK() (++cont_ticks)
#define HEX_GROEBNER_CONT_END() do { \
 uint64_t units=cont_ticks*cont_factor; \
 if(cont_ticks>cont_count || units>1048576) ++cont_violations; \
 if(cont_ticks>cont_max_ticks) cont_max_ticks=cont_ticks; \
 if(units>cont_max_units) cont_max_units=units; \
} while(0)

#define HEX_GROEBNER_CONT_PHASE(p) (++continuation_phases[p])
#define lean_hex_matrix_advance hex_test_matrix_advance
#include STATECODE
#undef lean_hex_matrix_advance
static uint64_t continuation_calls=0;
__typeof__(hex_test_matrix_advance) __wrap_lean_hex_matrix_advance;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_matrix_advance(lean_obj_arg state,b_lean_obj_arg steps) {
 ++continuation_calls;return hex_test_matrix_advance(state,steps);
}
LEAN_EXPORT lean_obj_res hex_test_continuation_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(continuation_calls));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_successes(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(continuation_successes));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_arithmetic(lean_obj_arg world) {
 (void)world;
 lean_object *tail=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(continuation_zero));
 lean_ctor_set(tail,1,lean_box_uint64(continuation_inverses));
 lean_object *out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(continuation_reduced));lean_ctor_set(out,1,tail);
 return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res hex_test_continuation_reset_bounds(lean_obj_arg world) {
 (void)world;cont_max_ticks=cont_max_units=cont_violations=0;
 return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_outcomes(lean_obj_arg world) {
 const uint64_t widths=(UINT64_C(1)<<1)|(UINT64_C(1)<<2)|(UINT64_C(1)<<4);
 int ok=cont_validation_work[0]==widths && cont_validation_work[1]==widths && cont_declined_mask==widths && cont_edge_mask==widths && cont_allocated_mask==widths;
 for(unsigned t=2;t<=4;++t) ok=ok && cont_invalid_masks[t]==widths;
 ok=ok && cont_exhausted[1][2]==widths && cont_exhausted[1][4]==widths && cont_exhausted[1][5]==widths;
 ok=ok && cont_exhausted[2][4]==widths && cont_exhausted[2][5]==widths;
 (void)world;return lean_io_result_mk_ok(lean_box(ok));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_workspaces(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(continuation_phases[2]));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_validations(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(continuation_phases[1]));
}
LEAN_EXPORT lean_obj_res hex_test_continuation_phases(lean_obj_arg world) {
 (void)world;lean_object *tail=lean_alloc_ctor(0,2,0),*pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(continuation_phases[4]));
 lean_ctor_set(tail,1,lean_box_uint64(continuation_phases[5]));
 lean_ctor_set(pair,0,lean_box_uint64(continuation_phases[3]));lean_ctor_set(pair,1,tail);
 return lean_io_result_mk_ok(pair);
}

LEAN_EXPORT lean_obj_res hex_test_continuation_bounds(lean_obj_arg world) {
 (void)world;lean_object *tail=lean_alloc_ctor(0,2,0),*pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(cont_max_units));
 lean_ctor_set(tail,1,lean_box_uint64(cont_violations));
 lean_ctor_set(pair,0,lean_box_uint64(cont_max_ticks));lean_ctor_set(pair,1,tail);
 return lean_io_result_mk_ok(pair);
}

#define lean_hex_matrix_validate hex_test_matrix_validate
#define lean_hex_matrix_zeros hex_test_matrix_zeros
#include WHOLECODE
#undef lean_hex_matrix_validate
#undef lean_hex_matrix_zeros
#undef lean_hex_groebner_eliminate_matrix
LEAN_EXPORT lean_obj_res hex_test_sparse_offsets(uint8_t enabled,lean_obj_arg world) {
 (void)world;sparse_offset_enabled=enabled;return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_sparse_quantum(uint64_t cap,lean_obj_arg world) {
 (void)world;sparse_quantum=cap;return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_sparse_counts(lean_obj_arg world) {
 (void)world;lean_object *last=lean_alloc_ctor(0,2,0),*third=lean_alloc_ctor(0,2,0);
 lean_object *second=lean_alloc_ctor(0,2,0),*first=lean_alloc_ctor(0,2,0);
 lean_ctor_set(last,0,lean_box_uint64(sparse_done_checks));lean_ctor_set(last,1,lean_box_uint64(sparse_refused_work));
 lean_ctor_set(third,0,lean_box_uint64(sparse_zero_checks));lean_ctor_set(third,1,last);
 lean_ctor_set(second,0,lean_box_uint64(sparse_updates));lean_ctor_set(second,1,third);
 lean_ctor_set(first,0,lean_box_uint64(sparse_frames));lean_ctor_set(first,1,second);
 return lean_io_result_mk_ok(first);
}
static uint64_t primitive_validations=0,primitive_zeros=0;
static uint64_t primitive_validate_admitted=0,primitive_validate_declined=0;
static uint64_t primitive_zero_admitted=0,primitive_zero_declined=0;
__typeof__(hex_test_matrix_validate) __wrap_lean_hex_matrix_validate;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_matrix_validate(uint64_t p,b_lean_obj_arg limits,
 b_lean_obj_arg columns,b_lean_obj_arg index,b_lean_obj_arg row,b_lean_obj_arg stats) {
 lean_object *saved_limits[7],*saved_stats[8],*saved_row[2];
 for(unsigned i=0;i<7;++i)saved_limits[i]=lean_ctor_get(limits,i);
 for(unsigned i=0;i<8;++i)saved_stats[i]=lean_ctor_get(stats,i);
 for(unsigned i=0;i<2;++i)saved_row[i]=lean_ctor_get(row,i);
 size_t a=lean_sarray_size(saved_row[0]),b=lean_sarray_size(saved_row[1]);
 uint8_t *snapshot=NULL;
 if(a<=1048576 && b<=1048576) {
  snapshot=malloc(a+b+1);assert(snapshot);
  memcpy(snapshot,lean_sarray_cptr(saved_row[0]),a);
  memcpy(snapshot+a,lean_sarray_cptr(saved_row[1]),b);
 }
 ++primitive_validations;lean_object *result=hex_test_matrix_validate(p,limits,columns,index,row,stats);
 for(unsigned i=0;i<7;++i)assert(saved_limits[i]==lean_ctor_get(limits,i));
 for(unsigned i=0;i<8;++i)assert(saved_stats[i]==lean_ctor_get(stats,i));
 for(unsigned i=0;i<2;++i)assert(saved_row[i]==lean_ctor_get(row,i));
 if(snapshot) {
  assert(a==lean_sarray_size(saved_row[0]) && b==lean_sarray_size(saved_row[1]));
  assert(memcmp(snapshot,lean_sarray_cptr(saved_row[0]),a)==0);
  assert(memcmp(snapshot+a,lean_sarray_cptr(saved_row[1]),b)==0);free(snapshot);
 }
 if(lean_is_scalar(result))++primitive_validate_declined;else {
  ++primitive_validate_admitted;assert(lean_is_exclusive(result));
  lean_object *pair=lean_ctor_get(result,0);assert(lean_is_exclusive(pair));
  assert(lean_is_exclusive(lean_ctor_get(pair,0)));
  assert(lean_is_exclusive(lean_ctor_get(pair,1)));
 }
 return result;
}
__typeof__(hex_test_matrix_zeros) __wrap_lean_hex_matrix_zeros;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_matrix_zeros(b_lean_obj_arg size) {
 ++primitive_zeros;lean_object *result=hex_test_matrix_zeros(size);
 if(lean_is_scalar(result))++primitive_zero_declined;else {
  ++primitive_zero_admitted;assert(lean_is_exclusive(result));
  assert(lean_is_exclusive(lean_ctor_get(result,0)));
 }
 return result;
}
LEAN_EXPORT lean_obj_res hex_test_binary_counts(lean_obj_arg world) {
 (void)world;lean_object *tail=lean_alloc_ctor(0,2,0),*out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(binary_scans));lean_ctor_set(tail,1,lean_box_uint64(binary_bytes));
 lean_ctor_set(out,0,lean_box_uint64(binary_frames));lean_ctor_set(out,1,tail);
 return lean_io_result_mk_ok(out);
}
#include <sys/mman.h>
#include <unistd.h>

/* Put each borrowed array's final byte immediately before a protected page.
   The private kernel must read exactly four coefficients/indices per packet. */
static int delayed_guard_test(void) {
#if HEX_GROEBNER_AVX2
 if(!hex_avx2_available()) return 1;
 size_t page=(size_t)sysconf(_SC_PAGESIZE);
 for(unsigned width=1;width<=4;width*=2) for(unsigned stride=1;stride<=6;stride+=5)
  for(unsigned n=1;n<=10;++n) {
   uint8_t *cm=mmap(NULL,page*2,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
   uint8_t *vm=mmap(NULL,page*2,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
   if(cm==MAP_FAILED || vm==MAP_FAILED) return 0;
   if(mprotect(cm+page,page,PROT_NONE)||mprotect(vm+page,page,PROT_NONE)) return 0;
   uint8_t *cols=cm+page-n*4,*vals=vm+page-n*width;
   matrix_context ctx={0};ctx.columns=64;ctx.width=width;ctx.p=width==1?251:width==2?65521:INT32_MAX;ctx.modulus_squared=ctx.p*ctx.p;
   ctx.dense=matrix_zeros(64*8);
   uint64_t expected[64],factor=ctx.p-1;
   for(unsigned col=0;col<64;++col) {
    expected[col]=width==4?ctx.modulus_squared-ctx.p-col:UINT64_MAX-(UINT64_C(1)<<40)+col;
    delayed_write(&ctx,col,expected[col]);
   }
   for(unsigned j=0;j<n;++j) {
    matrix_write(cols+j*4,4,j*stride);
    matrix_write(vals+j*width,width,ctx.p-1-j);
    if(j) {
     expected[j*stride]+=factor*(ctx.p-1-j);
     if(width==4 && expected[j*stride]>=ctx.modulus_squared) expected[j*stride]-=ctx.modulus_squared;
    }
   }
   uint8_t cb[40],vb[40];memcpy(cb,cols,n*4);memcpy(vb,vals,n*width);
   delayed_pivot pivot={cols,vals,n,(n-1)*stride,0};
   if(width==4) delayed_update_wide_avx2(&ctx,&pivot,factor);
   else delayed_update_avx2(&ctx,&pivot,factor);
   for(unsigned col=0;col<64;++col) if(delayed_read(&ctx,col)!=expected[col]) return 0;
   if(memcmp(cb,cols,n*4)||memcmp(vb,vals,n*width)) return 0;
   lean_dec(ctx.dense);munmap(cm,page*2);munmap(vm,page*2);
  }
#endif
 return 1;
}
LEAN_EXPORT lean_obj_res hex_test_delayed_guard(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box(delayed_guard_test()));
}
LEAN_EXPORT lean_obj_res hex_test_delayed_width_packets(uint8_t width,lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(delayed_packet_widths[width==1?0:width==2?1:2]));
}
LEAN_EXPORT lean_obj_res hex_test_delayed_vectors(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(delayed_vectors));
}
LEAN_EXPORT lean_obj_res hex_test_delayed_available(lean_obj_arg world) {
 (void)world;
#if HEX_GROEBNER_AVX2
 return lean_io_result_mk_ok(lean_box(hex_avx2_available()));
#else
 return lean_io_result_mk_ok(lean_box(0));
#endif
}

LEAN_EXPORT lean_obj_res hex_test_delayed_quantum(uint64_t cap,lean_obj_arg world) {
 (void)world;delayed_quantum=cap;return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_delayed_refused(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(delayed_refused_work));
}
LEAN_EXPORT lean_obj_res hex_test_delayed_counts(lean_obj_arg world) {
 (void)world;lean_object *tail=lean_alloc_ctor(0,2,0),*out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(delayed_updates));lean_ctor_set(tail,1,lean_box_uint64(delayed_overflows));
 lean_ctor_set(out,0,lean_box_uint64(delayed_frames));lean_ctor_set(out,1,tail);
 return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res hex_test_delayed_offsets(uint8_t enabled,lean_obj_arg world) {
 (void)world;delayed_offset_enabled=enabled;return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res hex_test_binary_installed(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(binary_installed));
 lean_ctor_set(out,1,lean_box_uint64(binary_initialized));return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res hex_test_binary_groups(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(binary_groups));
}
LEAN_EXPORT lean_obj_res hex_test_binary_tables(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(binary_tables));
}
LEAN_EXPORT lean_obj_res hex_test_binary_projects(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(binary_projects));
}
LEAN_EXPORT lean_obj_res hex_test_binary_paths(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0),*tail=lean_alloc_ctor(0,2,0);
 lean_ctor_set(tail,0,lean_box_uint64(binary_words));lean_ctor_set(tail,1,lean_box_uint64(binary_high_words));
 lean_ctor_set(out,0,lean_box_uint64(binary_sparse));lean_ctor_set(out,1,tail);
 return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res hex_test_matrix_primitives(lean_obj_arg world) {
 (void)world;lean_object *pair=lean_alloc_ctor(0,2,0);
 lean_ctor_set(pair,0,lean_box_uint64(primitive_validations));
 lean_ctor_set(pair,1,lean_box_uint64(primitive_zeros));return lean_io_result_mk_ok(pair);
}
LEAN_EXPORT lean_obj_res hex_test_primitive_admissions(lean_obj_arg world) {
 (void)world;lean_object *outer=lean_alloc_ctor(0,2,0),*a=lean_alloc_ctor(0,2,0),*b=lean_alloc_ctor(0,2,0);
 lean_ctor_set(a,0,lean_box_uint64(primitive_validate_admitted));
 lean_ctor_set(a,1,lean_box_uint64(primitive_validate_declined));
 lean_ctor_set(b,0,lean_box_uint64(primitive_zero_admitted));
 lean_ctor_set(b,1,lean_box_uint64(primitive_zero_declined));
 lean_ctor_set(outer,0,a);lean_ctor_set(outer,1,b);return lean_io_result_mk_ok(outer);
}
static uint64_t scan_calls=0,gather_calls=0,byte_calls=0,product_calls=0;
__typeof__(hex_test_products_attempt) __wrap_lean_hex_monomial_products_attempt;
LEAN_EXPORT lean_obj_res __wrap_lean_hex_monomial_products_attempt(lean_obj_arg table,
 b_lean_obj_arg support,lean_obj_arg monomial,lean_obj_arg start,lean_obj_arg count,
 lean_obj_arg max_count,lean_obj_arg max_bytes,lean_obj_arg max_work,uint8_t native) {
 return hex_test_products_attempt(table,support,monomial,start,count,max_count,max_bytes,max_work,native);
}
LEAN_EXPORT lean_obj_res hex_test_batch_insertions(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(batch_insertions));
}
LEAN_EXPORT lean_obj_res hex_test_batch_counts(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(batch_hits));
 lean_ctor_set(out,1,lean_box_uint64(batch_terms));return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res hex_test_batch_deferrals(lean_obj_arg world) {
 (void)world;lean_object *out=lean_alloc_ctor(0,2,0),*tail=lean_alloc_ctor(0,2,0);
 lean_ctor_set(out,0,lean_box_uint64(batch_deferrals));
 lean_ctor_set(tail,0,lean_box_uint64(batch_waste));
 lean_ctor_set(tail,1,lean_box_uint64(batch_bound_errors));
 lean_ctor_set(out,1,tail);return lean_io_result_mk_ok(out);
}
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
 lean_object *result=hex_test_whole(p,limits,columns,reducers,targets,sugars,independent);
 const char *path=getenv("HEX_GROEBNER_FRAME_LOG");
 if(path && p==2 && lean_ctor_get_uint8(limits,7*sizeof(void*)+1) && lean_is_scalar(columns)) {
  uint64_t nc=lean_unbox(columns),nr=lean_array_size(reducers),nt=lean_array_size(targets),entries=0;
  for(uint64_t i=0;i<nr+nt;++i) {
   lean_object *row=lean_array_cptr(i<nr?reducers:targets)[i<nr?i:i-nr];
   entries+=lean_sarray_size(lean_ctor_get(row,0))/4;
  }
  uint64_t words=(nc+63)/64,rows=nr+nt;
  uint64_t logical=rows*65+2*entries+nc*5+nt*(entries+(nt+3)*nc+64)+nc;
  uint64_t physical=rows*words+3*entries+4*nt*nc+6*nc+nt*(rows*words+64);
  uint64_t scratch=((rows<nc?rows:nc)+1)*words*8;
  /* A loose upper bound includes all inputs, normalized reducers, maximal
     target output, headers and both workspaces. Below it, bytes cannot refuse. */
  uint64_t byte_upper=scratch+20*entries+128*rows+25*nt*nc+10*nc;
  lean_object *cap=lean_ctor_get(limits,4);
  uint64_t allowance=lean_is_scalar(cap)?lean_unbox(cap):UINT64_MAX/2;
  int accepted=!lean_is_scalar(result);
  const char *reason=accepted?"accepted":nc>131072||nr>131072||nt>4096?"shape":
    logical>(UINT64_C(1)<<38)?"logical":physical>(UINT64_C(1)<<34)?"physical":
    byte_upper<=allowance?"other_without_byte_refusal":"other_possible_byte_refusal";
  FILE *stream=fopen(path,"a");
  if(!stream) abort();
  fprintf(stream,"%llu,%llu,%llu,%llu,%s,%llu,%llu\\n",
   (unsigned long long)nc,(unsigned long long)nr,(unsigned long long)nt,
   (unsigned long long)entries,reason,(unsigned long long)byte_upper,(unsigned long long)allowance);
  if(fclose(stream)) abort();
 }
 return result;
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
LEAN_EXPORT lean_obj_res hex_test_avx512_widths(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint32(widths16));
}
LEAN_EXPORT lean_obj_res hex_test_avx512_count(lean_obj_arg world) {
 (void)world;return lean_io_result_mk_ok(lean_box_uint64(packets16));
}
LEAN_EXPORT lean_obj_res hex_test_avx512_available(lean_obj_arg world) {
 (void)world;
#if HEX_GROEBNER_AVX512
 return lean_io_result_mk_ok(lean_box(hex_avx512_available()));
#else
 return lean_io_result_mk_ok(lean_box(0));
#endif
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
'''.replace("RUNTIME_HEADER", json.dumps(str(source.parent / "matrix_runtime.h"))).replace("STATECODE", json.dumps(str(ROOT / "HexGroebner/ffi/matrix_state.c"))).replace("WHOLECODE", json.dumps(str(ROOT / "HexGroebner/ffi/matrix_eliminate.c"))).replace("HITCODE", json.dumps(str(ROOT / "HexGroebner/ffi/monomial_hit.c"))).replace("ROW_SOURCE", json.dumps(str(ROOT / "HexGroebner/ffi/row_update.c"))).replace("SOURCE", json.dumps(str(source))).replace("HEADER", json.dumps(str(source.parent / "matrix_simd.h"))))
        config = '''import Lake
open Lake DSL System
package GroebnerMatrixChecks
require Hex from ROOT

def probeO (pkg : Package) (name : String) (flags : Array String) : FetchM (Job FilePath) := do
  let source ← inputTextFile (pkg.dir / "probe.c")
  let scan ← inputTextFile (FilePath.mk SCAN)
  let simd ← inputTextFile (FilePath.mk SIMD)
  let wide ← inputTextFile (FilePath.mk WIDE_HEADER)
  let body ← inputTextFile (FilePath.mk BODY)
  let row ← inputTextFile (FilePath.mk ROW)
  let trie ← inputTextFile (FilePath.mk TRIE)
  let hit ← inputTextFile (FilePath.mk HITCODE)
  let runtimeHeader ← inputTextFile (FilePath.mk RUNTIME_HEADER)
  let whole ← inputTextFile (FilePath.mk WHOLECODE)
  let delayed ← inputTextFile (FilePath.mk DELAYED_HEADER)
  let continuation ← inputTextFile (FilePath.mk STATECODE)
  let inputs := ((source.zipWith (fun s _ => s) scan).zipWith (fun s _ => s) simd).zipWith (fun s _ => s) body
  let inputs := inputs.zipWith (fun s _ => s) wide
  let inputs := (inputs.zipWith (fun s _ => s) row).zipWith (fun s _ => s) trie
  let inputs := inputs.zipWith (fun s _ => s) hit
  let inputs := (inputs.zipWith (fun s _ => s) whole).zipWith (fun s _ => s) continuation
  let inputs := inputs.zipWith (fun s _ => s) runtimeHeader
  let inputs := inputs.zipWith (fun s _ => s) delayed
  buildO (pkg.dir / defaultBuildDir / (name ++ ".o")) inputs
    #["-isystem", (← getLeanIncludeDir).toString] flags
    (compiler := FilePath.mk COMPILER)
    (extraDepTrace := do addPureTrace COMPILER "compiler"; pure BuildTrace.nil)
'''.replace("RUNTIME_HEADER", json.dumps(str(source.parent / "matrix_runtime.h"))).replace("ROOT", json.dumps(str(ROOT))).replace("SCAN", json.dumps(str(source))).replace(
            "SIMD", json.dumps(str(source.parent / "matrix_simd.h"))).replace(
            "BODY", json.dumps(str(source.parent / "matrix_scan_impl.h"))).replace(
            "WIDE_HEADER", json.dumps(str(source.parent / "matrix_avx512.h"))).replace(
            "ROW", json.dumps(str(source.parent / "row_update.c"))).replace("COMPILER", json.dumps(cc)).replace("TRIE", json.dumps(str(source.parent / "trie_lookup.h"))).replace("HITCODE", json.dumps(str(source.parent / "monomial_hit.c"))).replace("STATECODE", json.dumps(str(source.parent / "matrix_state.c"))).replace("WHOLECODE", json.dumps(str(source.parent / "matrix_eliminate.c")))
        config = config.replace("DELAYED_HEADER", json.dumps(str(source.parent / "matrix_delayed.h")))
        flags = ["-O3", "-g", "-Wall", "-Wextra", "-Werror", "-fPIC", "-DLEAN_EXPORTING", "-DHEX_GROEBNER_ENABLE_AVX512"]
        if sanitize:
            flags += ["-fsanitize=address,undefined", "-fno-sanitize-recover=undefined", "-fno-omit-frame-pointer"]
        link_args = ["-Wl,--wrap=lean_array_push", "-Wl,--wrap=lean_hex_groebner_queue_support", "-Wl,--wrap=lean_hex_groebner_clear_support", "-Wl,--wrap=lean_hex_groebner_subtract_row", "-Wl,--wrap=lean_hex_monomial_products_attempt", "-Wl,--wrap=lean_hex_matrix_validate", "-Wl,--wrap=lean_hex_matrix_zeros", "-Wl,--wrap=lean_hex_matrix_advance", "-Wl,--wrap=lean_hex_groebner_remap_index", "-Wl,--wrap=lean_hex_groebner_append_zeros", "-Wl,--wrap=lean_hex_groebner_remap_columns", "-Wl,--wrap=lean_hex_scan_transition", "-Wl,--wrap=lean_hex_gather",
                     "-Wl,--wrap=lean_hex_prepare_dense", "-Wl,--wrap=lean_hex_dense_transition",
                     "-Wl,--wrap=lean_hex_groebner_equal_bytes",
                     "-Wl,--wrap=lean_hex_groebner_equal_products",
                     "-Wl,--wrap=lean_hex_groebner_eliminate_matrix",
                     "-Wl,--wrap=lean_hex_groebner_combine_owned",
                     "-Wl,--wrap=lean_hex_groebner_search_monomial",
                     "-Wl,--wrap=lean_hex_groebner_compare_monomials", "-Wl,--wrap=lean_hex_groebner_lookup_trie", "-Wl,--wrap=lean_hex_groebner_validate_trie"] + libraries
        targets = []
        variant_flags = {}
        for variant, extra in variants.items():
            module = "Check" + variant
            target = "check" + variant
            targets.append(target)
            (directory / (module + ".lean")).write_text('''import HexGroebner.NativeChecks
import HexGroebner.PairRowsConformance
import HexGroebner.SupportConformance
import HexGroebner.SampledConformance
import HexGroebner.DenseConformance
import HexGroebner.DenseMatrixConformance
import HexGroebner.DelayedConformance
import HexGroebner.SparseBinaryConformance
@[extern "hex_test_sparse_counts"] opaque sparseCounts : IO (UInt64 × UInt64 × UInt64 × UInt64 × UInt64)
@[extern "hex_test_sparse_offsets"] opaque sparseOffsets (enabled : Bool) : IO Unit
@[extern "hex_test_sparse_quantum"] opaque sparseQuantum (cap : UInt64) : IO Unit
@[extern "hex_test_delayed_counts"] opaque delayedCounts : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_delayed_quantum"] opaque delayedQuantum (cap : UInt64) : IO Unit
@[extern "hex_test_delayed_refused"] opaque delayedRefused : IO UInt64
@[extern "hex_test_delayed_guard"] opaque delayedGuard : IO Bool
@[extern "hex_test_delayed_vectors"] opaque delayedVectors : IO UInt64
@[extern "hex_test_delayed_width_packets"] opaque delayedWidthPackets (width : UInt8) : IO UInt64
@[extern "hex_test_delayed_available"] opaque delayedAvailable : IO Bool
@[extern "hex_test_delayed_offsets"] opaque delayedOffsets (enabled : Bool) : IO Unit
@[extern "hex_test_dense_counts"] opaque denseCounts : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_subtract_count"] opaque subtractCount : IO UInt64
@[extern "hex_test_copy_bytes"] opaque copyBytes (input : @& ByteArray) : IO ByteArray
@[extern "hex_test_reset_pivot_owners"] opaque resetPivotOwners : IO Unit
@[extern "hex_test_pivot_owners"] opaque pivotOwners : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_batch_deferrals"] opaque batchDeferrals : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_batch_counts"] opaque batchCounts : IO (UInt64 × UInt64)
@[extern "hex_test_batch_insertions"] opaque batchInsertions : IO UInt64
@[extern "hex_test_binary_counts"] opaque binaryCounts : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_binary_paths"] opaque binaryPaths : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_binary_installed"] opaque binaryInstalled : IO (UInt64 × UInt64)
@[extern "hex_test_matrix_primitives"] opaque matrixPrimitives : IO (UInt64 × UInt64)
@[extern "hex_test_primitive_admissions"] opaque primitiveAdmissions : IO ((UInt64 × UInt64) × (UInt64 × UInt64))
@[extern "hex_test_remap_count"] opaque remapCount : IO UInt64
@[extern "hex_test_continuation_count"] opaque continuationCount : IO UInt64
@[extern "hex_test_continuation_successes"] opaque continuationSuccesses : IO UInt64
@[extern "hex_test_continuation_arithmetic"] opaque continuationArithmetic : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_continuation_reset_bounds"] opaque resetContinuationBounds : IO Unit
@[extern "hex_test_continuation_validations"] opaque continuationValidations : IO UInt64
@[extern "hex_test_continuation_workspaces"] opaque continuationWorkspaces : IO UInt64
@[extern "hex_test_continuation_outcomes"] opaque continuationOutcomes : IO Bool
@[extern "hex_test_continuation_phases"] opaque continuationPhases : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_continuation_bounds"] opaque continuationBounds : IO (UInt64 × UInt64 × UInt64)
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
@[extern "hex_test_delayed_refused"] opaque delayedRefusedWork : IO UInt64
@[extern "hex_test_byte_count"] opaque byteCount : IO UInt64
@[extern "hex_test_search_count"] opaque searchCount : IO UInt64
@[extern "hex_test_accept_count"] opaque acceptedCount : IO UInt64
@[extern "hex_test_insert_count"] opaque insertCount : IO UInt64
@[extern "hex_test_unique_count"] opaque uniqueCount : IO UInt64
@[extern "hex_test_product_exclusive"] opaque productExclusive : IO Bool
@[extern "hex_test_product_aliases"] opaque productAliases : IO Bool
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
@[extern "hex_test_avx512_count"] opaque avx512Count : IO UInt64
@[extern "hex_test_avx512_widths"] opaque avx512Widths : IO UInt32
@[extern "hex_test_avx512_available"] opaque avx512Available : IO Bool
def checkDenseOwnership (primitiveSeed : Nat) : IO Unit := do
  for independent in [false,true] do
    let checkpoint := Hex.Groebner.DenseMatrixConformance.snapshotState primitiveSeed independent
    let some cache := checkpoint.densePivots | throw (IO.userError "missing dense checkpoint")
    let some held := cache.rows[0]? | throw (IO.userError "empty dense checkpoint")
    let heldBytes ← copyBytes held.dense
    let heldSource ← copyBytes held.source.coefficients
    let scheduleSeed ← Hex.Groebner.NativeChecks.readSeed
    let completed := Hex.Groebner.MatrixState.finishState (1+scheduleSeed%64) checkpoint
    let alternate := Hex.Groebner.MatrixState.finishState (64-scheduleSeed%64) checkpoint
    if completed.phase != .done || alternate.phase != .done ||
        checkpoint.nativePivots.size != 1 || cache.rows.size != 1 ||
        completed.nativePivots.size != (if independent then 3 else 6) ||
        alternate.stats != completed.stats then
      throw (IO.userError "shared dense checkpoint did not complete")
    let afterBytes ← copyBytes held.dense
    let afterSource ← copyBytes held.source.coefficients
    if heldBytes != afterBytes || heldSource != afterSource then
      throw (IO.userError "shared nonempty dense cache was mutated")
  IO.println "shared dense checkpoints: 4 IO byte comparisons"
  let beforeTiny ← wholeCounts
  let tinyRow : Hex.Groebner.SparseRow :=
    ⟨Hex.Groebner.Packed.push .u32 {} 0,Hex.Groebner.Packed.push .u32 {} 1⟩
  let tinyField : Hex.Groebner.PrimeField :=
    ⟨2147483647,Hex.Nat.isPrimeTrial_isPrime (by decide),by decide⟩
  let tiny := Hex.Groebner.eliminateWith tinyField { densePivots := true }
    (2+primitiveSeed%127) #[tinyRow] #[tinyRow]
  if !tiny.result.isOk then throw (IO.userError "small cached-option matrix failed")
  let afterTiny ← wholeCounts
  if afterTiny.1 != beforeTiny.1+1 || afterTiny.2 != beforeTiny.2 then
    throw (IO.userError "small cached-option matrix lost its bulk frame")
  IO.println "small M31 cached-option bulk frame: accepted"
  let beforeDispatch ← wholeCounts
  if !Hex.Groebner.DenseMatrixConformance.dispatchChecks primitiveSeed false then
    throw (IO.userError "public dense-option dispatch counters differ")
  let afterDispatch ← wholeCounts
  if afterDispatch.1 != beforeDispatch.1+12 || afterDispatch.2 != beforeDispatch.2 then
    throw (IO.userError "dense-option public dispatch lost bulk frames")
  if !Hex.Groebner.DenseMatrixConformance.dispatchChecks primitiveSeed true then
    throw (IO.userError "dense-option public dispatch boundary counters differ")
  if !Hex.Groebner.DenseMatrixConformance.capChecks primitiveSeed then
    throw (IO.userError "dense-option bulk work cap differs from reference")
  IO.println "public M31 cached-option bulk frames: 12 accepted; exact boundary counters and work cap passed"

def checkMersenne : IO UInt64 := do
  let before512 ← avx512Count
  let beforeMersenne ← mersenneCount
  Hex.Groebner.NativeChecks.runMersenneF4
  let mersenne ← mersenneCount
  let after512 ← avx512Count
  let paths512 ← avx512Widths
  let available512 ← avx512Available
  IO.println s!"AVX-512 packets: {after512}; full F4={after512-before512}; available={available512}; width/layout bits={paths512}"
  if available512 && paths512 != 63 then
    throw (IO.userError "an AVX-512 width/layout path was not exercised")
  if available512 && after512 ≤ before512 then
    throw (IO.userError "full F4 did not exercise AVX-512 packets")
  if WIDE && (← IO.getEnv "HEX_GROEBNER_REQUIRE_AVX512") == some "1" && !available512 then
    throw (IO.userError "AVX-512 coverage required but unavailable")
  if VECTOR && (← avx2) && mersenne ≤ beforeMersenne then
    throw (IO.userError "complete F4 did not exercise Mersenne vectors")
  return mersenne

@[extern "hex_test_binary_groups"] opaque binaryGroups : IO UInt64
@[extern "hex_test_binary_tables"] opaque binaryTables : IO UInt64
@[extern "hex_test_binary_projects"] opaque binaryProjects : IO UInt64

@[extern "hex_test_support_count"] opaque supportCount : IO UInt64
@[extern "hex_test_support_aliases"] opaque supportAliases : IO Bool
@[extern "hex_test_support_copies"] opaque supportCopies : IO UInt64
@[extern "hex_test_support_clears"] opaque supportClears : IO UInt64

private def checkSupportSystems : IO Unit := do
  let seed ← Hex.Groebner.NativeChecks.readSeed
  for route in [:3] do
    let before ← supportCount
    let clears ← supportClears
    let copies ← supportCopies
    if !Hex.Groebner.PairRowsConformance.systemChecks seed route then
      throw (IO.userError s!"support whole-system route {route} mismatch")
    if (← supportCount) ≤ before || (← supportClears) ≤ clears || (← supportCopies) != copies then
      throw (IO.userError s!"support whole-system route {route} copies={(← supportCopies)-copies}, calls={(← supportCount)-before}, clears={(← supportClears)-clears}")
    IO.println s!"support system {route} calls/clears/copies: {(← supportCount)-before}/{(← supportClears)-clears}/{(← supportCopies)-copies}"

private def checkSupport : IO Unit := do
  if !(← supportAliases) then throw (IO.userError "support queue ownership mismatch")
  let before ← supportCount
  let seed ← Hex.Groebner.NativeChecks.readSeed
  if !Hex.Groebner.SupportConformance.queueChecks seed then
    throw (IO.userError "native support queue/reference mismatch")
  if (← supportCount) ≤ before then throw (IO.userError "native support queue unused")
  if !Hex.Groebner.SupportConformance.clearChecks seed then
    throw (IO.userError "native support clear/reference mismatch")
  for native in [true,false] do
    if !Hex.Groebner.PairRowsConformance.scratchChecks native then
      throw (IO.userError "support scratch exhaustion/retry mismatch")
  let copiesBefore ← supportCopies
  let queuesBefore ← supportCount
  let clearsBefore ← supportClears
  for native in [true,false] do
    if !Hex.Groebner.PairRowsConformance.chunkChecks seed native then
      throw (IO.userError "production support chunks or separate-tail allocation mismatch")
  if (← supportCopies) != copiesBefore || (← supportCount) ≤ queuesBefore ||
      (← supportClears) ≤ clearsBefore then
    throw (IO.userError s!"production support loop copies={(← supportCopies)-copiesBefore}, calls={(← supportCount)-queuesBefore}, clears={(← supportClears)-clearsBefore}")
  IO.println s!"production support calls/clears/copies: {(← supportCount)-queuesBefore}/{(← supportClears)-clearsBefore}/{(← supportCopies)-copiesBefore}"
  IO.println s!"native support queue calls: {(← supportCount)-before}"
  checkSupportSystems

private def checkBinaryBuffers : IO Unit := do
  if !(← delayedGuard) then throw (IO.userError "delayed exact packet/guard-page test failed")
  let vectorsBefore ← delayedVectors
  let widePacketsBefore ← delayedWidthPackets 4
  let sparseBefore ← sparseCounts
  let sparseSeed ← Hex.Groebner.NativeChecks.readSeed
  for offsets in [false,true] do
    sparseOffsets offsets
    match Hex.Groebner.SparseBinaryConformance.checkRandom (sparseSeed+(if offsets then 7 else 0)) with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    match Hex.Groebner.SparseBinaryConformance.checkRuntime (sparseSeed+(if offsets then 7 else 0)) with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    match Hex.Groebner.SparseBinaryConformance.checkSelection (sparseSeed+(if offsets then 7 else 0)) with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
  sparseOffsets false
  if !Hex.Groebner.SparseBinaryConformance.shapeChecks ||
      !Hex.Groebner.SparseBinaryConformance.cardinalityChecks ||
      !Hex.Groebner.SparseBinaryConformance.malformedChecks then
    throw (IO.userError "sparse F2 shape/cardinality/malformed boundary differs")
  let some sparseWork := Hex.Groebner.SparseBinaryConformance.capChecks sparseSeed |
    throw (IO.userError "sparse F2 ordinary quantum differs")
  let refusedBefore := (← sparseCounts).2.2.2.2
  sparseQuantum (sparseWork-1).toUInt64
  if (Hex.Groebner.SparseBinaryConformance.capChecks (sparseSeed+7) (sparseWork-1)).isNone then
    throw (IO.userError "sparse F2 bounded refusal/fallback differs")
  let refusedAfter := (← sparseCounts).2.2.2.2
  if refusedAfter ≤ refusedBefore || refusedAfter-refusedBefore > 2*(sparseWork-1).toUInt64 then
    throw (IO.userError "sparse F2 discarded work missing or unbounded")
  sparseQuantum sparseWork.toUInt64
  if (Hex.Groebner.SparseBinaryConformance.capChecks (sparseSeed+14) sparseWork).isNone then
    throw (IO.userError "sparse F2 exact native work boundary differs")
  sparseQuantum (2^34)
  let sparseAfter ← sparseCounts
  if sparseAfter.1 ≤ sparseBefore.1 || sparseAfter.2.1 ≤ sparseBefore.2.1 ||
      sparseAfter.2.2.1 ≤ sparseBefore.2.2.1 || sparseAfter.2.2.2.1 ≤ sparseBefore.2.2.2.1 then
    throw (IO.userError "sparse F2 frames/updates/reset/final-state checks unused")
  IO.println s!"sparse F2 frames/updates/reset/final-state/refused: {sparseAfter}"
  let delayedBefore ← delayedCounts
  let delayedSeed ← Hex.Groebner.NativeChecks.readSeed
  for offsets in [false,true] do
    delayedOffsets offsets
    if !Hex.Groebner.DelayedConformance.runtimeChecks (delayedSeed+(if offsets then 7 else 0)) then
      throw (IO.userError "delayed native/reference rows, inputs or budget cuts differ")
  delayedOffsets false
  if !Hex.Groebner.DelayedConformance.boundaryChecks delayedSeed ||
      !Hex.Groebner.DelayedConformance.producerChecks delayedSeed then
    throw (IO.userError "delayed high columns or full producer differs")
  if !Hex.Groebner.DelayedConformance.denseChecks delayedSeed then
    throw (IO.userError "delayed dense preparation charge or cap differs")
  if !Hex.Groebner.DelayedConformance.scalarChecks delayedSeed then
    throw (IO.userError "delayed matrix differs from fully scalar Lean")
  for wide in [false,true] do
    let some work := Hex.Groebner.DelayedConformance.wideChecks delayedSeed (2^34) wide |
      throw (IO.userError "delayed widened coefficient/reducer counts differ")
    delayedQuantum (work-1).toUInt64
    if (Hex.Groebner.DelayedConformance.wideChecks (delayedSeed+17) (work-1) wide).isNone then
      throw (IO.userError "delayed widened coefficient work refusal differs")
    delayedQuantum work.toUInt64
    if (Hex.Groebner.DelayedConformance.wideChecks (delayedSeed+34) work wide).isNone then
      throw (IO.userError "delayed widened coefficient exact cap declined")
    delayedQuantum (2^34)
  let some wideWork := Hex.Groebner.DelayedConformance.wideChecks delayedSeed |
    throw (IO.userError "delayed newly admitted reductions differ")
  let refusedBefore ← delayedRefused
  delayedQuantum (wideWork-1).toUInt64
  if (Hex.Groebner.DelayedConformance.wideChecks (delayedSeed+17) (wideWork-1)).isNone then
    throw (IO.userError "delayed late work refusal differs from capped reference")
  if (← delayedRefused) ≤ refusedBefore then
    throw (IO.userError "delayed late work refusal did no charged work")
  delayedQuantum wideWork.toUInt64
  if (Hex.Groebner.DelayedConformance.wideChecks (delayedSeed+34) wideWork).isNone then
    throw (IO.userError "delayed exact work cap was declined")
  delayedQuantum (2^34)
  let delayedAfter ← delayedCounts
  let vectorsAfter ← delayedVectors
  if (← delayedAvailable) then
    if (← delayedWidthPackets 4) ≤ widePacketsBefore then
      throw (IO.userError "delayed wide four-lane packets unused")
    if vectorsAfter ≤ vectorsBefore then throw (IO.userError "delayed AVX2 packet unused")
  else if vectorsAfter != vectorsBefore then
    throw (IO.userError "delayed unavailable AVX2 packet executed")
  if delayedAfter.1 ≤ delayedBefore.1 || delayedAfter.2.1 ≤ delayedBefore.2.1 ||
      delayedAfter.2.2 ≤ delayedBefore.2.2 then
    throw (IO.userError "delayed frames, row updates or near-overflow controls unused")
  IO.println s!"delayed frames/updates/near-overflow targets: {delayedAfter}"
  let allocationBefore ← binaryCounts
  let targetBefore ← binaryPaths
  let targetSeed ← Hex.Groebner.NativeChecks.readSeed
  let some allocated := Hex.Groebner.EliminationConformance.binaryTargetChecks targetSeed |
    throw (IO.userError "target-built packed word pivot/reference mismatch")
  let allocationAfter ← binaryCounts
  let targetAfter ← binaryPaths
  if allocationAfter.1 != allocationBefore.1+2 ||
      allocationAfter.2.2 != allocationBefore.2.2+allocated.toUInt64 ||
      targetAfter.2.1 ≤ targetBefore.2.1 then
    throw (IO.userError "actual private allocation or target-built word pivot unused")
  if !Hex.Groebner.EliminationConformance.binaryQuantum targetSeed then
    throw (IO.userError "F2 logical quantum or maximum target boundary mismatch")
  let before ← binaryCounts
  let projectsBefore ← binaryProjects
  let seed ← Hex.Groebner.NativeChecks.readSeed
  let some allocated := Hex.Groebner.EliminationConformance.binaryAllocationChecks seed |
    throw (IO.userError "projected private allocation/reference mismatch")
  let after ← binaryCounts
  if after.1 != before.1+2 || after.2.2 != before.2.2+allocated.toUInt64 ||
      (← binaryProjects) != projectsBefore+2 then
    throw (IO.userError "projected private buffer payload differs")

private def checkBinary (seed : Nat) : IO Unit := do
  let symbolicSeed ← Hex.Groebner.NativeChecks.readSeed
  if !Hex.Groebner.PairRowsConformance.bitmapChecks symbolicSeed then
    throw (IO.userError "symbolic support bitmap closure mismatch")
  checkBinaryBuffers
  let groupsBefore ← binaryGroups
  let groupSeed ← Hex.Groebner.NativeChecks.readSeed
  let some expectedGroups := Hex.Groebner.EliminationConformance.binaryGroupChecks groupSeed |
    throw (IO.userError "known-pivot groups/reference mismatch")
  if (← binaryGroups) != groupsBefore+expectedGroups.toUInt64 then
    throw (IO.userError "native known-pivot group count differs")
  if !Hex.Groebner.EliminationConformance.binaryTableBoundary seed then
    throw (IO.userError "former physical-work boundary replay mismatch")
  let boundaryBefore ← binaryGroups
  let some boundaryGroups := Hex.Groebner.EliminationConformance.binaryGroupBoundary groupSeed |
    throw (IO.userError "current grouped physical-work boundary mismatch")
  if (← binaryGroups) != boundaryBefore+boundaryGroups.toUInt64 then
    throw (IO.userError "current physical boundary missed table-saving admission")
  if !Hex.Groebner.EliminationConformance.binaryHighChecks groupSeed then
    throw (IO.userError "highest-word dense projection/reference mismatch")
  let tableBefore ← binaryTables
  if !Hex.Groebner.EliminationConformance.binaryTableChecks seed then
    throw (IO.userError "known-pivot XOR table/reference mismatch")
  if (← binaryTables) ≤ tableBefore then throw (IO.userError "known-pivot XOR table unused")
  if !Hex.Groebner.EliminationConformance.binaryRandomChecks seed then
    throw (IO.userError "seeded wide projection/reference mismatch")
  let projectionBefore ← binaryProjects
  if !Hex.Groebner.EliminationConformance.binaryProjectChecks seed then
    throw (IO.userError "known-pivot projection/reference mismatch")
  if (← binaryProjects) ≤ projectionBefore then
    throw (IO.userError "known-pivot projection unused")
  let before ← binaryCounts
  let pathsBefore ← binaryPaths
  let installedBefore ← binaryInstalled
  if !Hex.Groebner.EliminationConformance.binaryChecks seed ||
      !Hex.Groebner.EliminationConformance.binaryLargeChecks seed ||
      !Hex.Groebner.EliminationConformance.binaryWorkChecks seed then
    throw (IO.userError "private packed F2 frame/reference mismatch")
  let after ← binaryCounts
  let pathsAfter ← binaryPaths
  let installedAfter ← binaryInstalled
  let initialized := installedAfter.2-installedBefore.2
  if initialized == 0 || initialized ≥ installedAfter.1-installedBefore.1 then
    throw (IO.userError "mixed frames did not skip sparse packed-row initialization")
  if pathsAfter.1 ≤ pathsBefore.1 || pathsAfter.2.1 ≤ pathsBefore.2.1 ||
      pathsAfter.2.2 ≤ pathsBefore.2.2 then
    throw (IO.userError "private F2 sparse or word pivot update unused")
  if after.1 ≤ before.1 || after.2.1 ≤ before.2.1 || after.2.2 ≤ before.2.2 then
    throw (IO.userError "private F2 pivots or word scan unused")
  IO.println s!"private F2 frames/scans/bytes: {after}"
  let f4Before ← binaryCounts
  if !Hex.Groebner.EliminationConformance.binaryFresh seed then
    throw (IO.userError "packed F2 complete F4/reference mismatch")
  let f4After ← binaryCounts
  if f4After.1 ≤ f4Before.1 then throw (IO.userError "packed F2 policy unused by complete F4")

private def checkOwnership : IO Unit := do
  if !(← indexAliases) then throw (IO.userError "exclusive index/zero ownership mismatch")
  if !(← remapAliases) then throw (IO.userError "exclusive borrowed column-map alias mismatch")
  if !(← productExclusive) then throw (IO.userError "exclusive multi-slot insertion/lookup mismatch")
  if !(← productAliases) then throw (IO.userError "exclusive product insertion/alias mismatch")
  if !(← ownedRuntime) then throw (IO.userError "native layout or linear resize mismatch")

def main : IO Unit := do
  checkOwnership
  IO.println "native constructor layout and marked-linear growth passed"
  let beforeOwned ← uniqueCount
  let beforeAlias ← aliasCount
  Hex.Groebner.NativeChecks.runOwned
  let afterOwned ← uniqueCount
  let afterAlias ← aliasCount
  if afterOwned ≤ beforeOwned || afterAlias ≤ beforeAlias || (← aliasMask) != 15 then
    throw (IO.userError "exclusive alias insertion was not exercised")
  IO.println s!"exclusive owned comparisons: reuses={afterOwned-beforeOwned}, aliased insertions={afterAlias-beforeAlias}"
  let primitiveSeed ← Hex.Groebner.NativeChecks.readSeed
  IO.println s!"primitive conformance seed: {primitiveSeed}"
  checkSupport
  checkBinary primitiveSeed
  let beforeBatchInsertions ← batchInsertions
  if !Hex.Groebner.ProductBatchConformance.insertionChecks primitiveSeed then
    throw (IO.userError "monomial batch insertion/reference state mismatch")
  let afterBatchInsertions ← batchInsertions
  if afterBatchInsertions ≤ beforeBatchInsertions then
    throw (IO.userError "native monomial batch insertion unused")
  IO.println s!"native monomial batch insertions: {afterBatchInsertions-beforeBatchInsertions}; alias/refusal states passed"
  if !Hex.Groebner.DenseMatrixConformance.frameChecks primitiveSeed then
    throw (IO.userError "dense normalized/target frame boundaries differ")
  IO.println "dense normalized/target frames: exact parent refusal and density boundaries passed"
  let beforeDense ← denseCounts
  if !Hex.Groebner.DenseConformance.packetChecks primitiveSeed ||
      !Hex.Groebner.DenseMatrixConformance.admissionChecks primitiveSeed ||
      !Hex.Groebner.DenseMatrixConformance.mixedChecks primitiveSeed ||
      !Hex.Groebner.DenseMatrixConformance.checks primitiveSeed ||
      !Hex.Groebner.DenseConformance.largeChecks primitiveSeed ||
      !Hex.Groebner.DenseConformance.boundaryChecks primitiveSeed ||
      !Hex.Groebner.DenseConformance.scanChecks primitiveSeed then
    throw (IO.userError "dense pivot scan prefix mismatch")
  let mut denseColumns : ByteArray := {}
  let mut denseValues : ByteArray := {}
  for i in [:128] do
    denseColumns := Hex.Groebner.Packed.push .u32 denseColumns i.toUInt64
    denseValues := Hex.Groebner.Packed.push .u32 denseValues (i+1).toUInt64
  let denseSource : Hex.Groebner.Native.Scan.Pivot := ⟨denseColumns,denseValues,primitiveSeed⟩
  let prepared := Hex.Groebner.Native.Dense.prepare 2147483647 128 denseSource 100000 100000
  let sourceSnapshot ← copyBytes prepared.row.source.coefficients
  let cacheSnapshot ← copyBytes prepared.row.dense
  let denseInitial : Hex.Groebner.Native.Scan.State := {
    dense := prepared.row.dense
    column := 0
    last := 127
    chargedUntil := 128
    pending := 1
    factor := 1 }
  let denseSlots := Hex.Groebner.Native.write (Hex.Groebner.Native.Dense.zeros 512) 4 0 1
  let denseOutput := Hex.Groebner.Native.Dense.transition 2147483647 128 denseSlots
    #[prepared.row] denseInitial 128 100000 0 false
  if denseOutput.state.dense != Hex.Groebner.Native.Dense.zeros 512 ||
      prepared.row.source.coefficients != sourceSnapshot || prepared.row.dense != cacheSnapshot ||
      denseInitial.dense != cacheSnapshot then
    throw (IO.userError "dense pivot source/cache/continuation snapshot was mutated")
  checkDenseOwnership primitiveSeed
  let afterDense ← denseCounts
  if afterDense.1 ≤ beforeDense.1 || afterDense.2.1 ≤ beforeDense.2.1 ||
      afterDense.2.2 ≤ beforeDense.2.2 then
    throw (IO.userError "dense pivot native materialization/update was not exercised")
  IO.println s!"dense pivot calls: {afterDense}"
  let beforeDenseF4 ← denseCounts
  let beforeDenseF4Frames ← wholeCounts
  if !Hex.Groebner.DenseMatrixConformance.fullChecks primitiveSeed then
    throw (IO.userError "complete dense/sparse F4 basis differs")
  let afterDenseF4 ← denseCounts
  let afterDenseF4Frames ← wholeCounts
  if afterDenseF4Frames.2 ≤ beforeDenseF4Frames.2 then
    throw (IO.userError "complete F4 fixture did not reach the continuation")
  IO.println s!"dense full-F4 bulk declines: {afterDenseF4Frames.2-beforeDenseF4Frames.2}"
  if afterDenseF4.2.2 ≤ beforeDenseF4.2.2 then
    throw (IO.userError "complete F4 did not exercise dense pivot updates")
  IO.println s!"dense full-F4 updates: {afterDenseF4.2.2-beforeDenseF4.2.2}"


  let beforePortableScan ← counts
  let beforePortableWhole ← wholeCounts
  let beforePortableBytes ← byteCount
  let beforePortableRemap ← remapCount
  let beforePortableIndex ← indexCount
  let beforePortableZeros ← zeroAppendCount
  let beforePortableContinuation ← continuationCount
  let beforePortableBatchDeferrals ← batchDeferrals
  let beforePortableBatches ← batchCounts
  let beforePortableProducts ← productCount
  let beforePortable ← matrixPrimitives
  for offset in [:6] do
    let seed := primitiveSeed+offset
    if !Hex.Groebner.MatrixPrimitiveConformance.portable seed then
      throw (IO.userError s!"portable matrix route failed, seed={seed}")
    Hex.Groebner.NativeChecks.runPortableF4 seed
  if (← matrixPrimitives) != beforePortable || (← counts) != beforePortableScan ||
      (← wholeCounts) != beforePortableWhole || (← byteCount) != beforePortableBytes ||
      (← remapCount) != beforePortableRemap || (← indexCount) != beforePortableIndex ||
      (← zeroAppendCount) != beforePortableZeros ||
      (← continuationCount) != beforePortableContinuation ||
      (← productCount) != beforePortableProducts || (← batchCounts) != beforePortableBatches ||
      (← batchDeferrals) != beforePortableBatchDeferrals then
    throw (IO.userError "public portable F4 called a native row/bulk/column/byte provider")
  let beforeIntegrated ← primitiveAdmissions
  for offset in [:6] do
    if !Hex.Groebner.MatrixPrimitiveConformance.integrated (primitiveSeed+offset) then
      throw (IO.userError s!"traced native matrix integration failed, seed={primitiveSeed+offset}")
  let afterIntegrated ← primitiveAdmissions
  if afterIntegrated.1.1 ≤ beforeIntegrated.1.1 || afterIntegrated.2.1 ≤ beforeIntegrated.2.1 then
    throw (IO.userError "traced elimination did not admit both native primitives")
  IO.println s!"traced elimination primitive admissions: validation={afterIntegrated.1.1-beforeIntegrated.1.1}, zero={afterIntegrated.2.1-beforeIntegrated.2.1}"
  let beforeWide ← batchCounts
  let beforeWideDeferrals ← batchDeferrals
  Hex.Groebner.NativeChecks.runProductWide
  let afterWide ← batchCounts
  let wideBatches := afterWide.1-beforeWide.1
  if wideBatches == 0 || wideBatches ≥ 128 || afterWide.2-beforeWide.2 != 128 ||
      (← batchDeferrals) != beforeWideDeferrals then
    throw (IO.userError "adaptive 22-variable multiplication did not batch every term")
  IO.println s!"adaptive 22-variable accepted batches/terms: {wideBatches}/128; deferrals=0"
  let beforeMiss ← batchDeferrals
  Hex.Groebner.NativeChecks.runProductMiss
  let afterMiss ← batchDeferrals
  if afterMiss.1 ≤ beforeMiss.1 || afterMiss.2.1 ≤ beforeMiss.2.1 then
    throw (IO.userError "last-term miss did not exercise discarded-visit diagnostic")
  IO.println s!"last-term-miss deferred calls/reservations: {afterMiss.1-beforeMiss.1}/{afterMiss.2.1-beforeMiss.2.1}"
  let beforeWideZeros ← primitiveAdmissions
  Hex.Groebner.NativeChecks.runWideWorkspaces
  let afterWideZeros ← primitiveAdmissions
  if afterWideZeros.2.1-beforeWideZeros.2.1 != 6 ||
      afterWideZeros.2.2-beforeWideZeros.2.2 != 6 then
    throw (IO.userError s!"wide workspace zero-provider admission mismatch: before={beforeWideZeros.2}, after={afterWideZeros.2}")
  IO.println "wide workspace zeros: all widths, six admitted and six declined"
  Hex.Groebner.NativeChecks.run
  let batches ← batchCounts
  if batches.1 == 0 || batches.2 == 0 then throw (IO.userError "monomial product batch unused")
  IO.println s!"monomial product batches/terms: {batches}"
  let primitives ← matrixPrimitives
  IO.println s!"native matrix validation/zero-buffer primitives: {primitives}"
  let continuationCalls ← continuationCount
  if continuationCalls == 0 then throw (IO.userError "native continuation unused")
  if !(← continuationOutcomes) then
    throw (IO.userError "native validation/workspace outcomes missing at some coefficient width")
  IO.println "native validation/workspace outcomes: all widths, errors, exhaustion, admission edges and allocation"
  let workspaces ← continuationWorkspaces
  if workspaces == 0 then throw (IO.userError "native continuation workspace unused")
  IO.println s!"native continuation workspaces: {workspaces}"
  let validations ← continuationValidations
  if validations == 0 then throw (IO.userError "native continuation validation unused")
  IO.println s!"native continuation validations: {validations}"
  let phases ← continuationPhases
  if phases.1 == 0 || phases.2.1 == 0 || phases.2.2 == 0 then
    throw (IO.userError "native continuation fast phases unused")
  IO.println s!"native continuation calls: {continuationCalls}; fast input/scan/gather: {phases}"
  let bounds ← continuationBounds
  if bounds.1 == 0 || bounds.2.1 == 0 || bounds.2.1 > 1048576 || bounds.2.2 != 0 then
    throw (IO.userError "native continuation phase bound violated")
  IO.println s!"native continuation loop count/declared product/schedule errors: {bounds}"
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
  let beforeF4Deferrals ← batchDeferrals
  let beforeF4Batches ← batchCounts
  let beforeF4Primitives ← primitiveAdmissions
  resetContinuationBounds
  let beforeF4Continuation ← continuationCount
  let beforeF4Validations ← continuationValidations
  let beforeF4Workspaces ← continuationWorkspaces
  let beforeF4Phases ← continuationPhases
  Hex.Groebner.NativeChecks.runF4
  let beforeOversizedSuccess ← continuationSuccesses
  let beforeOversizedArithmetic ← continuationArithmetic
  let beforeOversizedWhole ← wholeCounts
  Hex.Groebner.NativeChecks.runOversizedF4
  let afterOversizedSuccess ← continuationSuccesses
  let afterOversizedArithmetic ← continuationArithmetic
  let afterOversizedWhole ← wholeCounts
  if afterOversizedSuccess ≤ beforeOversizedSuccess || afterOversizedWhole.2 ≤ beforeOversizedWhole.2 then
    throw (IO.userError "successful oversized F4 did not complete a deferred native continuation")
  if afterOversizedArithmetic.1 ≤ beforeOversizedArithmetic.1 ||
      afterOversizedArithmetic.2.1 ≤ beforeOversizedArithmetic.2.1 ||
      afterOversizedArithmetic.2.2 ≤ beforeOversizedArithmetic.2.2 then
    throw (IO.userError "oversized F4 did not exercise successful reductions, zero rows and non-unit inverses")
  IO.println s!"oversized F4 reduced/zero successes/non-unit inverses: {afterOversizedArithmetic.1-beforeOversizedArithmetic.1}/{afterOversizedArithmetic.2.1-beforeOversizedArithmetic.2.1}/{afterOversizedArithmetic.2.2-beforeOversizedArithmetic.2.2}"
  IO.println s!"oversized F4 successful continuations/bulk deferrals: {afterOversizedSuccess-beforeOversizedSuccess}/{afterOversizedWhole.2-beforeOversizedWhole.2}"
  let afterF4Deferrals ← batchDeferrals
  if afterF4Deferrals.2.2 != 0 then throw (IO.userError "batch visit cap exceeded")
  IO.println s!"F4 deferred batches/discarded visit reservations: {afterF4Deferrals.1-beforeF4Deferrals.1}/{afterF4Deferrals.2.1-beforeF4Deferrals.2.1}"
  let afterF4Batches ← batchCounts
  if afterF4Batches.1 ≤ beforeF4Batches.1 || afterF4Batches.2 ≤ beforeF4Batches.2 then
    throw (IO.userError "F4 did not exercise accepted monomial batches")
  IO.println s!"F4 monomial batches/terms: {afterF4Batches.1-beforeF4Batches.1}/{afterF4Batches.2-beforeF4Batches.2}"
  let afterF4Primitives ← primitiveAdmissions
  -- All F4-window matrices fit the continuation scheduler's geometry. Larger
  -- production frames legitimately retain the reference's native primitives.
  if afterF4Primitives != beforeF4Primitives then
    throw (IO.userError "bounded-shape F4 window used deselected standalone matrix primitives")
  IO.println s!"F4 primitive validation admitted/declined: {afterF4Primitives.1.1-beforeF4Primitives.1.1}/{afterF4Primitives.1.2-beforeF4Primitives.1.2}; zero admitted/declined: {afterF4Primitives.2.1-beforeF4Primitives.2.1}/{afterF4Primitives.2.2-beforeF4Primitives.2.2}"
  let afterF4Continuation ← continuationCount
  let afterF4Validations ← continuationValidations
  let afterF4Workspaces ← continuationWorkspaces
  let afterF4Phases ← continuationPhases
  if afterF4Continuation ≤ beforeF4Continuation || afterF4Validations ≤ beforeF4Validations ||
      afterF4Workspaces ≤ beforeF4Workspaces then
    throw (IO.userError "F4 did not exercise native continuation validation and workspace setup")
  if afterF4Phases.1 ≤ beforeF4Phases.1 || afterF4Phases.2.1 ≤ beforeF4Phases.2.1 ||
      afterF4Phases.2.2 ≤ beforeF4Phases.2.2 then
    throw (IO.userError "F4 did not exercise native continuation input, scan and gather")
  -- These counters check the configured phase-loop cap, not measured machine
  -- instructions, allocation volume or elapsed time inside each phase.
  let f4Bounds ← continuationBounds
  if f4Bounds.1 == 0 || f4Bounds.2.1 == 0 || f4Bounds.2.1 > 1048576 || f4Bounds.2.2 != 0 then
    throw (IO.userError "F4 native continuation configured loop cap violated")
  IO.println s!"F4 continuation calls/validation/workspace: {afterF4Continuation-beforeF4Continuation}/{afterF4Validations-beforeF4Validations}/{afterF4Workspaces-beforeF4Workspaces}; input/scan/gather: {afterF4Phases.1-beforeF4Phases.1}/{afterF4Phases.2.1-beforeF4Phases.2.1}/{afterF4Phases.2.2-beforeF4Phases.2.2}"
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
  let mersenne ← checkMersenne
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
  if VECTOR && available && (contiguous == 0 || gathered == 0 || covered != 255) then
    throw (IO.userError "an AVX2 path was not exercised")
  if VECTOR && (← IO.getEnv "HEX_GROEBNER_REQUIRE_AVX2") == some "1" && !available then
    throw (IO.userError "AVX2 coverage required but unavailable")
  resetPivotOwners
  let ownerSeed ← Hex.Groebner.NativeChecks.readSeed
  let ownerRows := 256+ownerSeed%2
  if !Hex.Groebner.SamplingChecks.grow ownerRows then
    throw (IO.userError "fresh sampling pivot growth failed")
  let (pushes,shared,entries) ← pivotOwners
  if pushes != ownerRows.toUInt64 || entries != 0 then
    throw (IO.userError s!"sampling copied shared pivot metadata: {pushes}/{shared}/{entries}")
  IO.println s!"sampling pivot pushes={pushes}, shared={shared}, existing shared entries={entries}"
  resetPivotOwners
  if !Hex.Groebner.SamplingChecks.growTargets ownerRows then
    throw (IO.userError "fresh sampled target pivot growth failed")
  let (pushes,shared,entries) ← pivotOwners
  if pushes != ownerRows.toUInt64 || entries != 0 then
    throw (IO.userError s!"sampling copied shared target pivot metadata: {pushes}/{shared}/{entries}")
  IO.println s!"sampling target pivot pushes={pushes}, shared={shared}, existing shared entries={entries}"
  resetPivotOwners
  let freshSeed ← Hex.Groebner.NativeChecks.readSeed
  let some digest := Hex.Groebner.SampledConformance.fresh freshSeed |
    throw (IO.userError "fresh sampled F4 failed")
  IO.println s!"fresh sampled F4 digest={digest}"
  let (pushes,shared,entries) ← pivotOwners
  if pushes == 0 || entries != 0 then
    throw (IO.userError s!"sampled F4 copied shared pivot metadata: {pushes}/{shared}/{entries}")
  IO.println s!"sampled F4 pivot pushes={pushes}, shared={shared}, existing shared entries={entries}"
  for kind in [:4] do
    let some (ready,held) := Hex.Groebner.SamplingChecks.snapshot kind |
      throw (IO.userError s!"missing sampling snapshot {kind}")
    let before ← copyBytes held
    -- Read after the first observation: the pure transition depends on this IO
    -- value and cannot move ahead of the first byte copy. Stay below its cap.
    let snapshotSeed ← Hex.Groebner.NativeChecks.readSeed
    let completed := Hex.Groebner.Sampling.advance
      { work := 10000000,packedBytes := 10000000 } (63-snapshotSeed%2) ready
    if completed.failure.isSome || completed.phase != .done then
      throw (IO.userError s!"sampling snapshot {kind} did not complete")
    let after ← copyBytes held
    if before.data != after.data then
      throw (IO.userError s!"sampling snapshot {kind} was mutated")
  IO.println "sampling snapshots: 4 IO byte comparisons"
  let beforeSubtract ← subtractCount
  let (beforeScan,beforeGather) ← counts
  Hex.Groebner.SampledConformance.run
  let afterSubtract ← subtractCount
  let (afterScan,afterGather) ← counts
  if afterSubtract ≤ beforeSubtract || afterScan ≤ beforeScan || afterGather ≤ beforeGather then
    throw (IO.userError "sampled F4 did not exercise instrumented combination/scan/gather")
  IO.println s!"sampled native calls: subtract={afterSubtract-beforeSubtract}, scan={afterScan-beforeScan}, gather={afterGather-beforeGather}"
'''.replace("VECTOR", "false" if variant.startswith("Scalar") else "true").replace("WIDE", "true" if variant in ("Native", "Remainder") else "false"))
            if profile != "regular":
                (directory / (module + ".lean")).write_text(profile_main(profile))
            extra = extra + defines
            variant_flags[variant] = flags + extra
            config += f'''\ntarget probe{variant} pkg : FilePath := probeO pkg "{variant}" #{json.dumps(flags + extra)}
lean_exe {target} where
  root := `{module}
  moreLinkObjs := #[probe{variant}]
  moreLinkArgs := #{json.dumps(link_args)}
'''
        usage_inputs = os.environ.get("HEX_GROEBNER_USAGE_INPUT_DIR") if profile == "regular" else None
        if usage_inputs:
            (directory / "Usage.lean").write_text('''import HexGroebner.Driver.Run
@[extern "hex_test_dense_counts"] opaque denseCounts : IO (UInt64 × UInt64 × UInt64)
@[extern "hex_test_dense_admitted"] opaque denseAdmitted : IO UInt64
@[extern "hex_test_whole_counts"] opaque wholeCounts : IO (UInt64 × UInt64)
@[extern "hex_test_delayed_refused"] opaque delayedRefusedWork : IO UInt64
@[extern "hex_test_avx512_count"] opaque avx512Count : IO UInt64
def main (args : List String) : IO UInt32 := do
  let status ← Hex.Groebner.Driver.run args
  let (prepares,scans,updates) ← denseCounts
  let packets ← avx512Count
  let admitted ← denseAdmitted
  let (accepted,declined) ← wholeCounts
  let refusedWork ← delayedRefusedWork
  (← IO.getStderr).putStrLn (Lean.Json.mkObj [
    ("avx512Packets",Lean.toJson packets),("prepares",Lean.toJson prepares),("admitted",Lean.toJson admitted),
    ("scans",Lean.toJson scans),("updates",Lean.toJson updates),
    ("delayedRefusedWork",Lean.toJson refusedWork),
    ("bulkAccepted",Lean.toJson accepted),("bulkDeclined",Lean.toJson declined)]).compress
  return status
''')
            config += f'''\nlean_exe usage where
  root := `Usage
  moreLinkObjs := #[probeNative]
  moreLinkArgs := #{json.dumps(link_args)}
'''
        (directory / "profile.json").write_text(json.dumps(dict(profile=profile,
            variants=names,defines=defines,sanitize=sanitize),indent=2)+"\n")
        (directory / "lakefile.lean").write_text(config)
        compiler_version = subprocess.check_output([cc, "--version"], text=True)
        print("matrix variants compiler:", compiler_version.splitlines()[0], flush=True)
        generated = ["lakefile.lean", "probe.c", *("Check"+name+".lean" for name in names)]
        if usage_inputs: generated.append("Usage.lean")
        generated_sha256 = {name: hashlib.sha256((directory/name).read_bytes()).hexdigest()
                            for name in generated}
        build = subprocess.run(["lake", "build", *targets, *(["usage"] if usage_inputs else [])], cwd=directory)
        status = dict(profile=profile, variants=names, defines=defines, sanitize=sanitize,
                      compiler=cc, compiler_version=compiler_version, variant_flags=variant_flags,
                      generated_sha256=generated_sha256,
                      build_exit_code=build.returncode, results=[], **identity)
        status_path = directory / "profile-status.json"
        status_path.write_text(json.dumps(status, indent=2)+"\n")
        build.check_returncode()
        env = dict(os.environ, ASAN_OPTIONS=os.environ.get("ASAN_OPTIONS", "detect_leaks=0"),
                   UBSAN_OPTIONS=os.environ.get("UBSAN_OPTIONS", "halt_on_error=1"),
                   LEAN_ABORT_ON_NONLINEAR="1")
        loader = os.environ.get("HEX_GROEBNER_TEST_LOADER")
        results = []
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
            result = subprocess.run(command, env=env)
            results.append(dict(variant=target.removeprefix("check"),exit_code=result.returncode))
            assert source_identity() == identity
            status["results"] = results
            status_path.write_text(json.dumps(status, indent=2)+"\n")
            result.check_returncode()
        if usage_inputs:
            output = directory / "usage-results"
            output.mkdir(exist_ok=False)
            for input_path in sorted(Path(usage_inputs).glob("*.json")):
                if input_path.name == "suite.json":
                    continue
                for enabled in ["false", "true"]:
                    usage_command = [str(directory / ".lake/build/bin/usage"),
                                     "--work", "100000000000", "--packed-bytes", "17179869184",
                                     "--pairs", "100000000", "--monomials", "10000000",
                                     "--matrix-entries", "1000000000",
                                     "--scheduling", "degree", "--dense-pivots", enabled, str(input_path)]
                    if loader:
                        usage_command = [loader, "--library-path", library_path,
                                         "--preload", os.pathsep.join(preload), *usage_command]
                    with (output / (input_path.stem+"-"+enabled+".stdout")).open("w") as out, \
                            (output / (input_path.stem+"-"+enabled+".stderr")).open("w") as err:
                        subprocess.run(usage_command, stdout=out, stderr=err, env=env, check=True)
                    (output / (input_path.stem+"-"+enabled+".command.json")).write_text(
                        json.dumps(usage_command, indent=2)+"\n")
        print(f"compiled matrix variants: {time.monotonic()-started:.2f}s elapsed", flush=True)
    finally:
        if not retained:
            shutil.rmtree(directory)


if __name__ == "__main__":
    run()
