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
#define lean_hex_groebner_prepare_monomial hex_test_unused_prepare
#define lean_hex_groebner_equal_monomial hex_test_unused_monomial_equal
#define lean_hex_groebner_equal_bytes hex_test_equal_bytes
#define lean_hex_groebner_equal_products hex_test_equal_products
#define lean_hex_groebner_compare_monomials hex_test_compare
#include ROW_SOURCE
#undef lean_hex_groebner_compare_monomials
#undef lean_hex_groebner_subtract_row
#undef lean_hex_groebner_prepare_monomial
#undef lean_hex_groebner_equal_monomial
#undef lean_hex_groebner_equal_bytes
#undef lean_hex_groebner_equal_products
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
static uint64_t scan_calls=0,gather_calls=0,byte_calls=0,product_calls=0;
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
'''.replace("ROW_SOURCE", json.dumps(str(ROOT / "HexGroebner/ffi/row_update.c"))).replace("SOURCE", json.dumps(str(source))).replace("HEADER", json.dumps(str(source.parent / "matrix_simd.h"))))
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
  let inputs := ((source.zipWith (fun s _ => s) scan).zipWith (fun s _ => s) simd).zipWith (fun s _ => s) body
  let inputs := inputs.zipWith (fun s _ => s) row
  buildO (pkg.dir / defaultBuildDir / (name ++ ".o")) inputs
    #["-isystem", (← getLeanIncludeDir).toString] flags
    (compiler := FilePath.mk COMPILER)
    (extraDepTrace := do addPureTrace COMPILER "compiler"; pure BuildTrace.nil)
'''.replace("ROOT", json.dumps(str(ROOT))).replace("SCAN", json.dumps(str(source))).replace(
            "SIMD", json.dumps(str(source.parent / "matrix_simd.h"))).replace(
            "BODY", json.dumps(str(source.parent / "matrix_scan_impl.h"))).replace(
            "ROW", json.dumps(str(source.parent / "row_update.c"))).replace("COMPILER", json.dumps(cc))
        flags = ["-O3", "-g", "-Wall", "-Wextra", "-Werror", "-fPIC", "-DLEAN_EXPORTING"]
        if sanitize:
            flags += ["-fsanitize=address,undefined", "-fno-sanitize-recover=undefined", "-fno-omit-frame-pointer"]
        link_args = ["-Wl,--wrap=lean_hex_scan_transition", "-Wl,--wrap=lean_hex_gather",
                     "-Wl,--wrap=lean_hex_groebner_equal_bytes",
                     "-Wl,--wrap=lean_hex_groebner_equal_products",
                     "-Wl,--wrap=lean_hex_groebner_compare_monomials"] + libraries
        targets = []
        for variant, extra in VARIANTS.items():
            module = "Check" + variant
            target = "check" + variant
            targets.append(target)
            (directory / (module + ".lean")).write_text('''import HexGroebner.NativeChecks
@[extern "hex_test_comparison_count"] opaque comparisonCount : IO UInt64
@[extern "hex_test_comparison_declines"] opaque comparisonDeclines : IO UInt64
@[extern "hex_test_counts"] opaque counts : IO (UInt64 × UInt64)
@[extern "hex_test_byte_count"] opaque byteCount : IO UInt64
@[extern "hex_test_product_count"] opaque productCount : IO UInt64
@[extern "hex_test_vector_counts"] opaque vectorCounts : IO (UInt64 × UInt64)
@[extern "hex_test_avx2"] opaque avx2 : IO Bool
@[extern "hex_test_widths"] opaque widths : IO UInt32
@[extern "hex_test_zero_count"] opaque zeroCount : IO UInt64
@[extern "hex_test_mersenne_count"] opaque mersenneCount : IO UInt64
def main : IO Unit := do
  Hex.Groebner.NativeChecks.run
  let primitiveCompared ← byteCount
  let primitiveProducts ← productCount
  let beforeZero ← zeroCount
  let comparedBefore ← comparisonCount
  let declinedBefore ← comparisonDeclines
  Hex.Groebner.NativeChecks.runF4
  let afterZero ← zeroCount
  let comparedAfter ← comparisonCount
  let declinedAfter ← comparisonDeclines
  let accepted := (comparedAfter-comparedBefore)-(declinedAfter-declinedBefore)
  if accepted == 0 || declinedAfter != declinedBefore then
    throw (IO.userError "F4 did not obtain bounded native comparison answers")
  IO.println s!"native monomial calls: {comparedAfter}, declines: {declinedAfter}; F4 accepted: {accepted}, F4 declines: {declinedAfter-declinedBefore}"
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
                   UBSAN_OPTIONS=os.environ.get("UBSAN_OPTIONS", "halt_on_error=1"))
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
