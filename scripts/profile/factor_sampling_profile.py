#!/usr/bin/env python3
"""Symbolized sampling profiles of `hexbz_factor_service` on named corpus rows.

`SPEC/profiling.md` fixes the tooling (samply, its symbolication data, Lean name
demangling) and the required output: a leaf-cost categorisation across Lean own
code / GMP / allocation / Lean runtime, and an inclusive-cost ranking. Raw
`*.json.gz` profiles are not committed; this script writes the analytical
summary that is.

Each profiled instance is replayed through the warm service enough times to
collect a useful sample count, with `--rate 999` sampling and the service pinned
to one core. Only the service's main thread is retained; the samply supervisor,
the io_uring helpers, and the pre-`main` startup samples are dropped.

Run::

    lake build hexbz_factor_service
    python3 scripts/profile/factor_sampling_profile.py \\
        --output reports/bench-results/hexbz-factor-sampling-profiles.json
"""

from __future__ import annotations

import argparse
import bisect
import collections
import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
HEX_SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"
BENCH_RESULTS = ROOT / "reports" / "bench-results"

# The instances issue #9127 requires a symbolized profile for.
PROFILED = [
    # Required by issue #9127.
    "sd5", "sd5_x_phi11", "xpow120_minus1", "cyclo_phi179",
    "cyclo_phi64_x_phi105", "cyclo_phi385", "wilkinson_56",
    # Added: #9130's exact-division evidence names these two rows, and the
    # phase table alone cannot separate division from candidate construction.
    "xpow48_minus1", "xpow105_minus1",
]

# Inclusive-share floor for the per-function Hex table. Low enough that a phase
# worth attributing is never dropped, high enough to keep the record readable.
INCLUSIVE_FLOOR_PERCENT = 0.5

DEFAULT_TARGET_SECONDS = 6.0
DEFAULT_RATE = 999
DEFAULT_CPU = 0


# ---------------------------------------------------------------- demangling

def demangle(symbol: str) -> str:
    """Invert `String.Internal.mangle` for symbols Lean's compiler emitted.

    Lean mangles each name component with alphanumerics kept, `_` doubled, and
    any other character as `_xHH` / `_uHHHH` / `_UHHHHHHHH`; components are
    joined with a single `_`. Compiled Lean symbols carry an `l_` prefix, or
    `lp_<package>_` when the module was precompiled into a shared library. C
    symbols from the runtime, libc, and GMP are left alone -- rewriting their
    underscores would turn `_int_free_chunk` into a plausible-looking Lean name.
    """
    for prefix in ("_init_l_", "initialize_", "lp_Hex_", "lp_", "l_"):
        if symbol.startswith(prefix):
            core = symbol[len(prefix):]
            break
    else:
        return symbol
    out, i = [], 0
    n = len(core)
    while i < n:
        ch = core[i]
        if ch != "_":
            out.append(ch)
            i += 1
            continue
        if core.startswith("__", i):
            out.append("_")
            i += 2
            continue
        for marker, width in (("_x", 2), ("_u", 4), ("_U", 8)):
            if core.startswith(marker, i) and i + 2 + width <= n:
                digits = core[i + 2:i + 2 + width]
                if all(d in "0123456789abcdef" for d in digits):
                    out.append(chr(int(digits, 16)))
                    i += 2 + width
                    break
        else:
            out.append(".")
            i += 1
    return "".join(out) or symbol


_SPEC_SUFFIX = re.compile(
    r"(?:_\.redArg|_\.boxed|_\.lam_\d+|_\.elam_\d+|_\.jp_\d+|_\.cold"
    r"|\.spec_\d+|_\.spec_\d+|_\.lam_\d+_\.boxed)$")


def simplify(name: str) -> str:
    """Fold Lean's specialization and join-point decorations into one name.

    The compiler emits a distinct symbol per specialization site, so
    `Hex.Matrix.rowAdd` appears under several mangled names that all denote the
    same source function. Folding them before counting is what makes an
    inclusive share readable: the specialization *context* is still visible in
    the enclosing entries of the inclusive table.
    """
    head = name.split("_.at_.", 1)[0]
    previous = None
    while previous != head:
        previous = head
        head = _SPEC_SUFFIX.sub("", head)
    return head or name


# ------------------------------------------------------------ categorisation

# SPEC/profiling.md fixes these four leaf-cost categories. Order matters: the
# allocator check runs before the generic `lean_` runtime check so that Lean's
# own allocation entry points land in the allocation budget.
_GMP = ("gmpn_", "gmpz_", "gmpq_", "gmp_")
_ALLOC = (
    "malloc", "free", "realloc", "calloc", "mi_", "memset", "memmove",
    "memcpy", "arena_", "tcache", "unlink_chunk", "malloc_consolidate",
    "lean_alloc", "lean_free", "lean_dealloc", "sysmalloc", "brk", "mmap",
)


def _normalise(name: str) -> str:
    base = name.lstrip("_")
    for prefix in ("GI___", "GI__", "GI_"):
        if base.startswith(prefix):
            base = base[len(prefix):].lstrip("_")
    for marker in (".isra.", ".part.", ".constprop.", ".cold"):
        index = base.find(marker)
        if index >= 0:
            base = base[:index]
    return base


def categorise(name: str) -> str:
    if name.startswith("Hex"):
        return "lean-own-code"
    base = _normalise(name)
    if any(token in base for token in _GMP):
        return "gmp"
    if any(base.startswith(token) or ("_" + token) in base for token in _ALLOC):
        return "allocation"
    if base.startswith("lean_") or base.startswith("Lean."):
        return "lean-runtime"
    # Compiled Lean standard-library code: not this library's own code, but not
    # runtime plumbing either. SPEC/profiling.md's runtime bucket is the closest
    # fit, and the inclusive ranking keeps the two visibly separate.
    if base.split(".")[0] in {"Array", "List", "Nat", "Int", "Option", "String",
                              "Vector", "Fin", "Prod", "UInt64", "Subarray"}:
        return "lean-runtime"
    return "other"


# ------------------------------------------------------------ symbolication

class Symbolicator:
    """Resolve relative addresses through samply's presymbolicated sidecar."""

    def __init__(self, syms_path: Path):
        data = json.loads(syms_path.read_text())
        strings = data["string_table"]
        self.tables = {}
        for entry in data["data"]:
            table = entry.get("symbol_table") or []
            rvas = [row["rva"] for row in table]
            names = [strings[row["symbol"]] for row in table]
            self.tables[entry["debug_name"]] = (rvas, names)

    def resolve(self, lib_name: str, address: int) -> "str | None":
        table = self.tables.get(lib_name)
        if table is None:
            return None
        rvas, names = table
        index = bisect.bisect_right(rvas, address) - 1
        return names[index] if index >= 0 else None


def main_thread(profile: dict) -> dict:
    threads = [t for t in profile["threads"]
               if t["name"] == "hexbz_factor_service"]
    if not threads:
        raise SystemExit("no hexbz_factor_service thread in the profile")
    return max(threads, key=lambda t: t["samples"]["length"])


def frame_names(profile: dict, thread: dict, symbolicator: Symbolicator):
    """Symbolized, demangled name for every frame index of `thread`."""
    strings = thread["stringArray"]
    funcs = thread["funcTable"]
    resources = thread["resourceTable"]
    libs = profile["libs"]
    lib_of_resource = []
    for index in range(resources["length"]):
        lib_index = resources.get("lib", [None] * resources["length"])[index]
        lib_of_resource.append(
            libs[lib_index]["debugName"] if lib_index is not None else None)
    frames = profile and thread["frameTable"]
    out = []
    for frame in range(frames["length"]):
        func = frames["func"][frame]
        raw = strings[funcs["name"][func]]
        address = frames["address"][frame]
        resource = funcs["resource"][func]
        lib = lib_of_resource[resource] if 0 <= resource < len(lib_of_resource) else None
        symbol = None
        if lib is not None and address is not None and address >= 0:
            symbol = symbolicator.resolve(lib, address)
        name = demangle(symbol) if symbol else raw
        out.append((simplify(name), name))
    return out


def stack_chain(thread: dict, stack: int):
    """Frame indices from leaf to root for one stack index."""
    table = thread["stackTable"]
    chain = []
    while stack is not None:
        chain.append(table["frame"][stack])
        stack = table["prefix"][stack]
    return chain


def analyse(profile: dict, symbolicator: Symbolicator, top: int) -> dict:
    thread = main_thread(profile)
    resolved = frame_names(profile, thread, symbolicator)
    names = [short for short, _ in resolved]
    raw_names = [full for _, full in resolved]
    samples = thread["samples"]
    self_raw_counts = collections.Counter()
    self_counts = collections.Counter()
    inclusive_counts = collections.Counter()
    category_counts = collections.Counter()
    total = 0
    for index in range(samples["length"]):
        stack = samples["stack"][index]
        if stack is None:
            continue
        chain = stack_chain(thread, stack)
        if not chain:
            continue
        total += 1
        leaf = names[chain[0]]
        self_counts[leaf] += 1
        self_raw_counts[raw_names[chain[0]]] += 1
        category_counts[categorise(leaf)] += 1
        # Dedupe by *name*, not by frame index: a recursive function occupies
        # several frames of one stack but is only on that stack once.
        for name in {names[frame] for frame in chain}:
            inclusive_counts[name] += 1
    if total == 0:
        raise SystemExit("profile retained no samples")

    def share(count):
        return round(100.0 * count / total, 2)

    # Every Hex function with a material inclusive share, not just the top few:
    # the dependent issues each need the share of a different phase, and a
    # fixed cut would silently drop the one they ask about.
    own = [(name, count) for name, count in inclusive_counts.items()
           if categorise(name) == "lean-own-code"
           and 100.0 * count / total >= INCLUSIVE_FLOOR_PERCENT]
    own.sort(key=lambda row: -row[1])
    return {
        "samples": total,
        "leaf_categories": {
            category: share(count)
            for category, count in sorted(category_counts.items(),
                                          key=lambda row: -row[1])
        },
        "classified_percent": share(
            total - category_counts.get("other", 0)),
        "top_self": [{"function": name, "percent": share(count)}
                     for name, count in self_counts.most_common(top)],
        "top_self_undecorated": [
            {"symbol": name, "percent": share(count)}
            for name, count in self_raw_counts.most_common(top)],
        "top_inclusive": [{"function": name, "percent": share(count)}
                          for name, count in inclusive_counts.most_common(top)],
        "inclusive_hex": [{"function": name, "percent": share(count)}
                          for name, count in own],
        "allocation_share_percent": share(category_counts.get("allocation", 0)),
    }


# ------------------------------------------------------------------- capture

def capture(instance: dict, workdir: Path, rate: int, cpu: int,
            target_seconds: float, entry: str) -> "tuple[dict, Path]":
    """Record one profile, returning (parsed profile, syms sidecar path)."""
    request = json.dumps({"coeffs": instance["coeffs"]},
                         separators=(",", ":")) + "\n"
    # One calibration call, so the replay count lands near the sample target.
    calibrate = subprocess.run(
        [str(HEX_SERVICE), "--entry", entry], input=request,
        capture_output=True, text=True, timeout=600)
    if calibrate.returncode != 0:
        raise SystemExit(f"service failed on {instance['name']}")
    per_call = None
    probe = subprocess.run(
        [str(HEX_SERVICE), "--entry", "factorPhaseProfile"], input=request,
        capture_output=True, text=True, timeout=600)
    if probe.returncode == 0:
        reply = json.loads(probe.stdout.splitlines()[-1])
        if reply.get("ok") and reply.get("result"):
            per_call = reply["result"]["phases"]["total"]["nanos"] / 1e9
    repeats = 1 if not per_call else max(1, int(target_seconds / per_call))
    requests = workdir / f"{instance['name']}.jsonl"
    requests.write_text(request * repeats)
    out = workdir / f"{instance['name']}.json.gz"
    argv = ["samply", "record", "--save-only", "--rate", str(rate),
            "--unstable-presymbolicate", "-o", str(out), "--",
            "taskset", "-c", str(cpu), str(HEX_SERVICE), "--entry", entry]
    with requests.open() as stdin, open("/dev/null", "w") as devnull:
        subprocess.run(argv, stdin=stdin, stdout=devnull,
                       stderr=subprocess.DEVNULL, check=True, timeout=3600)
    with gzip.open(out) as handle:
        profile = json.load(handle)
    return profile, out.with_suffix("").with_suffix(".json.syms.json"), repeats


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--names", default=None,
                   help="comma-separated corpus instances (default: the issue "
                        "#9127 profile set)")
    p.add_argument("--entry", default="factor",
                   help="service entry to profile (default: the production "
                        "`factor` cascade)")
    p.add_argument("--rate", type=int, default=DEFAULT_RATE)
    p.add_argument("--cpu", type=int, default=DEFAULT_CPU)
    p.add_argument("--target-seconds", type=float, default=DEFAULT_TARGET_SECONDS)
    p.add_argument("--top", type=int, default=15)
    p.add_argument("--output", type=Path, default=None)
    args = p.parse_args()

    if shutil.which("samply") is None:
        raise SystemExit("samply is not on PATH; see SPEC/profiling.md")
    if not HEX_SERVICE.exists():
        raise SystemExit("run `lake build hexbz_factor_service` first")

    corpus = {}
    for line in CORPUS_PATH.read_text().splitlines():
        if line.strip():
            record = json.loads(line)
            corpus[record["name"]] = record
    names = ([n.strip() for n in args.names.split(",") if n.strip()]
             if args.names else PROFILED)

    profiles = []
    with tempfile.TemporaryDirectory(prefix="hexbz-profile-") as tmp:
        workdir = Path(tmp)
        for name in names:
            print(f"profiling {name}", file=sys.stderr)
            profile, syms, repeats = capture(
                corpus[name], workdir, args.rate, args.cpu,
                args.target_seconds, args.entry)
            summary = analyse(profile, Symbolicator(syms), args.top)
            profiles.append({
                "name": name,
                "family": corpus[name]["family"],
                "degree": corpus[name]["degree"],
                "repeats": repeats,
                **summary,
            })

    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                            capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(ROOT), "status", "--porcelain"],
                           capture_output=True, text=True).stdout.strip()
    record = {
        "schema": "hexbz-sampling-profiles/1",
        "config": {
            "entry": args.entry,
            "rate_hz": args.rate,
            "cpu": args.cpu,
            "target_seconds": args.target_seconds,
            "samply_version": subprocess.run(
                ["samply", "--version"], capture_output=True,
                text=True).stdout.strip(),
            "git_commit": commit or None,
            "git_dirty": bool(dirty),
        },
        "profiles": profiles,
    }
    out = args.output or (BENCH_RESULTS / "hexbz-factor-sampling-profiles.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"wrote {out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
