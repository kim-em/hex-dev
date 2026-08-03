#!/usr/bin/env python3
"""Phase-attributed factorization diagnostic sweep (issues #9127, #9128).

Drives the `factorPhaseProfile`, `primeCounterfactual`, `primeScout`,
`factorTrace`, and `factor` entries of `hexbz_factor_service` over a named
subset of the committed corpus and writes one durable JSON record.

The record answers four separate questions and keeps them separate:

* **Phase attribution.** `factorPhaseProfile` decomposes one production
  factorization into the production functions it calls, in production order,
  and times each. Its counters and its times come from that one execution.
* **Counterfactual prime plans.** `primeCounterfactual` replays the downstream
  lift and recombination for every good prime in a fixed comparison set, so the
  cost of having stopped at each candidate is measurable. Only the row marked
  `selected` is work the production cascade actually did.
* **Scout prices.** `primeScout` prices, at every good prime in a bounded
  prefix of the candidate list, the four ways of learning that prime's modular
  degree pattern: the bounded scout the planner runs, the complete degree
  pattern, the Berlekamp matrix with its kernel, and a full Berlekamp split. It
  also checks the scouted pattern against the split. This is the evidence the
  prime-planning policy is chosen from; none of it is work the production
  cascade does.

Every cost in the plan sections is one observation per call, so both are
repeated and merged into one plan by per-candidate median (`--plan-repeats`).
Everything else the service reports is deterministic, and the merge asserts
that the repeats agree on all of it before replacing the durations.
* **Kernel attribution.** `kernelProfile` decomposes the Berlekamp fixed-space
  kernel at the production-selected prime into the stages issue #9132 names --
  column construction, conversion to the generic matrix representation, pivot
  search, row swap/scale/add, rank and nullspace-basis construction, and the
  conversion of basis vectors back to polynomials -- and prices three packed
  contiguous representations against it. Each packed result is checked entry
  for entry against `Hex.Matrix.nullspace` before its time is reported, and the
  counted Gauss-Jordan mirror is checked against the production `rowReduce`.
  Like the scout prices, none of this is work the production cascade does.
* **Validation.** Cross-checks run alongside, on a wider sample than the
  representative set: the counted recombination mirror must agree with the
  production `factorTrace` on leaf count, selected prime, completed subset
  cardinalities, and the factor-degree multiset it returns, and the profile
  total must track the untimed end-to-end `factor` call.

This is a diagnostic driver run manually on dedicated hardware, not a CI job
and not a hex-internal benchmark harness, so the one-harness rule stays intact
(see SPEC/benchmarking.md addendum).

The driver pins itself to one core before spawning any service, so every
measured descendant inherits that affinity. `--cpu auto` (the default) picks a
core that is currently idle on itself and on its SMT siblings, because several
of these drivers may run at once on a shared host; pinning them all to a fixed
core makes each measure the others. See `scripts/bench/idle_core.py`.

Example::

    lake build hexbz_factor_service
    python3 scripts/bench/factor_phase_profile.py \\
        --output reports/bench-results/hexbz-phase-profile.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import statistics
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

import idle_core  # noqa: E402

from factor_sweep import (  # noqa: E402
    CORPUS_PATH,
    HEX_SERVICE,
    ROOT,
    Service,
    env_block,
    load_corpus,
)

BENCH_RESULTS = ROOT / "reports" / "bench-results"

# The elbow set named by issue #9127: the instances that populate solved ranks
# 125--140 of the combined cactus, plus the controls that bracket them.
REPRESENTATIVE = [
    "sd5", "sd5_shift1", "sd5_shift2", "sd4_x_sd4shift1", "sd5_x_phi11",
    "xpow48_minus1", "xpow105_minus1", "xpow120_minus1",
    "cyclo_phi179", "cyclo_phi64_x_phi105", "cyclo_phi128_x_phi165",
    "cyclo_phi385",
    "wilkinson_40", "wilkinson_48", "wilkinson_56",
]

# Controls: cheap shapes from the families the elbow set does not touch, so a
# phase share measured on the elbow can be read against a non-elbow baseline.
CONTROLS = [
    "chebyshev_T24", "chebyshev_U24", "legendre_P30", "legendre_P38",
    "cyclo_phi17", "cyclo_phi41", "xpow24_minus1",
    "randprod_10", "randprod_21",
]

# Instances whose symbolized sampling profile the report carries.
PROFILED = [
    "sd5", "sd5_x_phi11", "xpow120_minus1", "cyclo_phi179",
    "cyclo_phi64_x_phi105", "cyclo_phi385", "wilkinson_56",
]

DEFAULT_CUTOFF = 120.0
DEFAULT_PLAN_REPEATS = 3
DEFAULT_KERNEL_REPEATS = 3
# Nanosecond fields of the kernel record merged by median across repeats. Every
# other field is deterministic and is asserted to agree before the merge.
KERNEL_SPAN_KEYS = (
    "frobeniusPower", "columnPolys", "berlekampMatrixWall",
    "fixedSpaceMatrixWall", "matrixRebuild", "productionRowReduce",
    "rowReduceMatrixRebuild", "productionMatrixRebuild", "productionNullspace",
    "basisToPolynomials", "fixedSpaceKernelVectors", "berlekampSplit")
KERNEL_COUNTED_KEYS = ("countedWithTransform", "countedEchelonOnly")
KERNEL_PACKED_KEYS = ("packedWord", "packedHalfWord",
                      "packedHalfWordDivision", "packedHalfWordSkipZero")
# Per-candidate costs merged by median across `--plan-repeats` calls.
PLAN_NANO_KEYS = ("goodPrimeTest", "boundedScout", "scout", "berlekampMatrix",
                  "rowReduction", "fullSplit", "henselLift", "recombination")
DEFAULT_WARMUP = 1
DEFAULT_REPEATS = 5
# Above this first-call wall time a repeat sweep costs more than it buys, so the
# instance is measured once (the same rule the cross-system sweep uses).
REPEAT_CEILING_NANOS = 1_000_000_000


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def service_argv(entry: str):
    if not HEX_SERVICE.exists():
        raise SystemExit(
            f"{HEX_SERVICE} not built; run `lake build hexbz_factor_service`")
    return [str(HEX_SERVICE), "--entry", entry]


def total_nanos(profile: dict) -> "int | None":
    phases = profile.get("phases") or {}
    total = phases.get("total")
    return None if total is None else total["nanos"]


def call_ok(service: Service, coeffs, cutoff: float):
    """One request; returns the `result` object, or None on timeout/error."""
    reply, elapsed = service.call({"coeffs": coeffs}, cutoff)
    if reply is None:
        service.respawn()
        return None, None
    if not reply.get("ok"):
        return None, elapsed
    return reply.get("result"), elapsed


def measure_phase_profile(service: Service, inst: dict, cutoff: float,
                          warmup: int, repeats: int) -> dict:
    """Warm up, then repeat, and keep the median-total run's full profile.

    The profile kept is one whole execution rather than a per-phase median of
    different executions, so its phases still sum to its own total.
    """
    coeffs = inst["coeffs"]
    for _ in range(warmup):
        result, _ = call_ok(service, coeffs, cutoff)
        if result is None:
            return {"status": "timeout"}
    runs = []
    result, _ = call_ok(service, coeffs, cutoff)
    if result is None:
        return {"status": "timeout"}
    runs.append(result)
    first = total_nanos(result)
    if first is not None and first < REPEAT_CEILING_NANOS:
        for _ in range(max(0, repeats - 1)):
            result, _ = call_ok(service, coeffs, cutoff)
            if result is None:
                return {"status": "timeout"}
            runs.append(result)
    totals = sorted(total_nanos(r) for r in runs)
    median = totals[len(totals) // 2]
    chosen = min(runs, key=lambda r: abs(total_nanos(r) - median))
    return {
        "status": "ok",
        "runs": len(runs),
        "total_nanos_min": totals[0],
        "total_nanos_median": median,
        "total_nanos_max": totals[-1],
        "profile": chosen,
    }


def measure_end_to_end(service: Service, inst: dict, cutoff: float,
                       warmup: int, repeats: int) -> dict:
    """Untimed-phase production `factor` wall time, for the overhead estimate."""
    coeffs = inst["coeffs"]
    for _ in range(warmup):
        if call_ok(service, coeffs, cutoff)[0] is None:
            return {"status": "timeout"}
    samples = []
    result, elapsed = call_ok(service, coeffs, cutoff)
    if result is None:
        return {"status": "timeout"}
    samples.append(elapsed)
    if elapsed < REPEAT_CEILING_NANOS:
        for _ in range(max(0, repeats - 1)):
            result, elapsed = call_ok(service, coeffs, cutoff)
            if result is None:
                return {"status": "timeout"}
            samples.append(elapsed)
    samples.sort()
    return {
        "status": "ok",
        "runs": len(samples),
        "median_nanos": samples[len(samples) // 2],
        "min_nanos": samples[0],
        "max_nanos": samples[-1],
    }


def merge_plans(plans):
    """Median each per-candidate cost across repeated calls on one instance.

    Structure (candidate order, primes, widths, degrees, node and division
    counts) is deterministic, so the first non-empty plan supplies it and only
    the timings are replaced.
    """
    plans = [p for p in plans if p]
    if not plans:
        return None
    base = next((json.loads(json.dumps(p)) for p in plans if p.get("candidates")),
                None)
    if base is None:
        return plans[0]
    for i, cand in enumerate(base["candidates"]):
        peers = [p["candidates"][i] for p in plans
                 if len(p.get("candidates") or []) > i
                 and p["candidates"][i].get("prime") == cand.get("prime")]
        for key in PLAN_NANO_KEYS:
            values = [q[key]["nanos"] for q in peers if key in q]
            if values:
                cand[key]["nanos"] = int(statistics.median(values))
        values = [q["downstreamNanos"] for q in peers if "downstreamNanos" in q]
        if values:
            cand["downstreamNanos"] = int(statistics.median(values))
    return base


def measure_plan(service, inst, cutoff, repeats):
    """Repeat one plan-section call and merge the repeats by median."""
    plans = []
    for _ in range(max(1, repeats)):
        result, _ = call_ok(service, inst["coeffs"], cutoff)
        if result is None:
            return None
        plans.append(result)
    return merge_plans(plans)


def merge_kernels(kernels):
    """Median every duration in a kernel record across repeated calls.

    Structure -- basis size, modulus, rank, kernel dimension, row-addition
    counts, and every agreement flag -- is deterministic, so the first record
    supplies it and only the durations are replaced. A repeat that disagrees on
    any of the deterministic fields is a harness fault, not noise, so it raises.
    """
    kernels = [k for k in kernels if k]
    if not kernels:
        return None
    base = json.loads(json.dumps(kernels[0]))
    for key in ("basisSize", "modulus", "rank", "kernelDimension",
                "mirrorAgreesWithRowReduce", "echelonOnlyAgrees",
                "splitFactors"):
        values = {json.dumps(k.get(key)) for k in kernels}
        if len(values) > 1:
            raise SystemExit(
                f"kernel repeats disagree on deterministic field {key}: {values}")
    for key in KERNEL_SPAN_KEYS:
        if key in base:
            base[key]["nanos"] = int(statistics.median(
                k[key]["nanos"] for k in kernels))
            base[key]["smallAllocs"] = int(statistics.median(
                k[key]["smallAllocs"] for k in kernels))
    for key in ("matrixConversionNanos", "fixedSpaceDiagonalNanos",
                "peakResidentBytes"):
        if key in base:
            base[key] = int(statistics.median(k[key] for k in kernels))
    # The basis stage is a signed within-execution difference, so median the
    # signed values rather than the truncated magnitudes.
    signed = [(-1 if k["nullspaceBasisNegative"] else 1)
              * k["nullspaceBasisMagnitudeNanos"] for k in kernels]
    median = int(statistics.median(signed))
    base["nullspaceBasisNegative"] = median < 0
    base["nullspaceBasisMagnitudeNanos"] = abs(median)
    base["nullspaceBasisNanos"] = max(0, median)
    for outer in KERNEL_COUNTED_KEYS:
        for span in ("pivotSearch", "rowSwapScale", "rowAdd", "wall"):
            base[outer][span]["nanos"] = int(statistics.median(
                k[outer][span]["nanos"] for k in kernels))
            base[outer][span]["smallAllocs"] = int(statistics.median(
                k[outer][span]["smallAllocs"] for k in kernels))
        base[outer]["stagedNanos"] = int(statistics.median(
            k[outer]["stagedNanos"] for k in kernels))
    for outer in KERNEL_PACKED_KEYS:
        for field in ("packNanos", "reduceNanos", "nullspaceNanos",
                      "totalNanos", "smallAllocs"):
            base[outer][field] = int(statistics.median(
                k[outer][field] for k in kernels))
        if not all(k[outer]["agreesWithNullspace"] for k in kernels):
            raise SystemExit(
                f"packed variant {outer} disagreed with Hex.Matrix.nullspace")
    return base


def measure_kernel(service, inst, cutoff, repeats):
    """Repeat the kernel attribution and merge the repeats by median."""
    records = []
    for _ in range(max(1, repeats)):
        result, _ = call_ok(service, inst["coeffs"], cutoff)
        if result is None:
            return None
        records.append(result)
    if any(r.get("status") != "ok" for r in records):
        return records[0]
    merged = dict(records[0])
    merged["kernel"] = merge_kernels([r["kernel"] for r in records])
    return merged


def degree_multiset(profile: dict):
    """Sorted factor degrees with multiplicity from a phase profile."""
    degrees = []
    for degree, multiplicity in zip(profile.get("factorDegrees", []),
                                    profile.get("multiplicities", [])):
        degrees.extend([degree] * multiplicity)
    return sorted(degrees)


def trace_degree_multiset(factorization):
    """Sorted factor degrees with multiplicity from a `factorTrace` reply."""
    if factorization is None:
        return None
    degrees = []
    for factor in factorization.get("factors", []):
        degrees.extend([len(factor["coeffs"]) - 1] * factor.get("multiplicity", 1))
    return sorted(degrees)


def validate_instance(trace_service: Service, inst: dict, profile: dict,
                      cutoff: float) -> dict:
    """Cross-check the counted recombination mirror against the production trace.

    `factorTrace` runs the unrestricted classical tier, so the comparison is
    meaningful exactly when the profiled cascade also answered classically from
    the same prime.
    """
    out = {"applicable": False}
    recombination = profile.get("recombination")
    if recombination is None or profile.get("method") != "classical":
        out["reason"] = "profiled run did not answer from the direct classical tier"
        return out
    result, _ = call_ok(trace_service, inst["coeffs"], cutoff)
    if result is None:
        out["reason"] = "factorTrace timed out"
        return out
    trace = result.get("trace", {})
    if trace.get("method") != "classical" or trace.get("decline") is not None:
        out["reason"] = f"factorTrace declined ({trace.get('decline')})"
        return out
    mirror_nodes = recombination["stages"]["nodes"]
    mirror_prime = (profile.get("primeWalk") or {}).get("selectedPrime")
    mirror_degrees = degree_multiset(profile)
    production_degrees = trace_degree_multiset(result.get("factorization"))
    out.update({
        "applicable": True,
        "mirror_nodes": mirror_nodes,
        "production_candidates_tried": trace.get("candidatesTried"),
        "nodes_agree": mirror_nodes == trace.get("candidatesTried"),
        "mirror_prime": mirror_prime,
        "production_prime": trace.get("prime"),
        "prime_agrees": mirror_prime == trace.get("prime"),
        "mirror_completed_levels": recombination["completedLevels"],
        "production_completed_levels": trace.get("completedLevels"),
        "levels_agree":
            recombination["completedLevels"] == trace.get("completedLevels"),
        "mirror_factor_degrees": mirror_degrees,
        "production_factor_degrees": production_degrees,
        "factors_agree": mirror_degrees == production_degrees,
    })
    return out


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--corpus", type=Path, default=CORPUS_PATH)
    p.add_argument("--names", default=None,
                   help="comma-separated instance names (default: the issue "
                        "#9127 representative set plus its controls)")
    p.add_argument("--validate-names", default=None,
                   help="comma-separated instance names for the wider mirror "
                        "validation sample (default: every corpus instance "
                        "under --validate-cutoff)")
    p.add_argument("--cutoff", type=float, default=DEFAULT_CUTOFF,
                   help=f"per-call cutoff seconds (default {DEFAULT_CUTOFF})")
    p.add_argument("--validate-cutoff", type=float, default=2.0,
                   help="per-call cutoff for the wider validation sample")
    p.add_argument("--warmup", type=int, default=DEFAULT_WARMUP)
    p.add_argument("--repeats", type=int, default=DEFAULT_REPEATS)
    p.add_argument("--no-counterfactual", dest="counterfactual",
                   action="store_false",
                   help="skip the per-candidate counterfactual prime plans")
    p.add_argument("--no-scout", dest="scout", action="store_false",
                   help="skip the per-candidate scout prices")
    p.add_argument("--no-kernel", dest="kernel", action="store_false",
                   help="skip the Berlekamp fixed-space kernel attribution")
    p.add_argument("--kernel-repeats", type=int, default=DEFAULT_KERNEL_REPEATS,
                   help="calls per instance for the kernel attribution "
                        f"(default {DEFAULT_KERNEL_REPEATS}); every duration "
                        "is their median")
    p.add_argument("--plan-repeats", type=int, default=DEFAULT_PLAN_REPEATS,
                   help="calls per instance for the counterfactual and scout "
                        f"sections (default {DEFAULT_PLAN_REPEATS}); the "
                        "per-candidate costs are their median")
    p.add_argument("--output", type=Path, default=None)
    p.add_argument("--cpu", default="auto",
                   help="logical CPU to pin to, or `auto` to pick an idle one "
                        "(default auto)")
    args = p.parse_args()

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    print(f"pinned to cpu {cpu}", file=sys.stderr)

    corpus = {inst["name"]: inst for inst in load_corpus(args.corpus)}
    names = ([n.strip() for n in args.names.split(",") if n.strip()]
             if args.names else REPRESENTATIVE + CONTROLS)
    missing = [n for n in names if n not in corpus]
    if missing:
        raise SystemExit("unknown corpus instances: " + ", ".join(missing))

    profile_service = Service(service_argv("factorPhaseProfile"))
    factor_service = Service(service_argv("factor"))
    trace_service = Service(service_argv("factorTrace"))

    results = []
    for name in names:
        inst = corpus[name]
        print(f"phase profile: {name} (degree {inst['degree']})", file=sys.stderr)
        measured = measure_phase_profile(
            profile_service, inst, args.cutoff, args.warmup, args.repeats)
        end_to_end = measure_end_to_end(
            factor_service, inst, args.cutoff, args.warmup, args.repeats)
        row = {
            "name": name,
            "family": inst["family"],
            "degree": inst["degree"],
            "expected_factor_degrees": inst.get("expectedFactorDegrees"),
            "phase_profile": measured,
            "end_to_end": end_to_end,
            "representative": name in REPRESENTATIVE,
            "sampling_profile_captured": name in PROFILED,
        }
        if measured["status"] == "ok" and end_to_end["status"] == "ok":
            profiled = measured["total_nanos_median"]
            plain = end_to_end["median_nanos"]
            row["instrumentation_ratio"] = profiled / plain if plain else None
            row["validation"] = validate_instance(
                trace_service, inst, measured["profile"], args.cutoff)
        results.append(row)

    counterfactuals = []
    if args.counterfactual:
        cf_service = Service(service_argv("primeCounterfactual"))
        for name in names:
            inst = corpus[name]
            print(f"counterfactual: {name}", file=sys.stderr)
            result = measure_plan(cf_service, inst, args.cutoff, args.plan_repeats)
            counterfactuals.append({
                "name": name,
                "family": inst["family"],
                "degree": inst["degree"],
                "status": "timeout" if result is None else "ok",
                "plan": result,
            })
        cf_service.kill()

    scouts = []
    if args.scout:
        scout_service = Service(service_argv("primeScout"))
        for name in names:
            inst = corpus[name]
            print(f"scout: {name}", file=sys.stderr)
            result = measure_plan(scout_service, inst, args.cutoff, args.plan_repeats)
            scouts.append({
                "name": name,
                "family": inst["family"],
                "degree": inst["degree"],
                "status": "timeout" if result is None else "ok",
                "plan": result,
            })
        scout_service.kill()

    kernels = []
    if args.kernel:
        kernel_service = Service(service_argv("kernelProfile"))
        for name in names:
            inst = corpus[name]
            print(f"kernel: {name}", file=sys.stderr)
            result = measure_kernel(
                kernel_service, inst, args.cutoff, args.kernel_repeats)
            kernels.append({
                "name": name,
                "family": inst["family"],
                "degree": inst["degree"],
                "status": "timeout" if result is None else result.get("status"),
                "kernel": result,
            })
        kernel_service.kill()

    # Wider validation sample: every corpus instance the classical tier answers
    # quickly, so the mirror's agreement with the production trace is not only
    # checked where the expensive phase profile ran.
    if args.validate_names is not None:
        wider = [n.strip() for n in args.validate_names.split(",") if n.strip()]
    else:
        wider = [inst["name"] for inst in corpus.values()]
    validation = []
    for name in wider:
        inst = corpus[name]
        result, _ = call_ok(profile_service, inst["coeffs"], args.validate_cutoff)
        if result is None:
            continue
        check = validate_instance(trace_service, inst, result, args.validate_cutoff)
        if check.get("applicable"):
            validation.append({"name": name, **check})
    print(f"wider validation sample: {len(validation)} instances", file=sys.stderr)

    profile_service.kill()
    factor_service.kill()
    trace_service.kill()

    ratios = [r["instrumentation_ratio"] for r in results
              if r.get("instrumentation_ratio")]
    scout_rows = 0
    scout_agree = 0
    scout_bad = []
    for row in scouts:
        for cand in ((row.get("plan") or {}).get("candidates") or []):
            if cand.get("zeroModularImage"):
                continue
            scout_rows += 1
            if cand.get("patternAgrees"):
                scout_agree += 1
            else:
                scout_bad.append({"name": row["name"], **cand})
    kernel_rows = 0
    kernel_mirror_agree = 0
    kernel_packed_agree = 0
    kernel_bad = []
    for row in kernels:
        k = ((row.get("kernel") or {}).get("kernel")) or {}
        if not k:
            continue
        kernel_rows += 1
        mirror_ok = k.get("mirrorAgreesWithRowReduce") and k.get(
            "echelonOnlyAgrees")
        packed_ok = all(k[key]["agreesWithNullspace"]
                        for key in KERNEL_PACKED_KEYS if key in k)
        kernel_mirror_agree += 1 if mirror_ok else 0
        kernel_packed_agree += 1 if packed_ok else 0
        if not (mirror_ok and packed_ok):
            kernel_bad.append({"name": row["name"],
                               "mirror_ok": bool(mirror_ok),
                               "packed_ok": bool(packed_ok)})

    record = {
        "schema": "hexbz-phase-profile/3",
        "env": env_block("hexbz_factor_service"),
        "config": {
            "cpu": cpu,
            "corpus": str(args.corpus.relative_to(ROOT)),
            "corpus_sha256": sha256(args.corpus),
            "hex_exe_sha256": sha256(HEX_SERVICE),
            "cutoff_seconds": args.cutoff,
            "validate_cutoff_seconds": args.validate_cutoff,
            "warmup": args.warmup,
            "repeats": args.repeats,
            "plan_repeats": args.plan_repeats,
            "kernel_repeats": args.kernel_repeats,
            "repeat_ceiling_nanos": REPEAT_CEILING_NANOS,
            "names": names,
            "representative": REPRESENTATIVE,
            "controls": CONTROLS,
            "sampling_profiles": PROFILED,
        },
        "results": results,
        "counterfactuals": counterfactuals,
        "scouts": scouts,
        "kernels": kernels,
        "validation": {
            "sample_size": len(validation),
            "nodes_agree": sum(1 for v in validation if v["nodes_agree"]),
            "prime_agree": sum(1 for v in validation if v["prime_agrees"]),
            "levels_agree": sum(1 for v in validation if v["levels_agree"]),
            "factors_agree": sum(1 for v in validation if v["factors_agree"]),
            "disagreements": [
                v for v in validation
                if not (v["nodes_agree"] and v["prime_agrees"]
                        and v["levels_agree"] and v["factors_agree"])],
            "instrumentation_ratio_median":
                statistics.median(ratios) if ratios else None,
            "instrumentation_ratio_max": max(ratios) if ratios else None,
            "scout_rows": scout_rows,
            "scout_patterns_agree": scout_agree,
            "scout_disagreements": scout_bad,
            "kernel_rows": kernel_rows,
            "kernel_mirror_agree": kernel_mirror_agree,
            "kernel_packed_agree": kernel_packed_agree,
            "kernel_disagreements": kernel_bad,
        },
    }

    out = args.output
    if out is None:
        commit = (record["env"].get("git_commit") or "unknown")[:8]
        host = record["env"].get("hostname") or "unknown"
        BENCH_RESULTS.mkdir(parents=True, exist_ok=True)
        out = BENCH_RESULTS / f"hexbz-phase-profile-{commit}-{host}.json"
    out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"wrote {out}", file=sys.stderr)

    if kernel_bad:
        print(f"kernel attribution disagreed with the production row reduction "
              f"or nullspace on {len(kernel_bad)} instances", file=sys.stderr)
        return 1
    if scout_bad:
        print(f"scouted degree pattern disagreed with the Berlekamp split on "
              f"{len(scout_bad)} candidates", file=sys.stderr)
        return 1
    bad = record["validation"]["disagreements"]
    if bad:
        print(f"mirror disagreed with the production trace on {len(bad)} "
              f"instances", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
