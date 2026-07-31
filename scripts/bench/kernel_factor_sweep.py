#!/usr/bin/env python3
"""Compare kernel factorization with certificate-backed polynomial tactics.

For each selected row of the committed integer-polynomial factor corpus this
diagnostic runs three fresh, Lake-built modules:

* a baseline proposition forcing kernel evaluation of
  ``Hex.ZPoly.factorize`` against the compiled factorization;
* ``factor_poly`` on the complete integer polynomial; and
* ``irreducibility`` when the corpus identifies the input as irreducible.

The tactic timings are end-to-end fresh-module times: they include compiled
factor/certificate search at elaboration time and kernel checking of the
reified result.  They are deliberately not labelled kernel-only.  Fixed import
baselines are recorded separately for the Mathlib-free factorization module and
the Mathlib certificate-provider module.

For multi-prime witnesses, an untimed preparation module serializes the exact
nested Rabin certificates.  Two further fresh modules replay identical literal
data with ``checkIrreducibilityCertificateLinear`` and
``checkIrreducibilityCertificateLinearIncremental``.  Their only source
difference is the checker name, isolating checker selection from certificate
search.  The signed import-baseline delta still includes literal elaboration,
instance synthesis, and kernel checking.

Provider decline is data.  Timeouts and kernel resource limits are censored.
An unexpected elaboration error, malformed metadata, or a generated
certificate rejected by either checker makes the sweep exit nonzero after it
writes the diagnostic record.

This is a manual diagnostic, not CI.  A representative sampled run is:

    python3 scripts/bench/kernel_factor_sweep.py \
      --name cyclo_phi5 --name xpow6_minus1 --name quartic_a4 \
      --name sd2 --timeout 30
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
HEX_SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"
KERNEL_IMPORT = "HexBerlekampZassenhaus.Factorization"
CERTIFICATE_IMPORT = "HexBerlekampZassenhausMathlib"
META_PREFIX = "KERNEL_FACTOR_META="

DEFAULT_MAX_REC_DEPTH = 100000
DEFAULT_MAX_HEARTBEATS = 0

# Direct kernel factorization is monotone enough to stop after its first
# censored point for most families.  Cyclotomic cost follows modular splitting
# rather than degree, so those families retain the old consecutive-hit rule.
NON_MONOTONE_FAMILIES = {"cyclotomic", "cyclotomic-products", "conway"}
CENSORED = {"timeout", "maxRecDepth", "maxHeartbeats"}


def hex_factor(coeffs, service):
    """Return ``(scalar, [(coeffs, multiplicity), ...])`` from compiled Hex."""
    service.stdin.write(json.dumps({"coeffs": coeffs}) + "\n")
    service.stdin.flush()
    line = service.stdout.readline()
    if not line:
        raise RuntimeError("the compiled factor service closed its output")
    reply = json.loads(line)
    if not reply.get("ok") or reply.get("result") is None:
        return None
    result = reply["result"]
    return result["scalar"], [
        (factor["coeffs"], factor["multiplicity"])
        for factor in result["factors"]
    ]


def coeff_array(coeffs):
    return "#[" + ",".join(str(c) for c in coeffs) + "]"


def zpoly(coeffs):
    # Tactic terms elaborate their argument before consulting the dependent
    # expected result type.  Without this ascription an all-nonnegative row is
    # inferred as ``DensePoly Nat`` and the integer provider correctly refuses
    # it; negative-coefficient rows happened to mask that bug in the old probe.
    return f"(Hex.DensePoly.ofCoeffs {coeff_array(coeffs)} : Hex.ZPoly)"


def option_block(max_rec, max_heartbeats, declaration):
    return (
        f"set_option maxRecDepth {max_rec} in\n"
        f"set_option maxHeartbeats {max_heartbeats} in\n"
        f"{declaration}\n"
    )


def gen_kernel_factor(coeffs, factorization, max_rec, max_heartbeats):
    scalar, factors = factorization
    entries = ",".join(
        f"({zpoly(factor_coeffs)}, {multiplicity})"
        for factor_coeffs, multiplicity in factors
    )
    proposition = (
        f"example : Hex.ZPoly.factorize ({zpoly(coeffs)})\n"
        f"    = ⟨{scalar}, #[{entries}]⟩ := by decide +kernel"
    )
    return (
        f"import {KERNEL_IMPORT}\n"
        "open Hex\n"
        + option_block(max_rec, max_heartbeats, proposition)
    )


def gen_factor_poly(coeffs, max_rec, max_heartbeats):
    declaration = (
        f"noncomputable example : Hex.ZPoly.Factored ({zpoly(coeffs)}) :=\n"
        f"  factor_poly ({zpoly(coeffs)})"
    )
    return (
        f"import {CERTIFICATE_IMPORT}\n"
        "open Hex\n"
        + option_block(max_rec, max_heartbeats, declaration)
    )


def gen_irreducibility(coeffs, max_rec, max_heartbeats):
    declaration = (
        f"example : Hex.ZPoly.Irreducible ({zpoly(coeffs)}) := by\n"
        "  irreducibility"
    )
    return (
        f"import {CERTIFICATE_IMPORT}\n"
        "open Hex\n"
        + option_block(max_rec, max_heartbeats, declaration)
    )


def gen_classification(factors):
    factor_literals = ",".join(zpoly(coeffs) for coeffs, _multiplicity in factors)
    return f'''import {CERTIFICATE_IMPORT}
import Lean.Data.Json

open Hex
open Lean

namespace KernelFactorSweep

def natJson (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

def intJson (n : Int) : Json :=
  Json.num (JsonNumber.fromInt n)

def natListJson (xs : List Nat) : Json :=
  Json.arr (xs.toArray.map natJson)

def rabinJson
    (data : Nat × Nat × List (List Nat) × List (List Nat × List Nat)) : Json :=
  let (p, n, powChain, bezout) := data
  Json.mkObj
    [("p", natJson p),
     ("n", natJson n),
     ("pow_chain", Json.arr <| powChain.toArray.map natListJson),
     ("bezout", Json.arr <| bezout.toArray.map fun pair =>
       Json.mkObj [("left", natListJson pair.1),
                   ("right", natListJson pair.2)])]

def rabinCaseJson {{p : Nat}} [bounds : ZMod64.Bounds p]
    (degree : Nat) (factor : FpPoly p)
    (cert : Berlekamp.IrreducibilityCertificate) : Json :=
  let acceptedLinear :=
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificateLinear factor hmonic cert
    else false
  let acceptedIncremental :=
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificateLinearIncremental factor hmonic cert
    else false
  Json.mkObj
    [("degree", natJson degree),
     ("monic", Json.bool (factor.leadingCoeff == 1)),
     ("factor", natListJson (Hex.CertReify.fpCoeffNats factor)),
     ("certificate", rabinJson (Hex.CertReify.rabinCertData cert)),
     ("accepted_linear", Json.bool acceptedLinear),
     ("accepted_incremental", Json.bool acceptedIncremental)]

def primeBlockJson (data : PrimeFactorData) : Json :=
  match data with
  | {{ p := p, bounds := bounds, factorDegrees := degrees,
       factorPolys := factors, factorCerts := certs }} =>
      letI := bounds
      let cases := degrees.toList.zip (factors.toList.zip certs.toList)
      Json.mkObj
        [("prime", natJson p),
         ("degree_count", natJson degrees.size),
         ("factor_count", natJson factors.size),
         ("certificate_count", natJson certs.size),
         ("cases", Json.arr <| cases.toArray.map fun entry =>
           rabinCaseJson entry.1 entry.2.1 entry.2.2)]

def multiJson (cert : ZPolyIrreducibilityCertificate) : Json :=
  Json.mkObj
    [("class", Json.str "multi-prime"),
     ("primes", Json.arr <| cert.perPrime.map fun block => natJson block.p),
     ("obstruction_count", natJson cert.degreeObstructions.size),
     ("blocks", Json.arr <| cert.perPrime.map primeBlockJson)]

meta def classifyFactor (factor : ZPoly) : Json :=
  match HexBerlekampZassenhaus.FactorTactic.searchWitness factor with
  | some (.primeConst) => Json.mkObj [("class", Json.str "free-prime-constant")]
  | some (.linear) => Json.mkObj [("class", Json.str "free-linear")]
  | some (.modP witness) =>
      Json.mkObj [("class", Json.str "free-mod-p"),
                  ("prime", natJson witness.p)]
  | some (.eisenstein prime shift) =>
      Json.mkObj [("class", Json.str "free-eisenstein"),
                  ("prime", natJson prime),
                  ("shift", intJson shift)]
  | none =>
      match Hex.certifyIrreducible? factor with
      | some cert => multiJson cert
      | none => Json.mkObj [("class", Json.str "provider-decline")]

run_meta do
  let factors : List ZPoly := [{factor_literals}]
  let result := Json.arr (factors.toArray.map classifyFactor)
  Lean.logInfo s!"{META_PREFIX}{{result.compress}}"

end KernelFactorSweep
'''


def fp_poly_literal(prime, coeffs):
    entries = ",".join(f"Hex.ZMod64.ofNat {prime} {n}" for n in coeffs)
    return f"Hex.FpPoly.ofCoeffs (p := {prime}) #[{entries}]"


def rabin_certificate_literal(prime, certificate):
    pow_chain = ",".join(
        fp_poly_literal(prime, coeffs) for coeffs in certificate["pow_chain"]
    )
    bezout = ",".join(
        "{ left := " + fp_poly_literal(prime, witness["left"])
        + ", right := " + fp_poly_literal(prime, witness["right"]) + " }"
        for witness in certificate["bezout"]
    )
    return (
        "{ p := " + str(certificate["p"])
        + ", n := " + str(certificate["n"])
        + ", powChain := #[" + pow_chain + "]"
        + ", bezout := #[" + bezout + "] }"
    )


def gen_rabin_replay(case, checker, max_rec, max_heartbeats):
    prime = case["prime"]
    factor = fp_poly_literal(prime, case["factor"])
    certificate = rabin_certificate_literal(prime, case["certificate"])
    declaration = (
        f"example : Hex.Berlekamp.{checker}\n"
        f"    ({factor}) (by rfl)\n"
        f"    ({certificate}) = true := by decide +kernel"
    )
    return (
        f"import {CERTIFICATE_IMPORT}\n"
        "open Hex\n"
        f"local instance : Hex.ZMod64.Bounds {prime} :=\n"
        f"  Hex.CertReify.boundsOfDecide {prime} rfl\n"
        + option_block(max_rec, max_heartbeats, declaration)
    )


def classify_failure(output):
    low = output.lower()
    if "maxrecdepth" in low or "maximum recursion depth" in low:
        return "maxRecDepth"
    if "maxheartbeats" in low or "deterministic timeout" in low:
        return "maxHeartbeats"
    decline_marker = "no certificate-backed proof is available"
    decline_at = low.rfind(decline_marker)
    if decline_at >= 0 and "error:" not in low[decline_at + len(decline_marker):]:
        return "provider-decline"
    return "error"


def run_lake_lean(source, timeout, workdir, stem):
    path = workdir / f"{stem}.lean"
    path.write_text(source)
    start = time.perf_counter_ns()
    proc = subprocess.Popen(
        ["lake", "-q", "lean", str(path)],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = proc.communicate()
        output = stdout + stderr
        return "timeout", None, output
    elapsed = time.perf_counter_ns() - start
    output = stdout + stderr
    if proc.returncode == 0:
        return "ok", elapsed, output
    return classify_failure(output), elapsed, output


def import_baseline(import_name, timeout, workdir, stem, repeats):
    source = f"import {import_name}\n"
    samples = []
    for repeat in range(repeats):
        status, elapsed, output = run_lake_lean(
            source, timeout, workdir, f"{stem}{repeat}"
        )
        if status != "ok" or elapsed is None:
            raise RuntimeError(
                f"failed to measure {import_name} import baseline ({status}):\n"
                + output[-1200:]
            )
        samples.append(elapsed)
    samples.sort()
    return samples[len(samples) // 2]


def timing_record(status, elapsed, baseline, output=""):
    baseline_delta = None if elapsed is None else elapsed - baseline
    record = {
        "status": status,
        "total_nanos": elapsed,
        "baseline_nanos": baseline,
        "baseline_delta_nanos": baseline_delta,
    }
    if status not in {"ok", "not-applicable", "skipped-frontier"} and output:
        record["message"] = diagnostic_excerpt(output)
    return record


def diagnostic_excerpt(output):
    """Keep the actual Lean diagnostic instead of trailing replay warnings."""
    decline_markers = (
        "no certificate-backed proof is available",
        "has no single-prime modular witness",
    )
    general_markers = (
        "error:",
        "maximum recursion depth",
        "deterministic timeout",
    )
    low = output.lower()
    positions = [low.find(marker) for marker in decline_markers]
    positions = [position for position in positions if position >= 0]
    if not positions:
        positions = [low.find(marker) for marker in general_markers]
        positions = [position for position in positions if position >= 0]
    if not positions:
        return output[-1200:]
    position = min(positions)
    start = output.rfind("\n", 0, max(0, position - 200)) + 1
    return output[start:position + 1000]


def classify_witnesses(factors, timeout, workdir):
    status, _elapsed, output = run_lake_lean(
        gen_classification(factors), timeout, workdir, "CertificateMetadata"
    )
    if status != "ok":
        return status, [], output
    payloads = [line[len(META_PREFIX):] for line in output.splitlines()
                if line.startswith(META_PREFIX)]
    if len(payloads) != 1:
        return "error", [], (
            f"expected one {META_PREFIX} line, found {len(payloads)}\n" + output
        )
    try:
        metadata = json.loads(payloads[0])
    except json.JSONDecodeError as exc:
        return "error", [], f"invalid certificate metadata JSON: {exc}\n{output}"
    if len(metadata) != len(factors):
        return "error", [], (
            f"certificate metadata has {len(metadata)} factors, expected {len(factors)}"
        )
    return "ok", metadata, ""


def coeffs_digest(coeffs):
    payload = json.dumps(coeffs, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def public_witnesses(factors, metadata):
    rows = []
    for index, ((coeffs, multiplicity), witness) in enumerate(zip(factors, metadata)):
        public = {key: value for key, value in witness.items() if key != "blocks"}
        public.update({
            "factor_index": index,
            "degree": max(0, len(coeffs) - 1),
            "multiplicity": multiplicity,
            "coeffs_sha256": coeffs_digest(coeffs),
        })
        if witness.get("class") == "multi-prime":
            public["rabin_case_count"] = sum(
                len(block["cases"]) for block in witness.get("blocks", [])
            )
        rows.append(public)
    return rows


def rabin_cases(metadata, max_cases):
    cases = []
    dropped = 0
    for factor_index, witness in enumerate(metadata):
        if witness.get("class") != "multi-prime":
            continue
        factor_cases = []
        for block_index, block in enumerate(witness.get("blocks", [])):
            prime = block["prime"]
            counts = {
                block.get("degree_count"),
                block.get("factor_count"),
                block.get("certificate_count"),
                len(block.get("cases", [])),
            }
            if len(counts) != 1:
                raise RuntimeError(
                    "mismatched multi-prime certificate arrays "
                    f"(factor {factor_index}, p={prime})"
                )
            for certificate_index, case in enumerate(block.get("cases", [])):
                if not case.get("monic"):
                    raise RuntimeError(
                        "generated Rabin factor is not monic "
                        f"(factor {factor_index}, p={prime})"
                    )
                if not case.get("accepted_linear") or not case.get("accepted_incremental"):
                    raise RuntimeError(
                        "generated Rabin certificate was not accepted by both "
                        f"compiled checkers (factor {factor_index}, p={prime})"
                    )
                factor_cases.append({
                    **case,
                    "factor_index": factor_index,
                    "block_index": block_index,
                    "certificate_index": certificate_index,
                    "prime": prime,
                })
        if max_cases and len(factor_cases) > max_cases:
            dropped += len(factor_cases) - max_cases
            factor_cases = factor_cases[:max_cases]
        cases.extend(factor_cases)
    return cases, dropped


def aggregate_timing(samples, baseline):
    statuses = [status for status, _elapsed, _output in samples]
    status = next((item for item in statuses if item != "ok"), "ok")
    elapsed_samples = [
        elapsed for _status, elapsed, _output in samples if elapsed is not None
    ]
    sorted_elapsed = sorted(elapsed_samples)
    elapsed = sorted_elapsed[len(sorted_elapsed) // 2] if sorted_elapsed else None
    output = next(
        (message for item, _elapsed, message in samples if item != "ok"), ""
    )
    record = timing_record(status, elapsed, baseline, output)
    record.update({
        "repeats": len(samples),
        "sample_statuses": statuses,
        "sample_total_nanos": [sample for sample in elapsed_samples],
        "min_total_nanos": min(elapsed_samples) if elapsed_samples else None,
        "max_total_nanos": max(elapsed_samples) if elapsed_samples else None,
    })
    return record


def run_rabin_series(
    cases, timeout, workdir, baseline, max_rec, max_heartbeats, repeats
):
    rows = []
    checkers = {
        "linear": "checkIrreducibilityCertificateLinear",
        "incremental": "checkIrreducibilityCertificateLinearIncremental",
    }
    for case_index, case in enumerate(cases):
        row = {
            "factor_index": case["factor_index"],
            "block_index": case["block_index"],
            "certificate_index": case["certificate_index"],
            "prime": case["prime"],
            "degree": case["degree"],
            "literal_sha256": hashlib.sha256(
                json.dumps(
                    {"factor": case["factor"], "certificate": case["certificate"]},
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest(),
        }
        samples = {label: [] for label in checkers}
        orders = []
        for repeat in range(repeats):
            order = list(checkers)
            if (case_index + repeat) % 2:
                order.reverse()
            orders.append(order)
            for label in order:
                source = gen_rabin_replay(
                    case, checkers[label], max_rec, max_heartbeats
                )
                status, elapsed, output = run_lake_lean(
                    source, timeout, workdir,
                    f"Rabin{label.title()}{case_index}Repeat{repeat}",
                )
                samples[label].append((status, elapsed, output))
        row["execution_order"] = orders
        for label in checkers:
            row[label] = aggregate_timing(samples[label], baseline)
        rows.append(row)
    return rows


def is_known_irreducible(instance, factorization):
    """Corpus degree data plus unit content identify an irreducible input.

    A single expected factor degree is not sufficient: Legendre rows, for
    example, can have non-unit content and hence are not irreducible as elements
    of ``Z[x]`` even though their primitive part has one full-degree factor.
    """
    expected = instance.get("expectedFactorDegrees")
    if expected != [instance["degree"]] or factorization is None:
        return False
    scalar, factors = factorization
    return (
        abs(scalar) == 1
        and len(factors) == 1
        and factors[0][1] == 1
        and len(factors[0][0]) - 1 == instance["degree"]
    )


def environment_block():
    def git(args):
        try:
            return subprocess.run(
                ["git", "-C", str(ROOT)] + args,
                capture_output=True,
                text=True,
                check=False,
            ).stdout.strip()
        except OSError:
            return ""

    commit = git(["rev-parse", "HEAD"]) or None
    dirty = git(["status", "--porcelain"])
    toolchain_path = ROOT / "lean-toolchain"
    toolchain = toolchain_path.read_text().strip() if toolchain_path.exists() else None
    now = time.time()
    return {
        "lean_toolchain": toolchain,
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "cpu_cores": os.cpu_count(),
        "hostname": socket.gethostname(),
        "exe_name": "kernel_factor_sweep",
        "git_commit": commit,
        "git_dirty": bool(dirty) if commit else None,
        "timestamp_unix_ms": int(now * 1000),
        "timestamp_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
    }


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--corpus", type=Path, default=CORPUS_PATH)
    parser.add_argument("--timeout", type=float, default=60.0,
                        help="per generated-module wall timeout in seconds")
    parser.add_argument("--max-degree", type=int, default=None)
    parser.add_argument("--family", default=None)
    parser.add_argument("--name", action="append", default=[],
                        help="select an exact corpus name; repeatable")
    parser.add_argument("--combined-only", action="store_true")
    parser.add_argument("--max-rec-depth", type=int, default=DEFAULT_MAX_REC_DEPTH)
    parser.add_argument("--max-heartbeats", type=int, default=DEFAULT_MAX_HEARTBEATS)
    parser.add_argument("--explore-stop-after", type=int, default=3)
    parser.add_argument("--baseline-repeats", type=int, default=3)
    parser.add_argument("--rabin-max-cases", type=int, default=8,
                        help="maximum nested Rabin cases per factor; 0 means all")
    parser.add_argument("--rabin-repeats", type=int, default=3,
                        help="repetitions per Rabin checker and literal")
    parser.add_argument("--skip-kernel-factor", action="store_true")
    parser.add_argument("--skip-certificates", action="store_true")
    parser.add_argument("--skip-rabin", action="store_true")
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    if args.baseline_repeats < 1:
        parser.error("--baseline-repeats must be positive")
    if args.rabin_repeats < 1:
        parser.error("--rabin-repeats must be positive")
    if args.rabin_max_cases < 0:
        parser.error("--rabin-max-cases must be nonnegative")
    if not HEX_SERVICE.exists():
        sys.exit(f"missing {HEX_SERVICE}; run `lake build hexbz_factor_service`")
    run_environment = environment_block()

    corpus_bytes = args.corpus.read_bytes()
    corpus_sha = hashlib.sha256(corpus_bytes).hexdigest()
    selected_names = set(args.name)
    instances = []
    for line in args.corpus.read_text().splitlines():
        if not line.strip():
            continue
        instance = json.loads(line)
        if args.family and instance["family"] != args.family:
            continue
        if selected_names and instance["name"] not in selected_names:
            continue
        if args.combined_only and not instance.get("combined"):
            continue
        if args.max_degree is not None and instance["degree"] > args.max_degree:
            continue
        instances.append(instance)
    instances.sort(key=lambda row: (row["family"], row["degree"], row["name"]))
    if selected_names:
        found = {instance["name"] for instance in instances}
        missing = selected_names - found
        if missing:
            parser.error("unknown or filtered corpus names: " + ", ".join(sorted(missing)))
    if not instances:
        parser.error("selection contains no corpus inputs")

    workdir = ROOT / ".lake" / "kernel-factor-tmp"
    workdir.mkdir(parents=True, exist_ok=True)

    baselines = {}
    if not args.skip_kernel_factor:
        print("measuring ZPoly.factorize import baseline ...", file=sys.stderr)
        baselines["kernel_factor"] = import_baseline(
            KERNEL_IMPORT, args.timeout, workdir, "KernelImport", args.baseline_repeats
        )
        print(f"  {baselines['kernel_factor']/1e9:.2f}s", file=sys.stderr)
    if not args.skip_certificates or not args.skip_rabin:
        print("measuring certificate-umbrella import baseline ...", file=sys.stderr)
        baselines["certificate"] = import_baseline(
            CERTIFICATE_IMPORT, args.timeout, workdir, "CertificateImport",
            args.baseline_repeats,
        )
        print(f"  {baselines['certificate']/1e9:.2f}s", file=sys.stderr)

    service = subprocess.Popen(
        [str(HEX_SERVICE), "--entry", "factor"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,
    )

    results = []
    censored_streak = {}
    unexpected = []
    try:
        for instance_index, instance in enumerate(instances):
            family = instance["family"]
            try:
                factorization = hex_factor(instance["coeffs"], service)
            except (BrokenPipeError, OSError, json.JSONDecodeError, RuntimeError) as exc:
                unexpected.append(
                    f"{instance['name']}: compiled factor service lost: {exc}"
                )
                for remaining in instances[instance_index:]:
                    results.append({
                        "family": remaining["family"],
                        "name": remaining["name"],
                        "degree": remaining["degree"],
                        "known_irreducible": False,
                        "kernel_factor": {
                            "status": "service-lost",
                            "message": str(exc),
                        },
                        "factor_poly": {"status": "not-run"},
                        "irreducibility": {"status": "not-run"},
                        "witness_search": {"status": "not-run", "factors": []},
                        "rabin_replay": [],
                    })
                break
            if factorization is None:
                unexpected.append(f"{instance['name']}: compiled factorizer declined")
                results.append({
                    "family": family,
                    "name": instance["name"],
                    "degree": instance["degree"],
                    "known_irreducible": False,
                    "kernel_factor": {"status": "compiled-factor-decline"},
                    "factor_poly": {"status": "not-run"},
                    "irreducibility": {"status": "not-run"},
                    "witness_search": {"status": "not-run", "factors": []},
                    "rabin_replay": [],
                })
                continue

            scalar, factors = factorization
            known_irreducible = is_known_irreducible(instance, factorization)
            result = {
                "family": family,
                "name": instance["name"],
                "degree": instance["degree"],
                "known_irreducible": known_irreducible,
                "compiled_factorization": {
                    "scalar": scalar,
                    "factor_count_with_multiplicity": sum(m for _q, m in factors),
                    "distinct_factor_count": len(factors),
                },
                "rabin_replay": [],
            }

            stop_after = (args.explore_stop_after
                          if family in NON_MONOTONE_FAMILIES else 1)
            if args.skip_kernel_factor:
                result["kernel_factor"] = {"status": "not-run"}
            elif censored_streak.get(family, 0) >= stop_after:
                result["kernel_factor"] = {"status": "skipped-frontier"}
            else:
                source = gen_kernel_factor(
                    instance["coeffs"], factorization,
                    args.max_rec_depth, args.max_heartbeats,
                )
                status, elapsed, output = run_lake_lean(
                    source, args.timeout, workdir, "KernelFactor"
                )
                result["kernel_factor"] = timing_record(
                    status, elapsed, baselines["kernel_factor"], output
                )
                if status == "ok":
                    censored_streak[family] = 0
                elif status in CENSORED:
                    censored_streak[family] = censored_streak.get(family, 0) + 1
                if status == "error":
                    unexpected.append(f"{instance['name']}: kernel factor proposition failed")

            metadata = []
            if args.skip_certificates and args.skip_rabin:
                result["witness_search"] = {"status": "not-run", "factors": []}
            else:
                meta_status, metadata, meta_output = classify_witnesses(
                    factors, args.timeout, workdir
                )
                result["witness_search"] = {
                    "status": meta_status,
                    "factors": public_witnesses(factors, metadata)
                    if meta_status == "ok" else [],
                }
                if meta_status != "ok":
                    result["witness_search"]["message"] = meta_output[-1200:]
                    if meta_status == "error":
                        unexpected.append(f"{instance['name']}: witness metadata failed")

            if args.skip_certificates:
                result["factor_poly"] = {"status": "not-run"}
                result["irreducibility"] = {"status": "not-run"}
            else:
                source = gen_factor_poly(
                    instance["coeffs"], args.max_rec_depth, args.max_heartbeats
                )
                status, elapsed, output = run_lake_lean(
                    source, args.timeout, workdir, "FactorPoly"
                )
                result["factor_poly"] = timing_record(
                    status, elapsed, baselines["certificate"], output
                )
                if status == "error":
                    unexpected.append(f"{instance['name']}: factor_poly unexpected error")

                if known_irreducible:
                    source = gen_irreducibility(
                        instance["coeffs"], args.max_rec_depth, args.max_heartbeats
                    )
                    status, elapsed, output = run_lake_lean(
                        source, args.timeout, workdir, "Irreducibility"
                    )
                    result["irreducibility"] = timing_record(
                        status, elapsed, baselines["certificate"], output
                    )
                    if status == "error":
                        unexpected.append(
                            f"{instance['name']}: irreducibility unexpected error"
                        )
                else:
                    result["irreducibility"] = {"status": "not-applicable"}

            if not args.skip_rabin and metadata:
                try:
                    cases, dropped = rabin_cases(metadata, args.rabin_max_cases)
                    result["rabin_cases_dropped"] = dropped
                    result["rabin_replay"] = run_rabin_series(
                        cases, args.timeout, workdir, baselines["certificate"],
                        args.max_rec_depth, args.max_heartbeats, args.rabin_repeats,
                    )
                except RuntimeError as exc:
                    unexpected.append(f"{instance['name']}: {exc}")
                    result["rabin_replay_error"] = str(exc)
                for replay in result["rabin_replay"]:
                    for checker in ("linear", "incremental"):
                        if replay[checker]["status"] == "error":
                            unexpected.append(
                                f"{instance['name']}: {checker} Rabin checker rejected "
                                f"literal {replay['literal_sha256']}"
                            )

            results.append(result)
            statuses = (
                result["kernel_factor"]["status"],
                result["factor_poly"]["status"],
                result["irreducibility"]["status"],
            )
            witnesses = ",".join(
                witness["class"] for witness in result["witness_search"]["factors"]
            ) or "-"
            print(
                f"  {family:22s} {instance['name']:22s} deg {instance['degree']:4d}  "
                f"kernel={statuses[0]:17s} factor_poly={statuses[1]:17s} "
                f"irreducibility={statuses[2]:17s} witnesses={witnesses}",
                file=sys.stderr,
            )
    finally:
        try:
            service.stdin.close()
            service.wait(timeout=5)
        except (BrokenPipeError, subprocess.TimeoutExpired, OSError):
            service.kill()

    report = {
        "schema_version": 2,
        "env": run_environment,
        "config": {
            "mode": "kernel-factor-vs-certificates",
            "propositions": {
                "kernel_factor": (
                    "Hex.ZPoly.factorize f = <compiled Factorization> "
                    "by decide +kernel"
                ),
                "factor_poly": "Hex.ZPoly.Factored f := factor_poly f",
                "irreducibility": "Hex.ZPoly.Irreducible f := by irreducibility",
                "rabin": (
                    "identical reified literal factor/certificate checked by "
                    "Linear and LinearIncremental"
                ),
            },
            "timing_labels": {
                "total_nanos": "end-to-end fresh Lake module wall time",
                "baseline_delta_nanos": (
                    "signed total minus the matching median import baseline; "
                    "includes elaboration and kernel checking"
                ),
            },
            "imports": {
                "kernel_factor": KERNEL_IMPORT,
                "certificate": CERTIFICATE_IMPORT,
            },
            "lake_built_modules": True,
            "timeout_seconds": args.timeout,
            "max_rec_depth": args.max_rec_depth,
            "max_heartbeats": args.max_heartbeats,
            "import_baseline_nanos": baselines,
            "baseline_repeats": args.baseline_repeats,
            "rabin_max_cases_per_factor": args.rabin_max_cases,
            "rabin_repeats": args.rabin_repeats,
            "selection": {
                "family": args.family,
                "names": args.name,
                "combined_only": args.combined_only,
                "max_degree": args.max_degree,
            },
            "corpus_path": str(args.corpus.relative_to(ROOT)),
            "corpus_sha256": corpus_sha,
        },
        "results": results,
        "unexpected_errors": unexpected,
    }
    host = report["env"]["hostname"] or "host"
    gitsha = (report["env"]["git_commit"] or "nogit")[:8]
    output = args.output or (
        ROOT / "reports" / "bench-results"
        / f"hexbz-kernel-factor-{gitsha}-{host}.json"
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    try:
        shown = output.relative_to(ROOT)
    except ValueError:
        shown = output
    print(f"\nwrote {shown}", file=sys.stderr)
    print(f"sha256 {hashlib.sha256(output.read_bytes()).hexdigest()}", file=sys.stderr)
    if unexpected:
        print("unexpected errors:", file=sys.stderr)
        for item in unexpected:
            print(f"  - {item}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
