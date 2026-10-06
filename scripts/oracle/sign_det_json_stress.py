#!/usr/bin/env python3
"""Native JSON width/string probes, independent of the line transport.

These are capacity checks under the ordinary 8 MiB stack, not timing evidence.
The byte ceiling is exercised by a string; width probes do not assert exhaustive
coverage of all inputs below the ceiling.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import resource
import subprocess
import tempfile

from sign_det_json_bytes import expected

ROOT = Path(__file__).resolve().parents[2]


def cases(ci=False):
    if ci:
        yield "ci-string", b'"' + b"x" * (4 * 1024 * 1024) + b'"'
        yield "ci-array-width", b"[" + b"0," * 999999 + b"0]"
        yield "ci-object-width", b"{" + b'"x":0,' * 999999 + b'"x":0}'
        yield "ci-escaped-string", b'"' + b"\\n" * 500000 + b'"'
        yield "ci-nesting-limit", b"[" * 128 + b"0" + b"]" * 128
        return
    yield "string-byte-ceiling", b'"' + b"x" * (16777216 - 2) + b'"'
    yield "escaped-string", b'"' + b"\\n" * 1000000 + b'"'
    yield "array-width", b"[" + b"0," * 1999999 + b"0]"
    yield "object-width-duplicates", b"{" + b'"x":0,' * 299999 + b'"x":0}'
    yield "nesting-limit", b"[" * 128 + b"0" + b"]" * 128
    yield "integer-digit-limit", b"1" + b"0" * 4095


def stack_limit():
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if hard != resource.RLIM_INFINITY and hard < 8 * 1024 * 1024:
        raise ValueError("requires an 8 MiB hard stack allowance")
    resource.setrlimit(resource.RLIMIT_STACK, (8 * 1024 * 1024, hard))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def check_stack(executable):
    """The same non-tail call must finish with the default thread and overflow
    with the constrained main thread, so ignored runtime flags cannot pass."""
    default_env = dict(os.environ)
    default_env.pop("LEAN_MAIN_USE_THREAD", None)
    default_env.pop("LEAN_STACK_SIZE_KB", None)
    control = subprocess.run([str(executable), "--stack-canary"], capture_output=True,
                             preexec_fn=stack_limit, env=default_env)
    if control.returncode != 0 or control.stdout.strip() != b"1000000":
        raise RuntimeError("stack canary control failed: " + control.stderr.decode(errors="replace"))
    limited = subprocess.run([str(executable), "--stack-canary"], capture_output=True,
                             preexec_fn=stack_limit,
                             env=dict(os.environ, LEAN_MAIN_USE_THREAD="0", LEAN_STACK_SIZE_KB="8192"))
    if limited.returncode != -6 or b"Stack overflow" not in limited.stderr:
        raise RuntimeError(f"8 MiB stack canary did not overflow: exit {limited.returncode}")
    print("stack canary: default-thread control passes, constrained main thread overflows", flush=True)


def run_guard(executable, source):
    return subprocess.run([str(executable), "--check-file", str(source)],
                          capture_output=True, preexec_fn=stack_limit,
                          env=dict(os.environ, LEAN_MAIN_USE_THREAD="0", LEAN_STACK_SIZE_KB="8192"))


def rejection_cases():
    yield "byte-limit", b'"' + b"x" * (16777216 - 1) + b'"', "certificate byte limit exceeded"
    yield "depth-limit", b"[" * 129 + b"0" + b"]" * 129, "certificate nesting limit exceeded"
    yield "digit-limit", b"1" + b"0" * 4096, "integer token limit exceeded"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path,
                        default=ROOT / ".lake/build/bin/hexsigndet_json_bytes")
    parser.add_argument("--ci", action="store_true", help="smaller mandatory native probes")
    args = parser.parse_args()
    check_stack(args.exe)
    with tempfile.TemporaryDirectory(prefix="hex-json-stress-") as directory:
        source = Path(directory) / "source.json"
        target = Path(directory) / "printed.json"
        for name, raw in cases(args.ci):
            source.write_bytes(raw)
            target.unlink(missing_ok=True)
            completed = subprocess.run([str(args.exe), "--file", str(source), str(target)],
                                       capture_output=True, preexec_fn=stack_limit,
                          env=dict(os.environ, LEAN_MAIN_USE_THREAD="0", LEAN_STACK_SIZE_KB="8192"))
            if completed.returncode != 0:
                raise RuntimeError(f"{name}: exit {completed.returncode}: "
                                   + completed.stderr.decode("utf-8", errors="replace"))
            printed = target.read_bytes()
            if expected(raw) != expected(printed):
                raise ValueError(name + ": parsed/printed value changed")
            target_check = run_guard(args.exe, target)
            guard_message = target_check.stderr.decode("utf-8", errors="replace")
            if len(printed) > 16777216:
                if target_check.returncode == 0 or "certificate byte limit exceeded" not in guard_message:
                    raise ValueError(name + ": expanded output byte limit was not enforced")
                guard_status = "byte limit rejects output"
            elif target_check.returncode != 0:
                raise ValueError(name + ": printed output guard failed: " + guard_message)
            else:
                guard_status = "output guard accepts"
            print(f"{name}: {len(raw)} input bytes, {len(printed)} output bytes, "
                  f"{len(printed) / len(raw):.3f}x, {guard_status}, passed", flush=True)
        for name, raw, message in rejection_cases():
            source.write_bytes(raw)
            target.unlink(missing_ok=True)
            completed = subprocess.run([str(args.exe), "--file", str(source), str(target)],
                                       capture_output=True, preexec_fn=stack_limit,
                          env=dict(os.environ, LEAN_MAIN_USE_THREAD="0", LEAN_STACK_SIZE_KB="8192"))
            if (completed.returncode == 0 or message not in completed.stderr.decode("utf-8", errors="replace")
                    or target.exists()):
                raise ValueError(name + ": missing lexical rejection")
            print(name + ": rejected before parsing, passed", flush=True)


if __name__ == "__main__":
    main()
