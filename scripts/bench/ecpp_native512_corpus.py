#!/usr/bin/env python3
"""Freeze subjects independently of native search; no search arm runs here."""
import argparse
import hashlib
import shutil
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--gp", default=shutil.which("gp"))
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
if not args.gp:
    parser.error("PARI/GP required; pass --gp if it is not on PATH")
GP = args.gp
DISCRIMINANTS = [3, 4, 7, 8, 11, 19, 43, 67, 163]
OUT = args.output
assert not OUT.exists(), "retain existing corpus artifacts"
report = {
    "version": "hex-native-ecpp-10636/v1",
    "generation": "UTF-8/no newline SHA512, big-endian, set bit 511, PARI nextprime/isprime; difficult coverage <= 2 kronecker(-d,n)=1",
    "gp": GP,
    "gp_version": subprocess.check_output([GP, "--version"], text=True, stderr=subprocess.STDOUT).strip(),
    "cases": [], "rejected": [], "controls": []}
seen = set()
for split in ["tuning", "holdout"]:
    for stratum, count in [("ordinary", 6), ("difficult", 2)]:
        for index in range(count):
            counter = 0
            while True:
                material = f"hex-native-ecpp-10636/v1/{split}/{stratum}/{index}/{counter}"
                digest = hashlib.sha512(material.encode("utf-8")).digest()
                start = int.from_bytes(digest, "big") | (1 << 511)
                script = f"n=nextprime({start});print(n);print(isprime(n));print(vector(9,i,kronecker(-{DISCRIMINANTS}[i],n)));quit\n"
                result = subprocess.run([GP, "-q", "-f"], input=script, text=True, capture_output=True, check=True)
                assert not result.stderr, result.stderr
                lines = result.stdout.splitlines()
                assert len(lines) == 3, result.stdout
                n = int(lines[0]); prime = int(lines[1]); symbols = json.loads(lines[2])
                assert prime == 1, n
                row = {"split": split, "stratum": stratum, "index": index, "counter": counter,
                       "sha512_input": material, "start": start, "subject": n,
                       "isprime": bool(prime), "symbols": symbols}
                reasons = []
                if n.bit_length() != 512: reasons.append("overflow")
                if n in seen: reasons.append("duplicate")
                if stratum == "difficult" and symbols.count(1) > 2: reasons.append("coverage")
                if reasons:
                    row["reasons"] = reasons; report["rejected"].append(row); counter += 1
                    continue
                seed = index if stratum == "ordinary" else index + 6
                row.update(id=f"{split}-512-{stratum}-{index}", bits=512, seed=seed)
                seen.add(n); report["cases"].append(row)
                OUT.write_text(json.dumps(report, indent=2) + "\n")
                print(row["id"], "accepted after", counter, "rejections", flush=True)
                break
original = json.loads((Path(__file__).resolve().parents[2] / "reports/ecpp/native/corpus.json").read_text())
ps = [r["subject"] for r in original["cases"] if r["bits"] == 256][:2]
for label, n in [("zero", 0), ("one", 1), ("square", ps[0] ** 2), ("product", ps[0] * ps[1])]:
    report["controls"].append(dict(id=label, subject=n, bits=n.bit_length(), seed=0, expected="no accepted certificate"))
for bits in [255, 256, 257, 511, 512, 513]:
    for label, n in [("lower", 2 ** (bits - 1)), ("upper", 2 ** bits - 1)]:
        report["controls"].append(dict(id=f"boundary-{bits}-{label}", subject=n, bits=bits, seed=0,
            expected="inputBits" if bits > 512 else "bounded outcome; no completeness promise"))
OUT.write_text(json.dumps(report, indent=2) + "\n")
