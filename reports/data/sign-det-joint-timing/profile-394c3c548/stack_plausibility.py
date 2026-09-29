"""Detect impossible callees below lean_nat_gcd in the recovered caller stacks."""
import argparse
import collections
import gzip
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/profile"))
from factor_sampling_profile import Symbolicator, frame_names, main_thread, stack_chain

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("profile", type=Path)
parser.add_argument("symbols", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
with gzip.open(args.profile, "rt") as stream:
    profile = json.load(stream)
thread = main_thread(profile, "hexsigndet_benc")
resolved = frame_names(profile, thread, Symbolicator(args.symbols))
by_leaf = collections.Counter()
examples = []
gcd = compiled = gmp = unexplained_gmp = 0
for stack in thread["samples"]["stack"]:
    names = [resolved[index][0] for index in stack_chain(thread, stack)]
    if "lean_nat_gcd" not in names:
        continue
    gcd += 1
    below = names[:names.index("lean_nat_gcd")]
    has_compiled = any(name.startswith(("Hex.", "Rat.", "List.")) for name in below)
    has_gmp = any(name in ("__gmpz_add", "__gmpz_mul_2exp") for name in below)
    via_constructor = any(name in ("_ZN4lean3mpzC1Em", "_ZN4lean3mpzC2Em") for name in below)
    compiled += has_compiled
    gmp += has_gmp
    unexplained_gmp += has_gmp and not via_constructor
    if has_compiled or has_gmp:
        by_leaf[names[0]] += 1
        if len(examples) < 12:
            examples.append({"leaf": names[0], "frames_below_gcd": below,
                             "compiled_callee": has_compiled, "gmp_callee": has_gmp,
                             "uint64_constructor": via_constructor})
document = {"scope": "Caller-stack plausibility; timing-window confidence is a separate check",
            "status": "checked-paths-consistent" if compiled == 0 and unexplained_gmp == 0 else "needs-investigation",
            "samples": thread["samples"]["length"], "gcd_ancestor_samples": gcd,
            "compiled_frames_below_gcd": compiled, "gmp_add_or_shift_below_gcd": gmp,
            "gmp_add_or_shift_without_uint64_constructor": unexplained_gmp,
            "inspected_paths_by_leaf": dict(by_leaf),
            "examples": examples,
            "limitation": "This checks specific call-path concerns, not every unwind edge. Lean mpz(uint64) calls GMP add and shift; those descendants are valid."}
args.output.write_text(json.dumps(document, indent=2) + "\n")
print(json.dumps({k: v for k, v in document.items() if k != "examples"}, indent=2))
