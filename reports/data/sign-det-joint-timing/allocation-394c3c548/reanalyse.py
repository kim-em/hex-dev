"""Stream retained folded stacks, distinguishing exact callbacks from helpers."""
import argparse
import collections
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("raw", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=False)
callback = re.compile(r"^lp_Hex_Hex_SignDetBench_Joint_runComparison(?:___redArg|___boxed)?$")
frames = collections.Counter()
callback_frames = collections.Counter()
variants = collections.Counter()
exact = other = rows = preparation = unplaced = 0
with (args.raw / "comparison-allocations.stacks").open() as stream:
    for line in stream:
        stack, count = line.rstrip().rsplit(" ", 1)
        count = int(count)
        names = {name for name in stack.split(";") if name}
        matched = {name for name in names if callback.fullmatch(name)}
        rows += 1
        if matched:
            exact += count
            variants.update({name: count for name in matched})
            callback_frames.update({name: count for name in names})
        else:
            other += count
            if "lp_Hex_Hex_SignDetBench_Joint_input" in names:
                preparation += count
            else:
                unplaced += count
        frames.update({name: count for name in names})
whole = (args.raw / "whole-process.txt").read_text()
total = int(re.search(r"^calls to allocation functions: (\d+)", whole, re.M)[1])
histogram = [tuple(map(int, line.split())) for line in
             (args.raw / "comparison-histogram.tsv").read_text().splitlines()]
assert sum(count for _, count in histogram) == total
summary = {"whole_process_intercepted_calls": total,
           "whole_process_requested_bytes": sum(size * count for size, count in histogram),
           "filtered_stack_calls": exact + other,
           "exact_callback_stack_calls": exact, "other_filtered_stack_calls": other,
           "other_stacks_with_preparation_frame": preparation,
           "other_stacks_without_preparation_or_callback": unplaced,
           "callback_calls_upper_bound_within_filtered_stacks": exact + unplaced,
           "folded_stack_rows": rows, "callback_frame_pattern": callback.pattern,
           "callback_frame_variants": dict(variants),
           "scope": "GMP/glibc allocation traffic; Lean object allocation is unmeasured"}
(args.output / "reanalysis.json").write_text(json.dumps(summary, indent=2) + "\n")
(args.output / "frame-allocation-counts.json").write_text(json.dumps({
    "scope": "Inclusive intercepted calls per distinct frame in substring-filtered stacks; shares overlap",
    "frames": dict(frames.most_common())}, indent=2) + "\n")
(args.output / "callback-frame-allocation-counts.json").write_text(json.dumps({
    "scope": "Inclusive intercepted calls per distinct frame in exact-callback stacks only; shares overlap",
    "frames": dict(callback_frames.most_common())}, indent=2) + "\n")
print(json.dumps(summary, indent=2))
