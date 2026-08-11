#!/usr/bin/env python3
"""Counterbalanced per-row end-to-end comparison of two factor-service binaries.

`factor_sweep_paired.py` counterbalances whole corpus passes, which is the right
grain for a corpus verdict and too coarse for a handful of named rows: a block
takes minutes, so host drift between blocks lands on whichever arm held the
slower slot. This driver counterbalances one row at a time, so the two arms are
adjacent in wall-clock and the pairing is tight enough to resolve a few percent.

Each repeat runs both arms once; the arm that goes first alternates, so arm and
position within the repeat are not confounded. The reported statistic is the
median of the within-repeat after/before ratios, with the spread of those
ratios, not the ratio of two independently pooled medians.

Build the two service binaries first, as for ``factor_sweep_paired.py``, then::

    python3 scripts/bench/factor_row_paired.py /tmp/svc.before /tmp/svc.after \\
        "$(python3 scripts/bench/idle_core.py)" 41 sd5_x_phi11 sd7

Name at least one control row whose cascade does not reach the code under test
and whose cost matches the target rows. Two separately linked binaries differ
in code placement whether or not they differ in the measured loop, and only a
control makes that visible instead of attributing it to the change.
"""
import json, statistics, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
rows = {r["name"]: r for r in map(json.loads,
        (ROOT / "bench/corpus/hexbz-factor-corpus.jsonl").read_text().splitlines())}


class Svc:
    def __init__(self, binary, cpu):
        self.p = subprocess.Popen(["taskset", "-c", cpu, binary, "--entry", "factor"],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)

    def call(self, coeffs):
        import time
        line = json.dumps({"coeffs": coeffs}, separators=(",", ":")) + "\n"
        t = time.perf_counter_ns()
        self.p.stdin.write(line); self.p.stdin.flush()
        reply = self.p.stdout.readline()
        return json.loads(reply), time.perf_counter_ns() - t

    def kill(self):
        self.p.kill(); self.p.wait()


def degrees(reply):
    res = reply.get("result")
    return None if res is None else tuple(sorted(len(f["coeffs"]) - 1 for f in res["factors"]))


def main():
    before, after, cpu = sys.argv[1], sys.argv[2], sys.argv[3]
    repeats = int(sys.argv[4])
    names = sys.argv[5:]
    a, b = Svc(before, cpu), Svc(after, cpu)
    for n in names:
        a.call(rows[n]["coeffs"]); b.call(rows[n]["coeffs"])
    print("| row | before | after | ratio | repeat spread | agree |")
    print("|---|---:|---:|---:|---|---|")
    for n in names:
        c = rows[n]["coeffs"]
        ratios, bs, as_, degs = [], [], [], set()
        for i in range(repeats):
            if i % 2 == 0:
                rb, eb = a.call(c); ra, ea = b.call(c)
            else:
                ra, ea = b.call(c); rb, eb = a.call(c)
            ratios.append(ea / eb); bs.append(eb); as_.append(ea)
            degs.add(degrees(rb)); degs.add(degrees(ra))
        ratios.sort()
        lo = ratios[int(0.1 * (len(ratios) - 1))]
        hi = ratios[int(0.9 * (len(ratios) - 1))]
        med = statistics.median(ratios)
        f = lambda ns: f"{ns/1e6:.3f} ms"
        print(f"| `{n}` | {f(statistics.median(bs))} | {f(statistics.median(as_))} | "
              f"{med:.3f}x | {lo:.3f}x to {hi:.3f}x | "
              f"{'same' if len(degs) == 1 else 'DIFFER'} |")
    a.kill(); b.kill()


main()
