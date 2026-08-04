#!/usr/bin/env python3
"""Offline replay of prime-planning policies over recorded per-candidate costs
(issue #9156).

`factor_phase_profile.py` records, at every good prime in a bounded prefix of the
hot-path candidate list, what each way of learning that prime's modular degree
pattern costs (`scouts`) and what stopping the walk there costs downstream
(`counterfactuals`). This driver measures nothing. It replays candidate policies
over those recorded costs, so the comparison between policies does not depend on
what the machine was doing when each row was measured, and so a policy can be
priced before it is written into the planner.

A policy's price on one instance is the sum of

* the good-prime test at every candidate it examines,
* the bounded scout at every candidate it scouts,
* the full Berlekamp split at every candidate it splits, and
* the Hensel lift and recombination at the candidate it selects.

Two limitations are inherent to a replay and are reported rather than hidden.
The recorded bounded scout is priced at one fixed target -- the first good
prime's width -- so a policy that tightens its target sooner is charged the
looser price. And the counterfactual downstream is recorded only for the fixed
comparison set (the first good prime plus, when that image is wide, the next
two); a policy that selects outside that set cannot be priced, and the
`unpriced` column counts those rows instead of dropping them silently.

The policies:

* **first** -- split the first good prime and use it.
* **fixed** -- the pre-#9128 rule: split the first good prime; if its image has
  more than `FIXED_WIDTH` local factors, split the next two good primes as well,
  and take the best of the three by the downstream score.
* **minwidth** -- the same three splits, choosing the narrowest image. A degree
  cost model with nothing else in it.
* **maxfield** -- the same three splits, choosing the largest prime, that is the
  smallest Hensel precision. A field-size cost model with nothing else in it.
* **scout** -- the #9128 rule: split the first good prime, and if its image has
  more than `FIXED_WIDTH` local factors, scout up to `FUEL` further good primes,
  stopping early on a scouted image inside the same width gate.
* **voi** -- the rule this PR lands: scout while `scoutPays` says the plan in
  hand still has enough recombination work left to repay another observation.
* **reachable** -- the floor a *discovering* policy can reach: something has to
  be split before anything is known, and the prime finally used has to be split
  too, so the least any walk can pay is the good-prime tests it passes, the first
  split, and -- when the winner is not the first good prime -- the winner's
  split. No scouting, no rejected splits.
* **oracle** -- the floor the issue names: one split at the cheapest candidate
  and its downstream. Unreachable by any policy, because it names the winner
  without paying to discover it.

Example::

    python3 scripts/bench/prime_policy_replay.py \\
        reports/bench-results/hexbz-phase-profile-<commit>-<host>.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

# The pre-scout fixed rule's constants, pinned here so the historical policy
# stays replayable however the planner evolves.
FIXED_WIDTH = 8
FUEL = 2

# `Hex.scoutRoundCost` and `Hex.splitColumnCost`: the cost of one bounded-scout
# and one Berlekamp-split word operation, in recombination word operations.
SCOUT_ROUND_COST = 12
SPLIT_COLUMN_COST = 3

# `Hex.hotPathCandidates` is every prime from 3 through 499.
CANDIDATE_HI = 499


def hot_path_primes(hi: int = CANDIDATE_HI) -> list:
    """The planner's candidate primes, in the order it walks them."""
    sieve = [True] * (hi + 1)
    for i in range(2, int(hi ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = [False] * len(sieve[i * i::i])
    return [p for p in range(3, hi + 1) if sieve[p]]


def fmt(nanos) -> str:
    if nanos is None:
        return "--"
    n = float(nanos)
    if n >= 1e9:
        return f"{n / 1e9:.3f}s"
    if n >= 1e6:
        return f"{n / 1e6:.3f}ms"
    if n >= 1e3:
        return f"{n / 1e3:.3f}us"
    return f"{n:.0f}ns"


def subset_cost(width: int) -> int:
    """`Hex.directSubsetCost`: candidates a complete head-forced search visits."""
    return 0 if width == 0 else 2 ** (width - 1)


def reachable_proper_count(degrees, n: int) -> int:
    """`Hex.reachableProperCount` of `Hex.directDegreeBits`."""
    bits = [False] * (n + 1)
    bits[0] = True
    for d in degrees:
        for i in range(n, d - 1, -1):
            if bits[i - d]:
                bits[i] = True
    return sum(1 for i in range(1, n) if bits[i])


def precision(bound: int, p: int) -> int:
    """`Hex.precisionForCoeffBound`: least `a` with `p ^ a >= 2 * bound + 1`."""
    target = 2 * bound + 1
    a, power = 0, 1
    while power < target:
        a += 1
        power *= p
    return a


def lift_words(bound: int, p: int) -> int:
    """`Hex.liftWords`: machine words in the Hensel modulus at `p`."""
    return max(1, (precision(bound, p) * p.bit_length() + 63) // 64)


def score(bound: int, n: int, p: int, degrees) -> tuple:
    """`Hex.directDegreeScore`, which a smaller tuple wins."""
    return (subset_cost(len(degrees)),
            reachable_proper_count(degrees, n),
            precision(bound, p),
            p)


def scout_pays(bound: int, n: int, inc: dict, q: int, fuel: int) -> bool:
    """`Hex.scoutPays`: can one more modular observation still pay for itself?"""
    return (q.bit_length() *
            (SCOUT_ROUND_COST * fuel * max(inc["degrees"], default=0) +
             SPLIT_COLUMN_COST * n)
            < subset_cost(len(inc["degrees"])) * lift_words(bound, inc["prime"]))


def instances(record: dict) -> list:
    """Join the scout and counterfactual sections into one per-instance view."""
    scouts = {r["name"]: r["plan"] for r in record.get("scouts", []) if r["plan"]}
    counter = {r["name"]: r["plan"]
               for r in record.get("counterfactuals", []) if r["plan"]}
    out = []
    for name, plan in scouts.items():
        cf = counter.get(name) or {}
        down = {row["prime"]: row for row in (cf.get("candidates") or [])}
        candidates = []
        for row in plan.get("candidates") or []:
            if row.get("zeroModularImage"):
                continue
            degrees = row.get("splitDegrees") or []
            d = down.get(row["prime"])
            candidates.append({
                "prime": row["prime"],
                "degrees": degrees,
                "good_prime_test": row["goodPrimeTest"]["nanos"],
                "bounded_scout": row["boundedScout"]["nanos"],
                "full_split": row["fullSplit"]["nanos"],
                "downstream": None if d is None else d["downstreamNanos"],
                "recombination":
                    None if d is None else d["recombination"]["nanos"],
                "nodes": None if d is None else d["stages"]["nodes"],
            })
        if not candidates:
            continue
        out.append({
            "name": name,
            "degree": plan["degree"],
            "coeff_bound": cf.get("coeffBound"),
            "selected_prime": plan.get("selectedPrime"),
            "candidates": candidates,
        })
    return out


class Walk:
    """Accounting for one policy's pass over one instance's candidates."""

    def __init__(self, inst):
        self.inst = inst
        self.nanos = 0
        self.splits = 0
        self.scouts = 0
        self.examined = 0

    def examine(self, cand):
        self.nanos += cand["good_prime_test"]
        self.examined += 1

    def split(self, cand):
        self.nanos += cand["full_split"]
        self.splits += 1

    def scout(self, cand):
        self.nanos += cand["bounded_scout"]
        self.scouts += 1

    def finish(self, cand):
        return {
            "prime": cand["prime"],
            "modular_nanos": self.nanos,
            "downstream_nanos": cand["downstream"],
            "total_nanos": (None if cand["downstream"] is None
                            else self.nanos + cand["downstream"]),
            "splits": self.splits,
            "scouts": self.scouts,
            "examined": self.examined,
        }


def policy_first(inst):
    w = Walk(inst)
    head = inst["candidates"][0]
    w.examine(head)
    w.split(head)
    return w.finish(head)


def _split_set(inst):
    """The fixed rule's retained set: the head, plus the next two if it is wide."""
    cands = inst["candidates"]
    if len(cands[0]["degrees"]) <= FIXED_WIDTH:
        return cands[:1]
    return cands[:1 + FUEL]


def _split_all(inst, choose):
    w = Walk(inst)
    retained = _split_set(inst)
    for cand in retained:
        w.examine(cand)
        w.split(cand)
    return w.finish(choose(retained))


def policy_fixed(inst):
    bound, n = inst["coeff_bound"], inst["degree"]
    return _split_all(inst, lambda rs: min(
        rs, key=lambda c: score(bound, n, c["prime"], c["degrees"])))


def policy_minwidth(inst):
    return _split_all(inst, lambda rs: min(
        rs, key=lambda c: (len(c["degrees"]), c["prime"])))


def policy_maxfield(inst):
    return _split_all(inst, lambda rs: max(rs, key=lambda c: c["prime"]))


def policy_scout(inst):
    """The #9128 rule: a fixed width gate on the first prime and on each scout."""
    bound, n = inst["coeff_bound"], inst["degree"]
    cands = inst["candidates"]
    w = Walk(inst)
    head = cands[0]
    w.examine(head)
    w.split(head)
    if len(head["degrees"]) <= FIXED_WIDTH:
        return w.finish(head)
    inc = head
    best = None
    fuel = FUEL
    for cand in cands[1:]:
        if fuel == 0:
            break
        w.examine(cand)
        w.scout(cand)
        fuel -= 1
        if score(bound, n, cand["prime"], cand["degrees"]) < \
                score(bound, n, inc["prime"], inc["degrees"]):
            inc, best = cand, cand
            if len(cand["degrees"]) <= FIXED_WIDTH:
                break
    if best is not None:
        w.split(best)
        return w.finish(best)
    return w.finish(head)


def policy_voi(inst):
    """This PR's rule: scout while `scoutPays` allows another observation."""
    bound, n = inst["coeff_bound"], inst["degree"]
    cands = inst["candidates"]
    good = {c["prime"]: c for c in cands}
    horizon = cands[-1]["prime"]
    w = Walk(inst)
    head = cands[0]
    w.examine(head)
    w.split(head)
    inc, best = head, None
    fuel = FUEL
    truncated = False
    for q in hot_path_primes():
        if fuel == 0 or q <= head["prime"]:
            continue
        if not scout_pays(bound, n, inc, q, fuel):
            break
        if q > horizon:
            # The record prices a bounded prefix of the candidate list; a walk
            # that wants to look past it is reported, not guessed at.
            truncated = True
            break
        cand = good.get(q)
        if cand is None:
            continue                    # a bad prime: no scout, no fuel spent
        w.examine(cand)
        w.scout(cand)
        fuel -= 1
        if score(bound, n, cand["prime"], cand["degrees"]) < \
                score(bound, n, inc["prime"], inc["degrees"]):
            inc, best = cand, cand
    if best is not None:
        w.split(best)
        out = w.finish(best)
    else:
        out = w.finish(head)
    out["truncated"] = truncated
    return out


def _priced(inst):
    return [c for c in inst["candidates"] if c["downstream"] is not None]


def policy_reachable(inst):
    """Floor for a policy that must split to learn and must split what it uses."""
    cands = inst["candidates"]
    priced = _priced(inst)
    winner = min(priced, key=lambda c: c["downstream"])
    w = Walk(inst)
    for cand in cands:
        w.examine(cand)
        if cand["prime"] == winner["prime"]:
            break
    w.split(cands[0])
    if winner["prime"] != cands[0]["prime"]:
        w.split(winner)
    return w.finish(winner)


def policy_oracle(inst):
    """Floor that names the winner without paying to discover it."""
    cands = inst["candidates"]
    winner = min(_priced(inst), key=lambda c: c["downstream"])
    w = Walk(inst)
    for cand in cands:
        w.examine(cand)
        if cand["prime"] == winner["prime"]:
            break
    w.split(winner)
    return w.finish(winner)


POLICIES = [
    ("first", policy_first),
    ("fixed", policy_fixed),
    ("minwidth", policy_minwidth),
    ("maxfield", policy_maxfield),
    ("scout", policy_scout),
    ("voi", policy_voi),
    ("reachable", policy_reachable),
    ("oracle", policy_oracle),
]


def replay(record: dict) -> dict:
    rows = []
    for inst in instances(record):
        if inst["coeff_bound"] is None or not _priced(inst):
            continue
        rows.append({"name": inst["name"], "degree": inst["degree"],
                     "selected_prime": inst["selected_prime"],
                     "policies": {name: fn(inst) for name, fn in POLICIES}})
    return {"rows": rows}


def print_table(result: dict) -> None:
    rows = result["rows"]
    names = [n for n, _ in POLICIES]
    header = " | ".join(names)
    print("### Offline policy replay\n")
    print(f"| instance | {header} | primes (first/fixed/scout/voi/oracle) |")
    print("|---" + "|---:" * len(names) + "|---|")
    totals = {n: 0 for n in names}
    unpriced = {n: 0 for n in names}
    for row in rows:
        cells = []
        for n in names:
            r = row["policies"][n]
            if r["total_nanos"] is None:
                unpriced[n] += 1
                cells.append("--")
            else:
                totals[n] += r["total_nanos"]
                cells.append(fmt(r["total_nanos"]))
        primes = "/".join(str(row["policies"][n]["prime"])
                          for n in ("first", "fixed", "scout", "voi", "oracle"))
        print(f"| `{row['name']}` | " + " | ".join(cells) + f" | {primes} |")
    print("| **aggregate** | " +
          " | ".join(f"**{fmt(totals[n])}**" for n in names) + " | |")
    for n in names:
        if unpriced[n]:
            print(f"\n{unpriced[n]} row(s) unpriced under `{n}`: it selected a "
                  f"prime outside the recorded comparison set.")
    truncated = [r["name"] for r in rows if r["policies"]["voi"].get("truncated")]
    if truncated:
        print(f"\n`voi` wanted to look past the recorded candidate prefix on: "
              f"{', '.join(truncated)}.")
    changed = [r for r in rows
               if r["policies"]["voi"]["prime"] != r["policies"]["scout"]["prime"]
               or r["policies"]["voi"]["splits"] !=
               r["policies"]["scout"]["splits"]
               or r["policies"]["voi"]["scouts"] !=
               r["policies"]["scout"]["scouts"]]
    print(f"\n`voi` differs from `scout` on {len(changed)} of {len(rows)} rows:")
    for r in changed:
        v, s = r["policies"]["voi"], r["policies"]["scout"]
        print(f"* `{r['name']}`: prime {s['prime']} -> {v['prime']}, "
              f"{s['splits']} split(s) and {s['scouts']} scout(s) -> "
              f"{v['splits']} and {v['scouts']}, "
              f"{fmt(s['total_nanos'])} -> {fmt(v['total_nanos'])}")


def print_agreement(record: dict, result: dict, policy: str) -> int:
    """Check a replayed policy against the prime the recorded binary selected."""
    bad = [r for r in result["rows"]
           if r["selected_prime"] is not None
           and r["policies"][policy]["prime"] != r["selected_prime"]]
    total = len(result["rows"])
    print(f"\n`{policy}` reproduces the recorded binary's selected prime on "
          f"{total - len(bad)} of {total} rows.")
    for r in bad:
        print(f"* `{r['name']}`: replay {r['policies'][policy]['prime']}, "
              f"binary {r['selected_prime']}")
    return len(bad)


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("record", type=Path,
                   help="a hexbz-phase-profile record with scout and "
                        "counterfactual sections")
    p.add_argument("--agrees-with", default=None,
                   help="policy whose replayed selection must match the prime "
                        "the recorded binary selected (exit 1 if it does not)")
    p.add_argument("--output", type=Path, default=None,
                   help="also write the replay as JSON")
    args = p.parse_args()

    record = json.loads(args.record.read_text())
    result = replay(record)
    if not result["rows"]:
        raise SystemExit("no instance in this record carries both a scout and a "
                         "counterfactual section")
    print_table(result)
    bad = 0
    if args.agrees_with is not None:
        bad = print_agreement(record, result, args.agrees_with)
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(f"\nwrote {args.output}", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
