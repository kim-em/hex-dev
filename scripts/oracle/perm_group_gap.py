#!/usr/bin/env python3
"""Required GAP oracle and independent fixture checks for HexPermGroup."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys


def compose(p: list[int], q: list[int]) -> list[int]:
    """Hex left-action product: (p.comp q)(x) = p(q(x))."""
    return [p[q[i]] for i in range(len(p))]


def inverse(p: list[int]) -> list[int]:
    out = [0] * len(p)
    for i, x in enumerate(p):
        out[x] = i
    return out


def closure(n: int, generators: list[list[int]]) -> set[tuple[int, ...]]:
    ident = tuple(range(n))
    seen = {ident}
    queue = [list(ident)]
    signed = generators + [inverse(p) for p in generators]
    while queue:
        p = queue.pop(0)
        for q in signed:
            r = tuple(compose(p, q))
            if r not in seen:
                seen.add(r)
                queue.append(list(r))
    return seen


def gap_perm(p: list[int]) -> str:
    return f"PermList([{','.join(str(x + 1) for x in p)}])"


def gap_group(gens: list[list[int]]) -> str:
    return f"Group([{','.join(gap_perm(p) for p in gens)}])"


def require_fields(record: dict) -> None:
    for field in ("schema_version", "id", "operation", "degree", "generators", "status"):
        if field not in record:
            raise ValueError(f"{record.get('id', '<unknown>')}: missing {field}")
    n = record["degree"]
    for p in record["generators"]:
        if len(p) != n or sorted(p) != list(range(n)):
            raise ValueError(f"{record['id']}: malformed degree-{n} permutation {p}")


def independent_checks(record: dict) -> None:
    require_fields(record)
    n, gens, op = record["degree"], record["generators"], record["operation"]
    if op == "large-order":
        expected = 1 << len(gens)
        if str(expected) != record["order_decimal"]:
            raise ValueError(f"{record['id']}: large exact order mismatch")
        return
    if op == "limits-corruption":
        if record["producer_status"] != "limited" or record["replay_status"] != "rejected":
            raise ValueError(f"{record['id']}: incomplete result gained a mathematical answer")
        return
    group = closure(n, gens)
    if "order" in record and len(group) != record["order"]:
        raise ValueError(f"{record['id']}: order mismatch in independent closure")
    if op == "chain-cosets":
        if (tuple(record["query"]) in group) != record["member"]:
            raise ValueError(f"{record['id']}: membership mismatch")
        h = closure(n, record["subgroup_generators"])
        left = {tuple(sorted(tuple(compose(g, list(x))) for x in h)) for g in group}
        right_reps_inverted = {
            tuple(sorted(tuple(compose(inverse(g), list(x))) for x in h)) for g in group
        }
        if len(left) != record["subgroup_index"] or left != right_reps_inverted:
            raise ValueError(f"{record['id']}: left/right transversal conversion mismatch")
    elif op == "elementary":
        if compose(record["left"], record["right"]) != record["hex_product"]:
            raise ValueError(f"{record['id']}: left-action composition mismatch")
    elif op == "rank-unrank-sampling":
        if sorted(record["indices"]) != list(range(len(group))):
            raise ValueError(f"{record['id']}: supplied indices are not exhaustive")
    elif op == "products":
        if record["direct_degree"] != n + record["right_degree"]:
            raise ValueError(f"{record['id']}: direct-product degree mismatch")
        if record["wreath_degree"] != n * record["right_degree"]:
            raise ValueError(f"{record['id']}: wreath-product degree mismatch")


def gap_program(records: list[dict]) -> str:
    lines = [
        'AssertEq := function(got, want, label) if got <> want then Error(label, ": ", got, " <> ", want); fi; end;',
    ]
    for k, r in enumerate(records):
        n, op = r["degree"], r["operation"]
        lines += [f"G{k}:={gap_group(r['generators'])};", f"D{k}:=[1..{n}];"]
        if op == "chain-cosets":
            lines += [
                f'AssertEq(Size(G{k}),{r["order"]},"{r["id"]} order");',
                f'AssertEq({gap_perm(r["query"])} in G{k},{str(r["member"]).lower()},"{r["id"]} membership");',
                f'AssertEq(Set(Orbits(G{k},D{k})),[[1,2,3]],"{r["id"]} orbits");',
                f'AssertEq(Size(Stabilizer(G{k},1)),{r["stabilizer_order"]},"{r["id"]} stabilizer");',
                f"H{k}:={gap_group(r['subgroup_generators'])};",
                f'AssertEq(IsSubgroup(G{k},H{k}),true,"{r["id"]} subgroup");',
                f'AssertEq(Length(RightTransversal(G{k},H{k})),{r["subgroup_index"]},"{r["id"]} transversal");',
            ]
        elif op == "elementary":
            p, q = gap_perm(r["left"]), gap_perm(r["right"])
            # GAP acts on the right, so q*p represents Hex p.comp q.
            lines += [
                f'AssertEq(List(D{k},x->x^({q}*{p})),List({[x + 1 for x in r["hex_product"]]}),"{r["id"]} reversed product");',
                f'AssertEq(SignPerm({p}),{r["sign"]},"{r["id"]} sign");',
                f'AssertEq(SortedList(CycleLengths({p},D{k})),[1,2],"{r["id"]} cycles");',
                f'AssertEq(IsTransitive(G{k},D{k}),true,"{r["id"]} transitive");',
                f'AssertEq(IsAbelian(G{k}),false,"{r["id"]} abelian");',
                f'AssertEq(Size(ClosureGroup(Group([{p}]),{q})),6,"{r["id"]} join");',
            ]
        elif op == "actions-kernel":
            lines += [
                f"A{k}:=ActionHomomorphism(G{k},D{k},OnPoints);",
                f'AssertEq(Size(Image(A{k})),{r["image_order"]},"{r["id"]} image");',
                f'AssertEq(Size(Kernel(A{k})),{r["kernel_order"]},"{r["id"]} kernel");',
                f'AssertEq(Size(Orbit(G{k},[1,1],OnTuples)),3,"{r["id"]} tuples");',
                f'AssertEq(Size(Orbit(G{k},Set([1,2]),OnSets)),3,"{r["id"]} sets");',
            ]
        elif op == "subgroup-search":
            lines += [
                f"H{k}:={gap_group(r['subgroup_generators'])};",
                f'AssertEq(Size(Stabilizer(G{k},Set([1,2]),OnSets)),{r["set_stabilizer_order"]},"{r["id"]} set stabilizer");',
                f'AssertEq(RepresentativeAction(G{k},Set([1,2]),Set([2,3]),OnSets)=fail,false,"{r["id"]} transporter");',
                f'AssertEq(Size(Intersection(G{k},H{k})),{r["intersection_order"]},"{r["id"]} intersection");',
                f'AssertEq(Size(Centralizer(G{k},H{k})),{r["centralizer_order"]},"{r["id"]} centralizer");',
                f'AssertEq(Size(Normalizer(G{k},H{k})),{r["normalizer_order"]},"{r["id"]} normalizer");',
            ]
        elif op == "blocks":
            lines += [
                f'AssertEq(Set(List(Blocks(G{k},D{k},[1,3]),Set)),Set([[1,3],[2,4]]),"{r["id"]} blocks");',
                f'AssertEq(IsPrimitive(G{k},D{k}),false,"{r["id"]} primitive");',
                f"B{k}:=Blocks(G{k},D{k},[1,3]); BA{k}:=ActionHomomorphism(G{k},B{k},OnSets);",
                f'AssertEq(Size(Kernel(BA{k})),4,"{r["id"]} block kernel");',
            ]
        elif op == "normal-structure":
            lines += [
                f"H{k}:={gap_group(r['subgroup_generators'])};",
                f'AssertEq(IsNormal(G{k},H{k}),false,"{r["id"]} normality");',
                f'AssertEq(Size(NormalClosure(G{k},H{k})),{r["normal_closure_order"]},"{r["id"]} normal closure");',
                f'AssertEq(Size(Core(G{k},H{k})),{r["core_order"]},"{r["id"]} core");',
                f'AssertEq(Size(DerivedSubgroup(G{k})),{r["derived_order"]},"{r["id"]} derived");',
                f'AssertEq(List(DerivedSeries(G{k}),Size),{r["derived_series_orders"]},"{r["id"]} series");',
                f'AssertEq(IsSolvableGroup(G{k}),true,"{r["id"]} solvable");',
            ]
        elif op == "products":
            lines += [
                f"H{k}:={gap_group(r['right_generators'])}; DP{k}:=DirectProduct(G{k},H{k});",
                f'AssertEq(Size(DP{k}),{r["direct_order"]},"{r["id"]} direct product");',
                f'AssertEq(Size(Image(Embedding(DP{k},1))),2,"{r["id"]} embedding");',
                f'AssertEq(Size(Image(Projection(DP{k},2))),2,"{r["id"]} projection");',
                f"WP{k}:=WreathProductImprimitiveAction(G{k},H{k});",
                f'AssertEq(Size(WP{k}),{r["wreath_order"]},"{r["id"]} wreath product");',
            ]
        elif op == "large-order":
            lines += [f'AssertEq(String(Size(G{k})),"{r["order_decimal"]}","{r["id"]} exact order");']
    lines += ['Print("GAP oracle: all fixture families passed\\n");', 'QUIT_GAP(0);']
    return "\n".join(lines) + "\n"


def main() -> int:
    records = [json.loads(line) for line in sys.stdin if line.strip()]
    for record in records:
        independent_checks(record)
    gap = os.environ.get("GAP") or shutil.which("gap")
    if not gap:
        print("HexPermGroup oracle requires GAP", file=sys.stderr)
        return 1
    run = subprocess.run([gap, "-q", "--quitonbreak"], input=gap_program(records), text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        print(run.stdout, file=sys.stderr)
        return run.returncode
    print(run.stdout.strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
