#!/usr/bin/env python3
"""Required GAP oracle and independent fixture checks for HexPermGroup."""
from __future__ import annotations

import json
import math
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
    if not gens:
        return "Group([()])"
    return f"Group([{','.join(gap_perm(p) for p in gens)}])"


def gap_value(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, list):
        return f"[{','.join(gap_value(x) for x in value)}]"
    if isinstance(value, str):
        return json.dumps(value)
    return str(value)


def cycles(p: list[int]) -> list[int]:
    seen: set[int] = set()
    lengths: list[int] = []
    for start in range(len(p)):
        if start in seen:
            continue
        x, length = start, 0
        while x not in seen:
            seen.add(x)
            length += 1
            x = p[x]
        lengths.append(length)
    return sorted(lengths)


def group_orbits(n: int, group: set[tuple[int, ...]]) -> list[list[int]]:
    remaining = set(range(n))
    result: list[list[int]] = []
    while remaining:
        start = min(remaining)
        orbit = sorted({g[start] for g in group})
        result.append(orbit)
        remaining.difference_update(orbit)
    return result


def commutator(p: list[int], q: list[int]) -> list[int]:
    return compose(p, compose(q, compose(inverse(p), inverse(q))))


def derived(n: int, group: set[tuple[int, ...]], generators: list[list[int]]) -> set[tuple[int, ...]]:
    return closure(n, [commutator(list(p), q) for p in group for q in generators])


def partition_blocks(labels: list[int]) -> list[list[int]]:
    return [
        [i + 1 for i, label in enumerate(labels) if label == root]
        for root in range(len(labels)) if labels[root] == root
    ]


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
        if len(gens) != 1 or cycles(gens[0]) != sorted(record["cycle_lengths"]):
            raise ValueError(f"{record['id']}: large cyclic presentation mismatch")
        expected = math.lcm(*record["cycle_lengths"])
        if str(expected) != record["order_decimal"]:
            raise ValueError(f"{record['id']}: large exact order mismatch")
        fixed = [i for i in range(n) if all(p[i] == i for p in gens)]
        if fixed != record["fixed_points"]:
            raise ValueError(f"{record['id']}: declared fixed points mismatch")
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
        right_inverted = {
            tuple(sorted(tuple(inverse(compose(list(x), g))) for x in h)) for g in group
        }
        emitted = {
            tuple(sorted(tuple(compose(rep, list(x))) for x in h))
            for rep in record["left_representatives"]
        }
        if len(left) != record["subgroup_index"] or left != right_inverted or emitted != left:
            raise ValueError(f"{record['id']}: left/right transversal conversion mismatch")
    elif op == "elementary":
        if compose(record["left"], record["right"]) != record["hex_product"]:
            raise ValueError(f"{record['id']}: left-action composition mismatch")
        if cycles(record["left"]) != record["cycle_type"]:
            raise ValueError(f"{record['id']}: cycle type mismatch")
    elif op == "subgroup-search":
        witness = record["transporter"]
        if record["transporter_exists"] != (witness is not None):
            raise ValueError(f"{record['id']}: transporter witness status mismatch")
        if witness is not None:
            moved = sorted(witness[x] for x in record["subset"])
            if tuple(witness) not in group or moved != sorted(record["target"]):
                raise ValueError(f"{record['id']}: invalid transporter witness")
        if record["negative_transporter_exists"]:
            raise ValueError(f"{record['id']}: impossible transporter reported")
    elif op == "rank-unrank-sampling":
        if sorted(record["indices"]) != list(range(len(group))):
            raise ValueError(f"{record['id']}: supplied indices are not exhaustive")
    elif op == "products":
        if record["direct_degree"] != n + record["right_degree"]:
            raise ValueError(f"{record['id']}: direct-product degree mismatch")
        if record["wreath_degree"] != n * record["right_degree"]:
            raise ValueError(f"{record['id']}: wreath-product degree mismatch")
    elif op == "group-corpus":
        expected_orbits = group_orbits(n, group)
        fixed = [i for i in range(n) if all(p[i] == i for p in gens)]
        if expected_orbits != record["orbits"] or fixed != record["fixed_points"]:
            raise ValueError(f"{record['id']}: orbit or fixed-point mismatch")
        if record["transitive"] != (n > 0 and len(expected_orbits) == 1):
            raise ValueError(f"{record['id']}: transitivity mismatch")
        if "reference_generators" in record and closure(n, record["reference_generators"]) != group:
            raise ValueError(f"{record['id']}: alternate presentations differ")
    elif op == "normal-series":
        orders = [len(group)]
        current, current_gens = group, gens
        while True:
            child = derived(n, current, current_gens)
            orders.append(len(child))
            if len(child) == 1 or child == current:
                break
            current = child
            current_gens = [list(p) for p in child]
        if orders != record["derived_series_orders"] or len(derived(n, group, gens)) != record["derived_order"]:
            raise ValueError(f"{record['id']}: derived-series mismatch")
        if record["solvable"] != (orders[-1] == 1):
            raise ValueError(f"{record['id']}: solvability mismatch")


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
                f'AssertEq(Set(Orbits(G{k},D{k})),Set({gap_value([[x + 1 for x in orbit] for orbit in r["orbits"]])}),"{r["id"]} orbits");',
                f'AssertEq(Size(Stabilizer(G{k},1)),{r["stabilizer_order"]},"{r["id"]} stabilizer");',
                f"S{k}:={gap_group(r['stabilizer_generators'])};",
                f'AssertEq(S{k}=Stabilizer(G{k},1),true,"{r["id"]} stabilizer subgroup");',
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
                f'AssertEq(SortedList(CycleLengths({p},D{k})),{gap_value(r["cycle_type"])},"{r["id"]} cycles");',
                f'AssertEq(IsTransitive(G{k},D{k}),{gap_value(r["transitive"])},"{r["id"]} transitive");',
                f'AssertEq(IsAbelian(G{k}),{gap_value(r["abelian"])},"{r["id"]} abelian");',
                f'AssertEq(Size(ClosureGroup(Group([{p}]),{q})),{r["join_order"]},"{r["id"]} join");',
            ]
        elif op == "actions-kernel":
            lines += [
                f"A{k}:=ActionHomomorphism(G{k},D{k},OnPoints);",
                f'AssertEq(Size(Image(A{k})),{r["image_order"]},"{r["id"]} image");',
                f'AssertEq(Size(Kernel(A{k})),{r["kernel_order"]},"{r["id"]} kernel");',
                f'AssertEq(Size(Orbit(G{k},{gap_value([x + 1 for x in r["tuple"]])},OnTuples)),{r["tuple_orbit_size"]},"{r["id"]} tuples");',
                f'AssertEq(Size(Orbit(G{k},Set({gap_value([x + 1 for x in r["subset"]])}),OnSets)),{r["subset_orbit_size"]},"{r["id"]} sets");',
                f'AssertEq(Size(Orbit(G{k},Set([]),OnSets)),{r["empty_subset_orbit_size"]},"{r["id"]} empty subset");',
                f"P{k}:={gap_value([partition_blocks(p) for p in r['partition_domain']])};",
                f"PA{k}:=ActionHomomorphism(G{k},P{k},OnSetsSets);",
                f'AssertEq(Size(Image(PA{k})),{r["partition_image_order"]},"{r["id"]} partition image");',
                f'AssertEq(Size(Kernel(PA{k})),{r["partition_kernel_order"]},"{r["id"]} partition kernel");',
            ]
        elif op == "subgroup-search":
            lines += [
                f"H{k}:={gap_group(r['subgroup_generators'])};",
                f'AssertEq(Size(Stabilizer(G{k},Set({gap_value([x + 1 for x in r["subset"]])}),OnSets)),{r["set_stabilizer_order"]},"{r["id"]} set stabilizer");',
                f'AssertEq(RepresentativeAction(G{k},Set({gap_value([x + 1 for x in r["subset"]])}),Set({gap_value([x + 1 for x in r["target"]])}),OnSets)=fail,{gap_value(not r["transporter_exists"])},"{r["id"]} transporter");',
                f'AssertEq(RepresentativeAction(G{k},Set({gap_value([x + 1 for x in r["subset"]])}),Set({gap_value([x + 1 for x in r["negative_target"]])}),OnSets)=fail,{gap_value(not r["negative_transporter_exists"])},"{r["id"]} negative transporter");',
                f'AssertEq(Size(Intersection(G{k},H{k})),{r["intersection_order"]},"{r["id"]} intersection");',
                f'AssertEq(Size(Centralizer(G{k},H{k})),{r["centralizer_order"]},"{r["id"]} centralizer");',
                f'AssertEq(Size(Normalizer(G{k},H{k})),{r["normalizer_order"]},"{r["id"]} normalizer");',
            ]
        elif op == "blocks":
            lines += [
                f'AssertEq(Set(List(Blocks(G{k},D{k},{gap_value([x + 1 for x in r["seed"]])}),Set)),Set({gap_value([[x + 1 for x in block] for block in r["blocks"]])}),"{r["id"]} blocks");',
                f'AssertEq(IsPrimitive(G{k},D{k}),{gap_value(r["primitive"])},"{r["id"]} primitive");',
                f"B{k}:=Blocks(G{k},D{k},{gap_value([x + 1 for x in r['seed']])}); BA{k}:=ActionHomomorphism(G{k},B{k},OnSets);",
                f'AssertEq(Size(Image(BA{k})),{r["block_image_order"]},"{r["id"]} block image");',
                f'AssertEq(Size(Kernel(BA{k})),{r["block_kernel_order"]},"{r["id"]} block kernel");',
            ]
        elif op == "normal-structure":
            lines += [
                f"H{k}:={gap_group(r['subgroup_generators'])};",
                f'AssertEq(IsNormal(G{k},H{k}),{gap_value(r["normal"])},"{r["id"]} normality");',
                f'AssertEq(Size(NormalClosure(G{k},H{k})),{r["normal_closure_order"]},"{r["id"]} normal closure");',
                f'AssertEq(Size(Core(G{k},H{k})),{r["core_order"]},"{r["id"]} core");',
                f'AssertEq(Size(DerivedSubgroup(G{k})),{r["derived_order"]},"{r["id"]} derived");',
                f'AssertEq(List(DerivedSeries(G{k}),Size),{r["derived_series_orders"]},"{r["id"]} series");',
                f'AssertEq(IsSolvableGroup(G{k}),{gap_value(r["solvable"])},"{r["id"]} solvable");',
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
            lines += [
                f'AssertEq(String(Size(G{k})),"{r["order_decimal"]}","{r["id"]} exact order");',
                f'AssertEq(SortedList(CycleLengths(GeneratorsOfGroup(G{k})[1],D{k})),{gap_value(sorted(r["cycle_lengths"]))},"{r["id"]} cycle lengths");',
            ]
        elif op == "group-corpus":
            lines += [
                f'AssertEq(Size(G{k}),{r["order"]},"{r["id"]} order");',
                f'AssertEq(Set(Orbits(G{k},D{k})),Set({gap_value([[x + 1 for x in orbit] for orbit in r["orbits"]])}),"{r["id"]} orbits");',
                f'AssertEq(IsTransitive(G{k},D{k}),{gap_value(r["transitive"])},"{r["id"]} transitive");',
            ]
            if "reference_generators" in r:
                lines += [
                    f"R{k}:={gap_group(r['reference_generators'])};",
                    f'AssertEq(G{k}=R{k},true,"{r["id"]} alternate presentation");',
                ]
        elif op == "normal-series":
            lines += [
                f'AssertEq(Size(G{k}),{r["order"]},"{r["id"]} order");',
                f'AssertEq(Size(DerivedSubgroup(G{k})),{r["derived_order"]},"{r["id"]} derived");',
                f"DS{k}:=DerivedSeries(G{k}); DO{k}:=List(DS{k},Size);",
                f"if Size(Last(DS{k}))>1 and DerivedSubgroup(Last(DS{k}))=Last(DS{k}) then Add(DO{k},Size(Last(DS{k}))); fi;",
                f'AssertEq(DO{k},{gap_value(r["derived_series_orders"])},"{r["id"]} series");',
                f'AssertEq(IsSolvableGroup(G{k}),{gap_value(r["solvable"])},"{r["id"]} solvable");',
            ]
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
