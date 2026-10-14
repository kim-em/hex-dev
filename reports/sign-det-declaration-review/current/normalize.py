"""Reproduce the companion's reference graph using the existing audit helpers."""
import argparse
import json
import re
import subprocess
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "reports/sturm-declaration-review"))
from audit_tools import SourceIndex, reference_graph
from scripts.ci.check_benches_mathlib_free import _parse_imports
sys.path.insert(0, str(ROOT / 'scripts/bench'))
from sweep_freshness import strip_lean_comments


def require(condition, message):
    if not condition:
        raise ValueError(message)


def compiler_kind(row):
    """Recognize compiler naming conventions; fail closed on unmatched extras."""
    if row['kind'] in {'constructor', 'recursor'}:
        return row['kind']
    parts = row['name'].split('.')
    conventions = {
        'equation': r'(?:eq_\d+|eq_def|else_eq)',
        'matcher': r'(?:match_\d+(?:_\d+)*|splitter|_sparseCasesOn_\d+)',
        'proof': r'_proof_\d+(?:_\d+)*',
        'simp': r'(?:_simp_\d+(?:_\d+)*|congr_simp)',
        'recursion': r'(?:_unary|_unsafe_rec|_f|_sunfold|_arg_pusher)',
        'structure': r'(?:casesOn|recOn|_flat_ctor)',
    }
    for kind, pattern in conventions.items():
        if any(re.fullmatch(pattern, part) for part in parts):
            return kind
    raise ValueError('unaccounted attributed constant: ' + row['name'])


def source_names(path):
    """Resolve source declaration names with their explicit namespace blocks."""
    blocks, result = [], {}
    for raw_line in strip_lean_comments(path.read_text()).splitlines():
        line = raw_line.strip()
        if line == 'mutual':
            blocks.append(('mutual', ''))
            continue
        opened = re.fullmatch(r'(?:@\[expose\]\s+)?(?:public\s+)?(?:noncomputable\s+)?(?:meta\s+)?(namespace|section)(?:\s+(\S+))?', line)
        if opened:
            kind, name = opened.groups()
            require(kind != 'namespace' or name is not None,
                    'unnamed source namespace: ' + str(path))
            blocks.extend((kind, part) for part in (name.split('.') if name else ['']))
            continue
        closed = re.fullmatch(r'end(?:\s+(\S+))?\s*', line)
        if closed:
            require(bool(blocks), 'unmatched source end: ' + str(path))
            name = closed.group(1)
            if name is None:
                require(blocks[-1][1] == '', 'missing source end name: ' + str(path))
                blocks.pop()
            else:
                count = len(name.split('.'))
                require(count <= len(blocks) and
                        '.'.join(part for _, part in blocks[-count:]) == name,
                        'mismatched source end: ' + str(path))
                del blocks[-count:]
            continue
        declared = re.match(r'^(?:@\[[^\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|def|opaque|structure|inductive|abbrev|class(?:\s+(?:inductive|abbrev))?)\s+([\w.?!\']+)', line)
        if declared:
            name = declared.group(1)
            prefix = '.'.join(name for kind, name in blocks if kind == 'namespace')
            full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, (prefix, name)))
            require(name not in result, 'ambiguous source declaration: ' + name)
            result[name] = full
    return result


REFERENCE_INPUTS = (
    'HexManual/Chapters/HexRCF.lean', 'HexManual/Chapters/HexSignDet.lean',
    'HexSignDet/SPEC/hex-sign-det.md', 'HexSignDetTheory/SPEC/hex-sign-det-theory.md',
    'conformance/HexSignDetTheory/Diagnostics/Conformance.lean',
    'conformance/HexSignDetTheory/Diagnostics/RootSemantics.lean',
)


def lexical_references(downstream):
    """Match explicit qualified names; short unqualified mentions are omitted."""
    declarations = []
    for name in downstream['public_without_downstream_production_path']:
        relative = name.removeprefix('Hex.SignDet.')
        accepted = {name}
        references = []
        for path in REFERENCE_INPUTS:
            for line, text in enumerate((ROOT / path).read_text().splitlines(), 1):
                allowed = accepted | ({relative} if '/SPEC/' in path and '.' in relative else set())
                tokens = re.findall(r"(?<![\w.])[A-Za-z_]\w*(?:\.[A-Za-z_][\w?!']*)+(?![\w.])", text)
                tokens.extend(re.findall(r"info: '([^']+)' depends on axioms", text))
                for matched in sorted(set(tokens) & allowed):
                    kind = ('axiom audit' if '#print axioms' in text or 'depends on axioms:' in text else
                            'manual' if path.startswith('HexManual/') else
                            'SPEC' if '/SPEC/' in path else 'conformance')
                    references.append({'path': path, 'line': line, 'text': text.strip(),
                                       'matched_name': matched, 'kind': kind})
        declarations.append({'name': name, 'has_direct_term_reference': bool(downstream['filtered_users'][name]),
                             'references': references})
    return {'scope': 'Supplementary full-name mentions in fixed Lean inputs and namespace-qualified mentions in the two owning SignDet SPECs. Short qualified names in Lean, unqualified names and receiver notation are omitted to avoid namespace ambiguity. These are not term clients.',
            'declarations': declarations}


def reference_disposition(row):
    """The checked evidence sentence; the preceding mathematical purpose is manual."""
    if row['references']:
        ref = min(row['references'], key=lambda r: ({'manual': 0, 'SPEC': 1, 'conformance': 2, 'axiom audit': 3}[r['kind']], r['path'], r['line']))
        return f"Existing {ref['kind']} mention: [{ref['path']}:{ref['line']}](../../../{ref['path']})."
    if row['has_direct_term_reference']:
        return 'Existing term clients are in the companion/evidence graph; no matched qualified manual/SPEC mention.'
    return 'Retained as an explicit public API decision; no existing term or matched qualified manual/SPEC mention is claimed.'


def derive(directory):
    rows = json.loads((directory / "declaration-use.json").read_text())
    fields = json.loads((directory / "structure-fields.json").read_text())
    manifest = json.loads((BASE.parent / "manifest.json").read_text())
    imports = json.loads((directory / "audit-imports.json").read_text())
    index = SourceIndex()
    roles = {module: dict(index.resolve(module)) for module in sorted(imports)}
    owned = {m["path"].removesuffix(".lean").replace("/", ".") for m in manifest["modules"]}
    declared = json.loads(re.search(r'let modules := (\[[^\n]+\])', (BASE / 'audit.lean.txt').read_text()).group(1))
    require(len(declared) == len(set(declared)) and set(declared) == owned, 'capture module list differs')
    require({row['module'] for row in rows} == owned, 'attributed module coverage differs')
    handwritten = set()
    for module in manifest["modules"]:
        name = module["path"].removesuffix(".lean").replace("/", ".")
        declared_names = source_names(ROOT / module['path'])
        require(set(declared_names) == set(module['handwritten_declarations']), 'source inventory differs: ' + name)
        for declaration in module["handwritten_declarations"]:
            expected = declared_names[declaration]
            matches = [row['name'] for row in rows if row['module'] == name and row['user_name'] == expected]
            require(len(matches) == 1, (name, declaration, matches))
            handwritten.add(matches[0])
    projections = {field['projection'] for field in fields}
    extras = [row for row in rows if row['name'] not in handwritten | projections]
    origins = [{'name': row['name'], 'module': row['module'], 'kind': compiler_kind(row),
                'base_declaration': row['base_declaration'], 'base_module': row['base_module']}
               for row in extras]
    origins.sort(key=lambda row: (row['module'], row['name']))
    counts = {kind: sum(row['kind'] == kind for row in origins)
              for kind in sorted({row['kind'] for row in origins})}
    require(len(handwritten) + len(projections) + sum(counts.values()) == len(rows), 'incomplete constant accounting')
    origin_report = {'scope': 'Additional attributed constants classified by recognized compiler naming conventions and constant kinds. This is not a proof of compiler provenance. Source-written manifest declarations and field projections are accounted separately; unmatched extras are refused.',
                     'handwritten': len(handwritten), 'fields': len(projections),
                     'counts': counts, 'extra_constants': origins}
    for module, role in roles.items():
        if module.split('.')[0] == 'HexSignDetTheory' and role['category'] != 'tests/conformance/manual':
            role['category'] = 'SignDet companion production'
        elif role['category'] == 'Sturm production':
            role['category'] = 'other Hex production'
    users, live, modules, aliases = reference_graph(
        rows, handwritten, projections, roles)
    private = {name for name in handwritten if name.startswith("_private.")}
    paths = []
    for name in sorted(private):
        queue, seen, found = deque([[name]]), {name}, None
        while queue:
            chain = queue.popleft()
            if len(chain) > 1 and chain[-1] in handwritten - private:
                found = chain
                break
            for user in users.get(chain[-1], []):
                if user not in seen:
                    seen.add(user)
                    queue.append(chain + [user])
        require(found is not None, "private helper has no public path: " + name)
        paths.append({"helper": name, "path": found})
    public = handwritten - private
    downstream = {
        "scope": "Compiler-alias merged paths in the current imported environment; evidence and external packages are not production roots. Anonymous examples, automation registration and external client projects are outside this model. Alias targets outside selected modules are not inventoried.",
        "public_with_downstream_production_path": sorted(public & live),
        "public_without_downstream_production_path": sorted(public - live),
        "filtered_users": users, "user_modules": modules, "generated_aliases": aliases,
    }
    production = {}
    for file in subprocess.check_output(["git", "ls-files", "*.lean"], cwd=ROOT, text=True).splitlines():
        path = ROOT / file
        for source in index.project:
            if path.is_relative_to(source):
                name = ".".join(path.relative_to(source).with_suffix("").parts)
                if not name.startswith("Hex"):
                    continue
                role = index.resolve(name)
                if role["path"] == file and role["category"] in {
                        "Sturm production", "SignDet companion production",
                        "other Hex production", "other root-package production"}:
                    production[name] = file
    cache = {}

    def reaches(name, visiting=frozenset()):
        if name.split(".")[0] in {"HexSignDet", "HexSignDetTheory"}:
            return True
        if name in cache:
            return cache[name]
        if name in visiting:
            return False
        role = index.resolve(name)
        cache[name] = role["path"] is not None and any(
            reaches(parent, visiting | {name}) for parent in _parse_imports(ROOT / role["path"]))
        return cache[name]

    required = {name: path for name, path in production.items() if reaches(name)}
    missing = {name: path for name, path in required.items() if name not in roles}
    require(not missing, ("missing production imports", missing))
    coverage = {
        "scope": "All tracked Hex production modules resolved with the existing source-role index and import parser, following transitive imports to either SignDet module root. Evidence modules and external projects are outside this production coverage model.",
        "production_modules": len(production), "required_modules": len(required),
        "covered_modules": dict(sorted(required.items())), "missing_modules": missing,
    }
    rows.sort(key=lambda row: (row["module"], row["name"]))
    for row in rows:
        row["users"].sort()
        row["axioms"].sort()
    fields.sort(key=lambda row: (row["structure"], row["field"]))
    return {"declaration-use.json": rows, "structure-fields.json": fields,
            "module-roles.json": roles, "downstream-use.json": downstream,
            "helper-paths.json": paths, "production-import-coverage.json": coverage,
            "generated-origins.json": origin_report,
            "source-references.json": lexical_references(downstream)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=BASE)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in derive(args.directory).items():
        expected = json.dumps(value, indent=2, sort_keys=True) + "\n"
        if args.check:
            require((args.directory / name).read_text() == expected, "derived artifact differs: " + name)
        else:
            (args.directory / name).write_text(expected)
    print("Companion reference graph, helper paths and production coverage verified.")


if __name__ == "__main__":
    main()
