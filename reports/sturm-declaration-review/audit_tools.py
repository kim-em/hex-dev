"""Resolve source roles and collapse generated aliases for the Sturm audit."""
if not __debug__:
    raise RuntimeError("The Sturm audit requires assertions; run Python without -O or PYTHONOPTIMIZE")

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.ci.check_benches_mathlib_free import _configured_source_roots, _lean_lib_source_dirs, _parse_imports
sys.path.insert(0, str(ROOT / 'scripts/bench'))
from sweep_freshness import lakefile_blocks, strip_lean_comments


def family_test_modules(lakefile):
    """Read literal test globs for the four real-closure family pairs.

    Unsupported glob expressions refuse classification rather than silently
    treating a new fixture as a production client.
    """
    modules = set()
    families = ('HexSturm', 'HexSignDet', 'HexOrderedFn', 'HexRealClosure')
    blocks = lakefile_blocks(lakefile.read_text())
    if 'command uncertain' in blocks:
        raise ValueError('uncertain Lake configuration cannot classify test evidence')
    for key, body in blocks.items():
        if not key.startswith('lean_lib '):
            continue
        name = key.removeprefix('lean_lib ')
        if not name.endswith('Tests') or not name.startswith(families):
            continue
        body = strip_lean_comments(body)
        match = re.search(r'\bglobs\s*:=\s*#\[([^\]]*)\](.*)', body, re.DOTALL)
        if match is None:
            raise ValueError('test target requires literal module globs: ' + name)
        suffix = match.group(2).strip()
        if suffix not in ('', '.map Glob.one'):
            raise ValueError('unsupported test glob suffix: ' + name + ': ' + suffix)
        entries = match.group(1).split(',')
        for entry in entries:
            entry = entry.strip()
            if not entry:
                continue
            module = re.fullmatch(r'(?:\.one\s+|Glob\.one\s+)?`([A-Za-z_][\w.]*)', entry)
            if module is None:
                raise ValueError('unsupported test glob: ' + name + ': ' + entry)
            modules.add(module.group(1))
    return modules


def disposition_rows(text):
    """Read one contiguous Markdown table, rejecting disconnected API rows."""
    lines = text.splitlines()
    row_indices = [i for i, line in enumerate(lines) if line.startswith('| `')]
    assert row_indices, 'missing API disposition table'
    first, last = row_indices[0], row_indices[-1]
    assert first >= 2 and lines[first - 2] == (
        '| Declaration | Reference clients after compiler-alias merging | Disposition |')
    assert lines[first - 1] == '| --- | --- | --- |'
    assert row_indices == list(range(first, last + 1)), 'disconnected API disposition rows'
    rows = [re.fullmatch(r'\| `([^`]+)` \| ([^|]+) \| ([^|]+) \|', line)
            for line in lines[first:last + 1]]
    assert all(rows), 'malformed API disposition row'
    return [row.groups() for row in rows]


class SourceIndex:
    def __init__(self):
        self.cache = {}
        self.test_modules = family_test_modules(ROOT / 'lakefile.lean')
        self.project = list(dict.fromkeys([ROOT] + [ROOT / path
            for path in _lean_lib_source_dirs(ROOT / 'lakefile.lean')]))
        self.packages = ROOT / '.lake/packages'
        self.external = [path for path in _configured_source_roots(ROOT)
                         if path not in self.project]
        self.names = {entry['name'].strip('«»') for entry in
                      json.loads((ROOT / 'lake-manifest.json').read_text())['packages']}
        prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                             cwd=ROOT, text=True).strip())
        self.toolchain = [prefix / 'src/lean', prefix / 'src/lean/lake']

    def resolve(self, module):
        if module not in self.cache:
            self.cache[module] = self._resolve(module)
        return self.cache[module]

    def _resolve(self, module):
        relative = Path(*module.split('.')).with_suffix('.lean')
        local = list(dict.fromkeys(root / relative for root in self.project
                                   if (root / relative).is_file()))
        assert len(local) <= 1, (module, 'ambiguous root-package sources', local)
        if local:
            path = local[0].relative_to(ROOT).as_posix()
            parts = Path(path).parts
            evidence = parts[0] in {'bench', 'conformance', 'examples', 'experiments', 'HexManual'} or any(
                part in {'Tests', 'Fixtures', 'Diagnostics', 'ProofProbe', 'DepthThree'}
                for part in parts) or Path(path).stem.endswith(('Tests', 'Conformance', 'Examples'))
            owner = module.split('.')[0]
            evidence = evidence or owner in {'HexManual', 'RealClosureConsumer'} or (
                module in {'HexRealClosure.TrivialChecks', 'HexOrderedFnTheory.LiouvilleRun'}
                or module in self.test_modules)
            category = 'tests/conformance/manual' if evidence else (
                'Sturm production' if owner in {'HexSturm', 'HexSturmMathlib'}
                else 'other Hex production' if owner.startswith('Hex') else 'other root-package production')
            return {'path': path, 'category': category, 'package': 'root'}
        matches = []
        for root in self.external:
            candidate = root / relative
            if candidate.is_file():
                package = candidate.relative_to(self.packages).parts[0]
                assert package in self.names, (module, 'unknown external package', package)
                matches.append((candidate, package))
        for root in self.toolchain:
            candidate = root / relative
            if candidate.is_file():
                matches.append((candidate, 'Lean toolchain'))
        matches = list(dict.fromkeys(matches))
        assert len(matches) == 1, (module, 'unresolved or ambiguous dependency source', matches)
        candidate, package = matches[0]
        return {'path': None, 'category': 'external dependency', 'package': package}


def reference_graph(rows, handwritten, fields, roles):
    """Merge compiler aliases with their base, preserving genuine source methods."""
    selected = {row['name'] for row in rows}
    bases = {}
    modules = {}
    compiler_name = re.compile(
        r'(?:^|\.)(?:_?eq_\d+|_?match_\d+|_(?:proof|simp)_\d+(?:_\d+)*|congr_simp|eq_def|eq_unfold|induct|induct_unfolding|mutual_induct|fun_cases|fun_cases_unfolding)(?:\.|$)')

    def register(name, module, base):
        assert name not in modules or modules[name] == module, (name, modules.get(name), module)
        modules[name] = module
        if base['declaration'] is not None:
            parent = base['declaration']
            assert parent not in modules or modules[parent] == base['module'], parent
            modules[parent] = base['module']
            if name not in handwritten | fields and (name in selected or compiler_name.search(name)):
                assert name not in bases or bases[name] == parent, name
                bases[name] = parent

    for row in rows:
        register(row['name'], row['module'], {'declaration': row['base_declaration'], 'module': row['base_module']})
        for user, module in row['user_modules'].items():
            register(user, module, row['user_bases'][user])

    def canonical(name):
        seen = set()
        while name in bases:
            assert name not in seen, ('generated-base cycle', name)
            seen.add(name)
            name = bases[name]
        return name

    users = {}
    for row in rows:
        target = canonical(row['name'])
        users.setdefault(target, set())
        for user in row['users']:
            client = canonical(user)
            if client != target:
                users[target].add(client)
    live = {target for target, clients in users.items() if any(
        roles[modules[client]]['category'] in {'other Hex production', 'other root-package production'}
        for client in clients)}
    changed = True
    while changed:
        previous = set(live)
        live.update(target for target, clients in users.items() if any(client in live for client in clients))
        changed = live != previous
    return {name: sorted(clients) for name, clients in users.items()}, live, modules, {
        name: canonical(name) for name in sorted(bases)}


def client_status(name, downstream, roles):
    clients = downstream['filtered_users'][name]
    if not clients:
        return 'None'
    categories = {roles[downstream['user_modules'][client]]['category'] for client in clients}
    assert categories <= {'Sturm production', 'tests/conformance/manual', 'external dependency'}, (name, categories)
    return 'Pair/evidence/dependency references only' if 'external dependency' in categories else 'Pair declarations and/or evidence only'


def production_coverage(imported, index):
    """Check tracked Hex production modules' root-package transitive imports."""
    production = {}
    files = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines()
    for file in files:
        path = ROOT / file
        for source in index.project:
            if path.is_relative_to(source):
                name = '.'.join(path.relative_to(source).with_suffix('').parts)
                if not name.startswith('Hex'):
                    continue
                role = index.resolve(name)
                if role['path'] == file and role['category'] in {
                        'Sturm production', 'other Hex production', 'other root-package production'}:
                    production[name] = file
    cache = {}

    def reaches_pair(name, visiting=frozenset()):
        if name.split('.')[0] in {'HexSturm', 'HexSturmMathlib'}:
            return True
        if name in cache:
            return cache[name]
        if name in visiting:
            return False
        role = index.resolve(name)
        if role['path'] is None:
            cache[name] = False
            return False
        imports = _parse_imports(ROOT / role['path'])
        answer = any(reaches_pair(parent, visiting | {name}) for parent in imports)
        cache[name] = answer
        return answer

    required = {name: path for name, path in production.items() if reaches_pair(name)}
    return {
        'scope': 'All tracked Hex production modules resolved through root-package source roots, following root-package imports to either Sturm module root. External packages are leaves. This is import coverage, not runtime or compiled-use evidence; evidence modules and external client projects are outside the production completeness claim. TrivialChecks is an explicit executable-test role.',
        'production_modules': len(production),
        'required_modules': len(required),
        'missing_modules': {name: path for name, path in sorted(required.items()) if name not in imported},
        'covered_modules': {name: path for name, path in sorted(required.items()) if name in imported},
    }
