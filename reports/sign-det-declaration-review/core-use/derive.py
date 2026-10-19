"""Derive the core-use graph with the existing source-role and alias helpers."""
from collections import deque
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location(
    'core_use_existing_helpers', BASE.parent / 'current/normalize.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_source_forms(path):
    """Refuse declaration forms outside the shared source parser's grammar."""
    for line in helpers.strip_lean_comments(path.read_text()).splitlines():
        line = line.strip()
        declaration = re.match(
            r'^(?:@\[[^\n]+\]\s*)?'
            r'((?:(?:private|protected|noncomputable|partial|public|unsafe|meta)\s+)*)'
            r'(?:theorem|def|opaque|structure|inductive|abbrev|class)\s+', line)
        if declaration:
            require(not ({'partial', 'public', 'unsafe', 'meta'} &
                         set(declaration.group(1).split())),
                    'unsupported source declaration form: ' + str(path))
        require(not re.match(
            r'^(?:@\[[^\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
            r'instance\s+[\w.\']+', line),
            'named instance requires explicit inventory: ' + str(path))


def evidence_scope():
    """Check the explicit evidence selection and standalone-entry exclusions."""
    scope = json.loads((BASE / 'evidence-scope.json').read_text())
    folders = ['conformance/HexSignDet', 'bench/HexSignDet',
               'conformance/HexRCF/SelectedRoot', 'conformance/HexRealClosureTheory',
               'experiments/KernelReplay']
    require(scope['folders'] == folders, 'evidence source scope differs')
    actual = {}
    for folder in folders:
        for path in (ROOT / folder).rglob('*.lean'):
            module = '.'.join(path.relative_to(ROOT / folder.split('/')[0])
                              .with_suffix('').parts)
            actual[module] = str(path.relative_to(ROOT))
    required = scope['required_modules']
    excluded = scope['excluded_entry_points']
    require(not set(required) & set(excluded), 'overlapping evidence selection')
    require(set(actual) == set(required) | set(excluded), 'evidence files differ')
    require(all(actual[name] == path for name, path in required.items()),
            'evidence source path differs')
    for name, row in excluded.items():
        require(actual[name] == row['path'] and bool(row['reason']),
                'unexplained evidence exclusion: ' + name)
    return scope


def derive(directory):
    rows = json.loads((directory / 'declaration-use.json').read_text())
    fields = json.loads((directory / 'structure-fields.json').read_text())
    imports = json.loads((directory / 'audit-imports.json').read_text())
    inputs = json.loads((directory / 'inputs.json').read_text())
    for name, expected in inputs['inputs'].items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                'current capture source differs: ' + name)
    require(hashlib.sha256((BASE / 'audit.lean.txt').read_bytes()).hexdigest() ==
            inputs['producer_sha256'], 'capture producer differs')
    scope = evidence_scope()
    require(set(scope['required_modules']) <= set(imports), 'missing selected evidence imports')
    owned = set(inputs['modules'])
    declared = json.loads(re.search(r'let modules := (\[[^\n]+\])',
                                   (BASE / 'audit.lean.txt').read_text()).group(1))
    require(len(declared) == len(set(declared)) and set(declared) == owned,
            'producer module selection differs')
    require({row['module'] for row in rows} == owned, 'attributed module coverage differs')
    handwritten = {}
    for path in sorted((ROOT / 'HexSignDet').rglob('*.lean')):
        check_source_forms(path)
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        for relative, full in helpers.source_names(path).items():
            matches = [row for row in rows
                       if row['module'] == module and row['user_name'] == full]
            require(len(matches) == 1, 'source declaration missing/ambiguous: ' + full)
            name = matches[0]['name']
            require(name not in handwritten, 'duplicate source declaration: ' + name)
            handwritten[name] = {'path': str(path.relative_to(ROOT)),
                                 'relative': relative, 'public_name': full}
    projections = {field['projection'] for field in fields}
    additional = sorted(
        ({key: row[key] for key in ('name', 'module', 'kind', 'base_declaration', 'base_module')}
         for row in rows if row['name'] not in set(handwritten) | projections),
        key=lambda row: row['name'])
    require(additional == json.loads((directory / 'additional-constants.json').read_text()),
            'additional constant inventory differs')
    require(len(handwritten) + len(projections) + len(additional) == len(rows),
            'incomplete constant accounting')
    index = helpers.SourceIndex()
    roles = {name: dict(index.resolve(name)) for name in imports}
    for module, role in roles.items():
        if module in owned:
            role['category'] = 'SignDet core production'
        elif role['category'] == 'Sturm production':
            role['category'] = 'other Hex production'
    users, live, modules, aliases = helpers.reference_graph(
        rows, set(handwritten), projections, roles)
    private = {name for name in handwritten if name.startswith('_private.')}
    paths = []
    for name in sorted(private):
        queue, seen, found = deque([[name]]), {name}, None
        while queue:
            chain = queue.popleft()
            if len(chain) > 1 and chain[-1] in set(handwritten) - private:
                found = chain
                break
            for client in users.get(chain[-1], []):
                if client not in seen:
                    seen.add(client)
                    queue.append(chain + [client])
        require(found is not None, 'private helper has no public path: ' + name)
        paths.append({'helper': name, 'path': found})
    public = set(handwritten) - private
    summary = {
        'source_revision': inputs['source_revision'], 'imported_modules': len(imports),
        'production_modules': len(owned), 'attributed_constants': len(rows),
        'handwritten': len(handwritten), 'fields': len(projections), 'private': len(private),
        'private_without_handwritten_public_path': [],
        'public_without_external_production_path': [
            dict(handwritten[name], name=name, clients=users.get(name, []),
                 client_modules={user: modules[user] for user in users.get(name, [])})
            for name in sorted(public - live)],
        'public_without_direct_clients': sorted(name for name in public if not users.get(name)),
        'axioms': sorted({axiom for row in rows for axiom in row['axioms']})}
    require(set(summary['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'},
            'unexpected core axioms')
    production = {}
    for file in subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT,
                                        text=True).splitlines():
        path = ROOT / file
        for source in index.project:
            if path.is_relative_to(source):
                name = '.'.join(path.relative_to(source).with_suffix('').parts)
                if not name.startswith('Hex'):
                    continue
                role = index.resolve(name)
                if role['path'] == file and role['category'] in {
                        'Sturm production', 'other Hex production',
                        'other root-package production'}:
                    production[name] = file
    helpers.check_production_imports(
        production, lambda name: helpers.family_evidence(index, name))
    cache = {}

    def reaches(name, visiting=frozenset()):
        if name.split('.')[0] in {'HexSignDet', 'HexSignDetTheory'}:
            return True
        if name in cache:
            return cache[name]
        if name in visiting:
            return False
        role = index.resolve(name)
        cache[name] = role['path'] is not None and any(
            reaches(parent, visiting | {name})
            for parent in helpers._parse_imports(ROOT / role['path']))
        return cache[name]

    required = {name: path for name, path in production.items() if reaches(name)}
    missing = {name: path for name, path in required.items() if name not in roles}
    require(not missing, 'missing production imports: ' + str(missing))
    missing_evidence = set(scope['required_modules']) - set(imports)
    require(not missing_evidence, 'missing selected evidence imports: ' + str(missing_evidence))
    coverage = {
        'scope': 'Tracked Hex production modules transitively importing either SignDet root; '
                 'import coverage, not runtime-use or external-client coverage.',
        'production_modules': len(production), 'required_modules': len(required),
        'covered_modules': dict(sorted(required.items())), 'missing_modules': missing}
    return {
        'summary.json': summary, 'handwritten.json': handwritten, 'helper-paths.json': paths,
        'downstream-use.json': {'users': users, 'modules': modules,
                                'aliases': aliases, 'live': sorted(live)},
        'module-roles.json': roles, 'production-import-coverage.json': coverage,
        'evidence-import-coverage.json': {
            'required_modules': scope['required_modules'], 'missing_modules': [],
            'excluded_entry_points': scope['excluded_entry_points']}}


if __name__ == '__main__':
    directory = Path(sys.argv[1])
    for name, value in derive(directory).items():
        (directory / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    print('Core source inventory, private paths and production/evidence import coverage agree.')
