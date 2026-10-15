"""Normalize all three raw OrderedFn capture files into their committed layout."""
import argparse
import json
import re
import subprocess
import sys
import types
from collections import defaultdict, deque
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sources(root, revision=None):
    """Read tracked source bytes, including unimported prospective clients."""
    paths = subprocess.check_output(
        ['git', 'ls-tree', '-rz', '--name-only', revision] if revision else
        ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'],
        cwd=root, text=True).split('\0')
    paths = [p for p in paths if p.endswith('.lean') or
             p == 'scripts/bench/sweep_freshness.py']
    require(all('\n' not in p for p in paths), 'newline in source path is unsupported')
    if revision is None:
        return {p: (root / p).read_bytes() for p in paths}
    result = {}
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=root,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        for path in paths:
            process.stdin.write((revision + ':' + path + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            require(len(header) == 3 and header[1] == b'blob', 'missing source: ' + path)
            result[path] = process.stdout.read(int(header[2]))
            require(process.stdout.read(1) == b'\n', 'invalid Git blob framing')
        process.stdin.close()
        require(process.wait() == 0, 'Git source reader failed')
    return result


def glob_list(expression):
    """Read literal Lake glob arrays, concatenations and Glob maps; refuse others."""
    pipeline = re.search(r'\|>\s*\.map\s+Glob\.one\s*$', expression)
    if pipeline:
        expression = expression[:pipeline.start()]
        require(not re.search(r'(?:\.|Glob\.)(?:one|submodules|andSubmodules)\s+`', expression),
                'mapped non-name glob')
    result, cursor = [], 0
    pattern = re.compile(r'#\[([^\]]*)\]\s*(?:\.map\s+Glob\.(one|submodules|andSubmodules))?')
    for match in pattern.finditer(expression):
        separator = expression[cursor:match.start()].strip()
        require(separator == ('' if cursor == 0 else '++'), 'unsupported glob expression: ' + expression)
        for entry in match[1].split(','):
            if not entry.strip():
                continue
            item = re.fullmatch(
                r'\s*(?:(?:\.|Glob\.)(one|submodules|andSubmodules)\s+)?`([A-Za-z_][\w.]*)\s*', entry)
            require(item is not None, 'unsupported glob entry: ' + entry)
            require(not (match[2] and item[1]), 'mapped non-name glob')
            result.append((match[2] or item[1] or 'one', item[2]))
        cursor = match.end()
    require(cursor and not expression[cursor:].strip(), 'unsupported glob suffix: ' + expression[cursor:])
    return result


def glob_matches(glob, name):
    kind, prefix = glob
    return ((kind != 'submodules' and name == prefix) or
            (kind != 'one' and name.startswith(prefix + '.')))


def library_clients(root, roots, revision=None):
    """Resolve Lake library membership and all transitive import clients independently."""
    files = sources(root, revision)
    helper = types.ModuleType('_orderedfn_lake_blocks')
    helper.__file__ = str(root / 'scripts/bench/sweep_freshness.py')
    sys.modules[helper.__name__] = helper
    exec(compile(files['scripts/bench/sweep_freshness.py'], helper.__file__, 'exec'), helper.__dict__)
    strip = helper.strip_lean_comments
    blocks = helper.lakefile_blocks(files['lakefile.lean'].decode())
    require('command uncertain' not in blocks, 'uncertain Lake configuration')
    for key, raw in blocks.items():
        if key.startswith('package '):
            require(not re.search(r'\bsrcDir\s*:=', strip(raw)),
                    'package-level srcDir is unsupported')
    modules = {}
    for key, raw in blocks.items():
        if not key.startswith('lean_lib '):
            continue
        target = key.removeprefix('lean_lib ')
        body = strip(raw)
        header = re.search(r'(?m)^\s*(?:@\[[^\]]*\]\s*)*lean_lib\s+\S+\s+where([^\n]*)', body)
        require(header is None or not header[1].strip(), 'inline library fields are unsupported')
        fields = dict(re.findall(
            r'(?ms)^\s+(\w+)\s*:=\s*(.*?)(?=^\s+\w+\s*:=|\Z)', body))
        source = fields.get('srcDir', '""').strip()
        require(re.fullmatch(r'"[^"\n]*"', source), 'nonliteral library srcDir: ' + target)
        directory = str(Path(source[1:-1]))
        directory = '' if directory == '.' else directory.rstrip('/')
        prefix = directory + '/' if directory else ''
        root_globs = glob_list(fields['roots']) if 'roots' in fields else [('one', target)]
        require(all(kind == 'one' for kind, _ in root_globs), 'non-name library roots')
        expression = fields.get('globs')
        parked = []
        wrapper = 'Array.filter (fun g => !isParkedGlob g) <|'
        if expression and expression.strip().startswith(wrapper):
            prefixes = strip(blocks.get('def parkedConformancePrefixes', ''))
            match = re.fullmatch(r'\s*def parkedConformancePrefixes\s*:\s*List String\s*:=\s*\[([^\]]*)\]\s*', prefixes)
            require(match is not None, 'unsupported parked conformance prefixes')
            for entry in match[1].split(','):
                if entry.strip():
                    require(re.fullmatch(r'\s*"[A-Za-z_][\w]*"\s*', entry), 'nonliteral parked prefix')
                    parked.append(entry.strip()[1:-1])
            definition = re.sub(r'\s+', '', strip(blocks.get('def isParkedGlob', '')))
            require(definition == 'defisParkedGlob:Glob→Bool|.onen|.submodulesn|.andSubmodulesn=>parkedConformancePrefixes.any(n.getRoot.toString.startsWith·)',
                    'unsupported parked glob predicate')
            expression = expression.strip()[len(wrapper):]
        globs = glob_list(expression) if expression is not None else root_globs
        globs = [g for g in globs if not any(g[1].split('.')[0].startswith(p) for p in parked)]
        buildable_roots = [name for _, name in root_globs
                           if any(glob_matches(g, name) for g in globs)]
        for path in files:
            if not path.endswith('.lean') or not path.startswith(prefix):
                continue
            name = path.removeprefix(prefix).removesuffix('.lean').replace('/', '.')
            if not (any(glob_matches(g, name) for g in globs) or
                    any(name == r or name.startswith(r + '.') for r in buildable_roots)):
                continue
            require(name not in modules or modules[name] == path, 'ambiguous library module: ' + name)
            modules[name] = path
    imports, reverse, mains = {}, defaultdict(set), set()
    for name, path in modules.items():
        text = strip(files[path].decode())
        imports[name] = []
        lines = text.splitlines()
        for line in lines:
            line = line.strip()
            if not line or re.fullmatch(r'(?:module(?:\s+[\w.]+)?|prelude)', line):
                continue
            match = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
            if match is None:
                # Later Verso code blocks can contain textual imports. Only
                # the real header is an import block in a valid Lean module.
                require(not re.match(r'(?:(?:public|private|meta)\s+)*import\b', line)
                        and line not in {'public', 'private', 'meta'},
                        'unsupported import layout in ' + path)
                break
            names = match[1].split()
            require(all(n == 'all' or re.fullmatch(r'[A-Za-z_][\w.]*', n) for n in names),
                    'unsupported import in ' + path)
            imports[name].extend(n for n in names if n != 'all')
        for parent in imports[name]:
            reverse[parent].add(name)
        if re.search(r'(?m)^(?:(?:public|private|unsafe|noncomputable)\s+)*def\s+(?:_root_\.)?main\b', text):
            mains.add(name)

    def closure(start):
        seen, queue = set(), deque(start)
        while queue:
            name = queue.popleft()
            if name in seen:
                continue
            seen.add(name)
            queue.extend(reverse[name] - seen)
        return seen

    reached = closure(roots) & modules.keys()
    omitted = reached & closure(mains)
    require(all(name in mains for name in omitted),
            'a library client imports an executable: ' + str(sorted(omitted - mains)))
    return ({n: modules[n] for n in sorted(reached - omitted)},
            {n: modules[n] for n in sorted(omitted)})


def normalized(directory):
    rows = json.loads((directory / 'declaration-use.json').read_text(encoding='utf-8'))
    rows.sort(key=lambda row: (row['module'], row['name']))
    for row in rows:
        row['users'].sort()
        row['axioms'].sort()
    fields = json.loads((directory / 'structure-fields.json').read_text(encoding='utf-8'))
    fields.sort(key=lambda field: (field['structure'], field['field']))
    imports = json.loads((directory / 'audit-imports.json').read_text(encoding='utf-8'))
    return {'declaration-use.json': rows, 'structure-fields.json': fields,
            'audit-imports.json': imports}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, data in normalized(args.directory).items():
        content = json.dumps(data, indent=2, sort_keys=True) + '\n'
        if args.check:
            if (args.directory / name).read_text(encoding='utf-8') != content:
                raise ValueError('normalized artifact differs: ' + name)
        else:
            (args.directory / name).write_text(content, encoding='utf-8')


if __name__ == '__main__':
    main()
