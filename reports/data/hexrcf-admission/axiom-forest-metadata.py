from pathlib import Path
import importlib.util
import json
import re
import subprocess

repo = Path.cwd()
task = Path('/home/kim/.codex/tasks/hex-10358')
results = []

def run(name, command):
    log = task / f'axiom-forest-metadata-{name}.log'
    with log.open('w') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    results.append(dict(name=name, command=command, log=log.name, exit_code=result.returncode))

run('copyright', ['python3', 'scripts/check_copyright_headers.py'])
run('lines', ['python3', 'scripts/check_file_line_counts.py', '--base', 'origin/main'])
run('dag', ['python3', 'scripts/check_dag.py'])
run('admissions', ['python3', 'scripts/ci/check_named_admissions.py'])
run('diff', ['git', 'diff', 'HEAD', '--check'])
spec = importlib.util.spec_from_file_location('admissions', repo / 'scripts/ci/check_named_admissions.py')
admissions = importlib.util.module_from_spec(spec)
spec.loader.exec_module(admissions)
paths = subprocess.check_output(['git', 'diff', 'HEAD', '--name-only'], text=True).splitlines()
paths += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], text=True).splitlines()
# Verso prose is not Lean code for this source scanner. Its checked examples
# remain covered by the complete HexManual build and ordinary axiom audits.
lean = [path for path in paths if path.endswith('.lean') and not path.startswith('HexManual/')]
for path in lean:
    tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', path], capture_output=True).returncode == 0
    if tracked:
        # Existing audit diagnostics can contain words such as "axiom" in
        # interpolated text. Check the additions; new modules are checked whole.
        diff = subprocess.check_output(['git', 'diff', 'HEAD', '--unified=0', '--', path], text=True)
        source = '\n'.join(line[1:] for line in diff.splitlines() if line.startswith('+') and not line.startswith('+++'))
    else:
        source = (repo / path).read_text()
    found = [match.group() for match in admissions.find_admissions(admissions.code_only(source))]
    if path == 'HexRCF/HandlerTests/Admission.lean':
        # Deliberately rejected raw expressions and one discarded local fixture.
        # All four must remain inside these negative tests; no declaration escapes
        # the enclosing environment rollback. Production has no such exception.
        assert found == ['sorryAx', 'sorryAx', 'sorryAx', 'mkSorry'], found
        assert 'finally\n      saved.restore' in source
    else:
        assert not found, path
(task / 'axiom-forest-metadata-selected-admissions.log').write_text(f'{len(lean)} changed/new Lean files: production additions contain no admissions; new negative-test module has exactly three raw forbidden constants and one discarded local fixture under full saved-state rollback; complete adapter import cones scanned separately; Verso prose excluded\n')
results.append(dict(name='selected-admissions', log='axiom-forest-metadata-selected-admissions.log', exit_code=0))
links = 0
for path in paths:
    if not path.endswith(('.lean', '.md')):
        continue
    for match in re.finditer(r'\]\(([^)]+)\)', (repo / path).read_text()):
        target = match.group(1).split('#')[0]
        if not target or '://' in target:
            continue
        assert (repo / path).parent.joinpath(target).exists(), (path, target)
        links += 1
(task / 'axiom-forest-metadata-relative.log').write_text(f'{links} relative filesystem links exist in changed/new Lean and Markdown files; external URLs excluded\n')
results.append(dict(name='relative', log='axiom-forest-metadata-relative.log', exit_code=0))
(task / 'axiom-forest-metadata.json').write_text(json.dumps(results, indent=2) + '\n')
for result in results:
    print(result['name'], result['exit_code'])
assert all(result['exit_code'] == 0 for result in results)
