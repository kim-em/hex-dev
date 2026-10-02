#!/usr/bin/env python3
"""Six adjacent AB/BA kernel-profile pairs on unchanged small identities.

Use separate checkouts to compare implementations, or the same checkout with
--candidate-bits to isolate the cost of the programmatic checker's cap literal.
The latter is diagnostic only: it does not change the shipping probes or budget.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.kronecker_sweep import cpu_lease, ALLOWED
from scripts.bench.kronecker_attribution import CASES
from scripts.bench import fresh_module_sweep as sweep
from scripts.ci.check_benches_mathlib_free import _parse_imports

PREFIX = 'HexKroneckerMathlib.ProofProbe'
MODULE = PREFIX + '.Attribution'
REL = Path('bench/HexKroneckerMathlib/ProofProbe/Attribution.lean')


def sources(root, cases):
    queue = [f'{PREFIX}.{case}Construction' for case in cases]
    seen, paths = set(), set()
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        rel = Path(*module.split('.')).with_suffix('.lean')
        path = next((root / prefix / rel for prefix in ['', 'bench', 'conformance']
                     if (root / prefix / rel).is_file()), None)
        if path:
            paths.add(path)
            queue.extend(_parse_imports(path))
    paths.update(root / p for p in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain'])
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--candidate-bits', type=int)
    parser.add_argument('--case', action='append', help='explicit case set for a separate comparison')
    parser.add_argument('--scratch', default='Attribution', help='scratch module basename')
    args = parser.parse_args()
    if not re.fullmatch('[A-Z][A-Za-z0-9]*', args.scratch):
        parser.error('scratch must be a Lean module basename')
    cases = args.case or CASES
    module = PREFIX + '.' + args.scratch
    rel_probe = REL.with_name(args.scratch + '.lean')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    roots = dict(reference=args.reference.resolve(), candidate=args.candidate.resolve())
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    for root in set(roots.values()):
        if (root / rel_probe).exists():
            raise RuntimeError(f'scratch module already exists: {root / rel_probe}')
    record = dict(schema='hex-kronecker-attribution-pairs-v1', cpu=cpu,
                  topology=sweep.cpu_topology(cpu), candidate_bits=args.candidate_bits,
                  runner=Path(__file__).read_text(), arms={}, samples=[])
    for arm, root in roots.items():
        hashes = sources(root, cases)
        record['arms'][arm] = dict(root=str(root), source_hashes=hashes,
            commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip())
        with tarfile.open(output / (arm + '-sources.tar.gz'), 'w:gz') as archive:
            for rel in hashes:
                archive.add(root / rel, arcname=rel)
    for index, root in enumerate(dict.fromkeys(roots.values())):
        command = ['lake', 'build', *(f'+{PREFIX}.{case}Construction' for case in cases)]
        print('warming', root, flush=True)
        run = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / f'warm-{index}.log').write_text(run.stdout)
        if run.returncode:
            raise RuntimeError(f'dependency build failed: {root}')
    try:
        for trial in range(6):
            for case in sweep.rotate(cases, trial):
                for arm in (['reference', 'candidate'] if trial % 2 == 0 else ['candidate', 'reference']):
                    root = roots[arm]
                    source = (root / REL.with_name(case + 'Kronecker.lean')).read_text()
                    source = source.replace('set_option maxHeartbeats 0',
                        'set_option profiler true\nset_option profiler.threshold 0\nset_option maxHeartbeats 0')
                    if arm == 'candidate' and args.candidate_bits is not None:
                        source = source.replace('  kronecker\n',
                            f'  kronecker (config := {{ maxPackedBits := {args.candidate_bits} }})\n')
                    (root / rel_probe).write_text(source)
                    for prefix in ['lib/lean', 'ir']:
                        parent = root / '.lake/build' / prefix / 'HexKroneckerMathlib/ProofProbe'
                        for path in parent.glob(args.scratch + '.*'):
                            if path.is_file():
                                path.unlink()
                    before = sweep.sampled_host_state(sweep.host_state())
                    command = ['lake', 'build', '+' + module + ':olean']
                    start = time.monotonic_ns()
                    run = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                    wall = time.monotonic_ns() - start
                    log = f'{trial + 1}-{case}-{arm}.log'
                    (output / log).write_text(run.stdout)
                    timer = re.findall(r'\ttype checking ([0-9.]+)([a-z]+)', run.stdout)
                    axioms = sweep.parse_axioms(run.stdout)
                    result = dict(trial=trial + 1, case=case, arm=arm, source=source, command=command,
                        log=log, wall_ns=wall, returncode=run.returncode, kernel_timer=timer,
                        axioms=axioms, host_before=before,
                        host_after=sweep.sampled_host_state(sweep.host_state()))
                    record['samples'].append(result)
                    record['sources_unchanged'] = all(sources(root, cases) == record['arms'][arm]['source_hashes']
                        for arm, root in roots.items())
                    (output / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
                    print(trial + 1, case, arm, timer, flush=True)
                    if run.returncode or not timer or axioms is None or set(axioms) - ALLOWED:
                        raise RuntimeError(f'profile or axiom audit failed: {log}')
    finally:
        for root in set(roots.values()):
            (root / rel_probe).unlink(missing_ok=True)
        lease.close()


if __name__ == '__main__':
    main()
