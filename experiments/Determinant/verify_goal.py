#!/usr/bin/env python3
"""Verify retained goal evidence without running any performance measurements."""
import hashlib
import json
from pathlib import Path
import re
import sys

from adversarial_report import main as inventory, theorem_axioms

ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def verify(root):
    cases = sorted(root.glob('*/*/case.json'))
    assert cases, 'no retained cases'
    elapsed, samples, snapshots, failures = 0.0, 0, 0, []
    for case in cases:
        folder = case.parent
        config = json.loads(case.read_text())
        assert 0 < config['invocation_seconds'] <= 60, folder
        status = json.loads((folder / 'status.json').read_text())
        elapsed += status['elapsed_seconds']
        result = folder / 'results.json'
        observations = json.loads(result.read_text())['samples'] if result.exists() else []
        if status['exit_status'] == 0:
            assert len(observations) == 4, folder
            assert [s['pair'] for s in observations] == [0, 0, 1, 1], folder
            assert observations[0]['arm'] == observations[3]['arm'], folder
            assert observations[1]['arm'] == observations[2]['arm'], folder
            assert observations[0]['arm'] != observations[1]['arm'], folder
        else:
            failures.append(str(folder.relative_to(root)))
        for sample in observations:
            axioms = theorem_axioms(sample['result']['compiler_output'])
            assert set(axioms) <= ALLOWED, folder
            assert set(axioms) == set(sample['result']['axioms']), folder
            samples += 1
        source_file = folder / 'sources.json'
        if source_file.exists():
            for name, digest in json.loads(source_file.read_text()).items():
                saved = folder / (Path(name).name + '.txt')
                assert hashlib.sha256(saved.read_bytes()).hexdigest() == digest, saved
                if folder.parent.name.startswith('bounded-final') and name.endswith('.lean'):
                    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
                snapshots += 1
        else:
            assert status['exit_status'] != 0, folder
    assert elapsed <= 3600, elapsed
    for variant in sorted({p.parent.parent for p in cases}):
        inventory(variant)
    audit_log = (root / 'validation' / 'audits.log').read_text()
    audit_axioms = re.findall(r"'(Determinant\.[^']+)' depends on axioms: \[([^]]*)\]", audit_log)
    assert audit_axioms, 'missing audit theorem dependency output'
    for name, names in audit_axioms:
        assert set(x.strip() for x in names.split(',') if x.strip()) <= ALLOWED, name
    assert 'Build completed successfully' in audit_log
    assert audit_log.count('ATOM_CHECK retained only the original quotient') == 3
    assert 'ATOM_CHECK expanded a monomial quotient' in audit_log
    for key in ('entry', 'iteration', 'diagonal'):
        assert f'CACHE_HIT {key}' in audit_log
    assert not list((ROOT / 'experiments/Determinant').glob('AdversarialSample*.lean'))
    summary = dict(cases=len(cases), successful_samples=samples, source_snapshots=snapshots,
                   failed_cases=failures, measurement_seconds=elapsed,
                   audit_dependency_records=len(audit_axioms),
                   permitted_axioms=sorted(ALLOWED))
    (root / 'validation' / 'evidence.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    verify(Path(sys.argv[1]))
