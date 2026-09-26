#!/usr/bin/env python3
"""Check retained relation experiments without starting any measurements."""
import hashlib
import json
from pathlib import Path
import re

from adversarial_report import main as inventory, theorem_axioms
from arithmetic import ROOT


def main():
    root = ROOT / 'reports/bench-results/determinant-relations'
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    cases = sorted(root.glob('*/*/case.json'))
    elapsed, samples, snapshots = 0.0, 0, 0
    for case in cases:
        folder = case.parent
        config = json.loads(case.read_text())
        assert 0 < config['invocation_seconds'] <= 60, folder
        status = json.loads((folder / 'status.json').read_text())
        elapsed += status['elapsed_seconds']
        path = folder / 'results.json'
        data = json.loads(path.read_text())['samples'] if path.exists() else []
        if status['exit_status'] == 0:
            assert len(data) == 4, folder
            assert [s['pair'] for s in data] == [0, 0, 1, 1], folder
            assert data[0]['arm'] == data[3]['arm'] != data[1]['arm'] == data[2]['arm'], folder
        for sample in data:
            axioms = theorem_axioms(sample['result']['compiler_output'])
            assert set(axioms) <= allowed, folder
            assert set(axioms) == set(sample['result']['axioms']), folder
            samples += 1
        for name, digest in json.loads((folder / 'sources.json').read_text()).items():
            saved = folder / (Path(name).name + '.txt')
            assert hashlib.sha256(saved.read_bytes()).hexdigest() == digest, saved
            snapshots += 1
    assert 0 < elapsed <= 600, elapsed
    for variant in sorted({p.parent.parent for p in cases}):
        inventory(variant)
    # Measurements keep their original sources; correctness validation has its own manifest.
    validation = root / 'validation'
    sources = json.loads((validation / 'sources.json').read_text())
    assert 'experiments/Determinant/Relations.lean' in sources
    assert 'experiments/Determinant/RelationsAudit.lean' in sources
    for name, digest in sources.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    assert 'Build completed successfully' in (validation / 'lake-build.log').read_text()
    audit = (validation / 'audits.log').read_text()
    assert 'Build completed successfully' in audit
    dependencies = re.findall(r"'(Determinant\.[^']+)' depends on axioms: \[([^]]*)\]", audit)
    assert dependencies
    for name, names in dependencies:
        assert set(n.strip() for n in names.split(',') if n.strip()) <= allowed, name
    for marker in ('independent quotients generated no expansion proofs',
                   'colliding quotient products expanded and cancelled',
                   'sum and factor caches populated and reused',
                   'cached entry exposes zero before recurrence',
                   'heartbeat decline and outer ceiling preserved',
                   'exact scalar-work decline'):
        assert 'RELATIONS_CHECK ' + marker in audit, marker
    assert not list((ROOT / 'experiments/Determinant').glob('AdversarialSample*.lean'))
    result = dict(cases=len(cases), samples=samples, source_snapshots=snapshots,
                  measurement_seconds=elapsed, audit_dependency_records=len(dependencies),
                  validated_source_files=len(sources),
                  allowed_axioms=sorted(allowed))
    (root / 'validation/evidence.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
