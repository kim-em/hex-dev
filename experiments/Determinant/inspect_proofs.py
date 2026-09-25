#!/usr/bin/env python3
"""One bounded structural comparison, not a performance ranking."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import sys

from arithmetic import ROOT
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
from scripts.bench.det_bench_limits import supervise


def main(output, candidate='direct'):
    assert candidate in ('direct', 'literal')
    with (ROOT / '.lake/determinant-adversarial.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        # The diagnostic is charged to the same sibling-root ledger as wider probes.
        previous = list(output.parent.parent.glob('*/*/case.json'))
        elapsed = 0
        for path in previous:
            status = path.parent / 'status.json'
            if not status.exists():
                raise SystemExit(f'unfinished prior case: {path.parent}')
            elapsed += json.loads(status.read_text())['elapsed_seconds']
        if elapsed + 65 > 360:
            raise SystemExit('insufficient remaining allowance for inspection')
        output.mkdir(parents=True, exist_ok=False)
        source = ROOT / 'reports/bench-results/determinant-direct/rankone10'
        case = json.loads((source / 'case.json').read_text())
        case.update(inspection=True, diagnostic=True, search_seconds=360, invocation_seconds=60)
        case['candidate'] = candidate
        (output / 'case.json').write_text(json.dumps(case, indent=2) + '\n')
        code = (source / 'AdversarialSampleDirect.lean.txt').read_text()
        header, body = code.split('#measure_decl theorem result', 1)
        header = header.replace('import Determinant.Normalized\n', 'import Determinant.Inspect\n')
        body = body.split('#print axioms result')[0]
        body = body.replace('  direct_bird', '  timed_proof\n    direct_bird')
        code = header + '#measure_decl theorem mathlibResult' + body.replace('direct_bird', 'simp only [norm_det] <;> ring')
        code += '#measure_decl theorem directResult' + body.replace('direct_bird', candidate + '_bird')
        code += '''#print axioms mathlibResult
#print axioms directResult
#compare_proofs Determinant.Adversarial.mathlibResult Determinant.Adversarial.directResult
end Determinant.Adversarial
'''
        path = ROOT / 'experiments/Determinant/InspectionSample.lean'
        assert not path.exists()
        (output / 'InspectionSample.lean.txt').write_text(code)
        paths = [Path(__file__), ROOT / 'experiments/Determinant/Inspect.lean',
                 ROOT / 'experiments/Determinant/Normalized.lean']
        (output / 'sources.json').write_text(json.dumps({str(p.relative_to(ROOT)):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}, indent=2) + '\n')
        for p in paths:
            (output / (p.name + '.txt')).write_bytes(p.read_bytes())

        def run(_deadline):
            cpu, lease = cpu_lease()
            os.sched_setaffinity(0, {cpu})
            os.environ['LEAN_NUM_THREADS'] = '1'
            topology = sweep.cpu_topology(cpu)
            monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
            def observe(module, result):
                (output / 'observation.json').write_text(json.dumps(dict(module=module, result=result), indent=2) + '\n')
            try:
                path.write_text(code)
                result = sweep.build_sample('Determinant.InspectionSample', 60, cpu, monitored, observe, True)
                text = result['compiler_output']
                audits = re.findall(r"'Determinant.Adversarial.(mathlibResult|directResult)' depends on axioms: \[([^]]*)\]", text)
                assert len(audits) == 2
                for _, names in audits:
                    assert {s.strip() for s in names.split(',')} <= {'propext','Classical.choice','Quot.sound'}
                comparison = json.loads(re.search(r'PROOF_COMPARISON (.*)', text)[1])
                data = dict(comparison=comparison, declaration_ns=re.findall(r'DECL_NS (\d+)', text),
                            tactic_ns=re.findall(r'CALL_NS (\d+)', text), axioms=dict(audits),
                            cpu=cpu, topology=topology, environment=sweep.environment())
                (output / 'inspection.json').write_text(json.dumps(data, indent=2) + '\n')
                print(json.dumps(data['comparison']), flush=True)
            finally:
                path.unlink(missing_ok=True)
                lease.close()
        return supervise(run, 65, output / 'status.json')


if __name__ == '__main__':
    raise SystemExit(main(Path(sys.argv[1]), sys.argv[2] if len(sys.argv) > 2 else 'direct'))
