#!/usr/bin/env python3
"""Fresh-module construction attribution with matched import-only subtraction."""
from pathlib import Path
import sys
import json
import tempfile
import shutil
import argparse
import re

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, run_cli, parse_args, environment,
    default_output, source_hashes,
)

PREFIX = 'HexPrimality.ProofProbe.PMinusOne'
SUPPORT = ROOT / 'bench/HexPrimality/ProofProbe/PMinusOne/Support.lean'
CASES = tuple(re.findall(r'\("([\w-]+)", \d+\)', SUPPORT.read_text()))
assert len(CASES) == 60 and len(set(CASES)) == 60

def module_name(name):
    parts = name.split('-')
    return ('Parent' + parts[1] + 'Q' + parts[2] if parts[0] == 'parent'
            else ''.join(p[0].upper() + p[1:] for p in parts))

def specification(name):
    module = f'{PREFIX}.{module_name(name)}'
    baseline = ProbeModule(module + 'Imports')
    return SweepSpec(
        description=__doc__,
        pairs=(ProbePair('imports', baseline, baseline,
                         {'component': 'import-only-baseline'}, null_control=True),
               ProbePair(name, ProbeModule(module + 'Disabled'),
                         ProbeModule(module + 'Enabled'),
                         {'component': 'construction-search-attribution',
                          'case': name, 'each_distinct_input': 'once',
                          'interpretation': 'phase attribution; no asymptotic verdict'})),
        probe_target='HexPrimalityElabProbeScientific',
        schema='hex-pminusone-construction-probes-v1',
        measurement='paired-fresh-module-import-subtracted-wall',
        output_stem='pminusone-construction-proof-' + name,
        extra_sources=(Path('HexPrimality/SPEC/hex-primality.md'),
                       Path('conformance-fixtures/HexPrimality/pminusone-stage2-parents.jsonl')),
        required_samples=8,
        import_baseline_control='imports',
        retain_compiler_output=True,
    )

def main():
    selector = argparse.ArgumentParser(add_help=False)
    selector.add_argument('--case', required=True, choices=CASES)
    selection, argv = selector.parse_known_args()
    spec = specification(selection.case)
    args = parse_args(spec.description, argv, default_samples=8)
    env = environment()
    output = args.output or default_output(env, spec.output_stem)
    if not output.is_absolute():
        output = ROOT / output
    sidecar = Path(str(output) + '.samples.jsonl')
    if any(p.exists() for p in (output, sidecar, Path(str(output) + '.gz'))):
        raise RuntimeError('measurement output exists; choose a fresh path')
    # Keep incremental records outside the checkout so they cannot dirty the
    # measured source snapshot. Retain them even if a later build fails.
    with tempfile.NamedTemporaryFile(mode='w', prefix='pminusone-proof-',
                                     suffix='.jsonl', delete=False) as log:
        retained = Path(log.name)
        print(f'Incremental samples: {retained}', flush=True)
        log.write(json.dumps({'type': 'metadata', 'environment': env,
                              'source_sha256': source_hashes(spec, Path(__file__))}) + '\n')
        log.flush()
        def observe(module, sample):
            log.write(json.dumps({'type': 'sample', 'module': module, **sample}) + '\n')
            log.flush()
        try:
            code = run_cli(spec, Path(__file__), argv, sample_observer=observe)
        except BaseException:
            print(f'Retained partial samples: {retained}', file=sys.stderr)
            raise
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(retained, sidecar)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
