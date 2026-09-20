#!/usr/bin/env python3
"""Fresh-module construction attribution with matched import-only subtraction."""
from pathlib import Path
import sys
import json
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, run_cli, parse_args, environment,
    default_output, source_hashes,
)

PREFIX = 'HexPrimality.ProofProbe.PMinusOne'
FAMILIES = ('Parents64', 'Parents128', 'Exhausted128', 'Parents256', 'Parents512',
            'FullMiss', 'Fields', 'Smooth', 'Table', 'Balanced')
BASELINE = ProbeModule(f'{PREFIX}.Baseline')
SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair('imports', BASELINE, BASELINE,
                     {'component': 'import-only-baseline'}, null_control=True),
           *(ProbePair(family, ProbeModule(f'{PREFIX}.{family}Disabled'),
                       ProbeModule(f'{PREFIX}.{family}Enabled'),
                       {'component': 'construction-search-attribution',
                        'family': family, 'each_distinct_input': 'once',
                        'interpretation': 'phase attribution; no asymptotic verdict'})
             for family in FAMILIES)),
    probe_target='HexPrimalityElabProbeScientific',
    schema='hex-pminusone-construction-probes-v1',
    measurement='paired-fresh-module-import-subtracted-wall',
    output_stem='pminusone-construction-proof',
    extra_sources=(Path('HexPrimality/SPEC/hex-primality.md'),
                   Path('conformance-fixtures/HexPrimality/pminusone-stage2-parents.jsonl')),
    required_samples=8,
    import_baseline_control='imports',
    retain_compiler_output=True,
)

def main():
    args = parse_args(SPEC.description, default_samples=8)
    env = environment()
    output = args.output or default_output(env, SPEC.output_stem)
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
                              'source_sha256': source_hashes(SPEC, Path(__file__))}) + '\n')
        log.flush()
        def observe(module, sample):
            log.write(json.dumps({'type': 'sample', 'module': module, **sample}) + '\n')
            log.flush()
        try:
            code = run_cli(SPEC, Path(__file__), sample_observer=observe)
        except BaseException:
            print(f'Retained partial samples: {retained}', file=sys.stderr)
            raise
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(retained, sidecar)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
