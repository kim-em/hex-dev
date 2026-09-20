#!/usr/bin/env python3
"""Fresh-module construction attribution with matched import-only subtraction."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

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
    probe_target='HexPrimalityPMinusOneProbe',
    schema='hex-pminusone-construction-probes-v1',
    measurement='paired-fresh-module-import-subtracted-wall',
    output_stem='pminusone-construction-proof',
    extra_sources=(Path('HexPrimality/SPEC/hex-primality.md'),
                   Path('conformance-fixtures/HexPrimality/pminusone-stage2-parents.jsonl')),
    required_samples=8,
    import_baseline_control='imports',
    retain_compiler_output=True,
)

if __name__ == '__main__':
    raise SystemExit(run_cli(SPEC, Path(__file__)))
