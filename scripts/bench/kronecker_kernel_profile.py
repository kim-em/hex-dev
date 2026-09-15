#!/usr/bin/env python3
"""Collect one fresh kernel-only profile for each Kronecker proof family."""
import argparse
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.kronecker_sweep import ALLOWED, PREFIX, cpu_lease


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    families = [('reflected-identities', 'GridK3D8', 'Profile'),
                ('determinant-identities', 'DetN4K3D1', 'Profile'),
                ('dense-box-declines', 'IndependentN5', 'KernelProfile')]
    pairs = tuple(sweep.ProbePair(stem,
        sweep.ProbeModule(f'{PREFIX}.{stem}{"Decline" if suffix == "KernelProfile" else "Kronecker"}Baseline'),
        sweep.ProbeModule(f'{PREFIX}.{stem}{suffix}'), {}) for _, stem, suffix in families)
    spec = sweep.SweepSpec(__doc__, pairs, 'HexKroneckerMathlibProofProbe',
        'hex-kronecker-kernel-profile-v1', 'kernel-only', 'hex-kronecker', absolute_only=True,
        extra_sources=(Path('scripts/bench/kronecker_sweep.py'),))
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    hashes = sweep.source_hashes(spec, Path(__file__))
    sweep.warm_imports(spec, 1200)
    topology = sweep.cpu_topology(cpu)
    monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
    profiles = []
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for (family, stem, _), pair in zip(families, pairs, strict=True):
        result = sweep.build_sample(pair.candidate.module, 180, cpu, monitored,
            retain_compiler_output=True)
        if result['axioms'] is None or set(result['axioms']) - ALLOWED:
            raise RuntimeError(f"unapproved or missing axiom audit: {result['axioms']}")
        profiles.append(dict(family=family, stem=stem, module=pair.candidate.module,
                             result=dict(result, state='complete')))
        data = dict(schema='hex-kronecker-kernel-profile-v1', cpu=cpu, topology=topology,
            source_hashes=hashes, sources_unchanged=hashes == sweep.source_hashes(spec, Path(__file__)),
            profiles=profiles)
        args.output.write_text(json.dumps(data, indent=2) + '\n')
        print(stem, 'complete', flush=True)
    lease.close()


if __name__ == '__main__':
    main()
