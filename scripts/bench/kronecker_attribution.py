#!/usr/bin/env python3
"""Retain fresh-module kernel profiles for the seven small losing grid cases."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.kronecker_sweep import cpu_lease

CASES = ['GridK1D2', 'GridK1D4', 'GridK1D8', 'GridK2D2', 'GridK3D2', 'GridK4D2', 'GridK6D2']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    sources = sorted(p for folder in ['HexKronecker', 'HexKroneckerMathlib', 'HexReflect']
                     for p in (ROOT/folder).glob('*.lean'))
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    with tarfile.open(args.output/'sources.tar.gz', 'w:gz') as archive:
        for p in sources:
            archive.add(p, arcname=p.relative_to(ROOT))
    records = []
    probe = ROOT/'bench/HexKroneckerMathlib/ProofProbe/Attribution.lean'
    try:
        for case in CASES:
            source = probe.with_name(case+'Kronecker.lean').read_text()
            source = source.replace('set_option maxHeartbeats 0',
                'set_option profiler true\nset_option profiler.threshold 0\nset_option maxHeartbeats 0')
            probe.write_text(source)
            command = ['lake', 'build', '+HexKroneckerMathlib.ProofProbe.Attribution']
            run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (args.output/(case+'.log')).write_text(run.stdout)
            records.append(dict(case=case, command=command, returncode=run.returncode, source=source,
                                host_load=os.getloadavg()))
            (args.output/'record.json').write_text(json.dumps(dict(cpu=cpu, source_hashes=hashes,
                samples=records), indent=2)+'\n')
            print(case, run.returncode, flush=True)
            if run.returncode:
                raise SystemExit(run.returncode)
    finally:
        probe.unlink(missing_ok=True)
        lease.close()

if __name__ == '__main__':
    main()
