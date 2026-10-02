#!/usr/bin/env python3
"""Add full primality? builds to an existing native primality corpus record."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import HEADER, run


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('native', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--timeout', type=float, default=60)
    args = p.parse_args()
    record = json.loads(args.native.read_text())
    cpu = pick()
    record['end_to_end'] = []
    record['end_to_end_cpu'] = cpu
    record['end_to_end_commit'] = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    record['native_source_record'] = str(args.native)
    module = 'HexPrimality.ProofProbe.Curve25519.EndToEnd'
    source = ROOT/'bench'/Path(module.replace('.', '/')+'.lean')
    artifact = ROOT/'.lake/build/lib/lean'/Path(module.replace('.', '/')+'.olean')
    if source.exists():
        raise RuntimeError('refusing to overwrite an existing probe')
    def save():
        args.output.write_text(json.dumps(record, indent=2)+'\n')
    try:
        for block in range(record['blocks']):
            for case in record['cases']:
                for arm in (['baseline', 'complete'] if block == 0 else ['complete', 'baseline']):
                    body = HEADER
                    if arm == 'baseline':
                        body += f'def input : Nat := {case["n"]}\n'
                    else:
                        body += f'theorem result : Hex.Nat.Prime {case["n"]} := by primality?\n'
                    source.write_text(body)
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', '+'+module+':olean'], ROOT, args.timeout, cpu)
                    if row['status'] == 'error' and 'primality?:' in row['stdout'] and (
                            'exhausted after' in row['stdout'] or 'construction limit is' in row['stdout']):
                        row['status'] = 'exhausted'
                    row.update(block=block, case=case['name'], system='hex', arm=arm,
                               source=body, source_bytes=len(body.encode()),
                               olean_bytes=artifact.stat().st_size if artifact.exists() else None)
                    record['end_to_end'].append(row)
                    save()
                    print(block, case['name'], arm, row['status'], row['seconds'], flush=True)
                    if row['status'] == 'error':
                        raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        source.unlink(missing_ok=True)
        save()


if __name__ == '__main__':
    main()
