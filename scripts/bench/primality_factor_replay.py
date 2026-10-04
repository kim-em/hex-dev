#!/usr/bin/env python3
"""Kernel-replay exact positive outputs from retained factor-policy runs.

Hex proofs become CI-built literal probes. PrimeCert proofs are checked in the
unmodified pinned upstream checkout. A manifest links every positive sample to
its exact term and checked module, including repeated timing samples.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HEADER = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
'''
AXIOMS = '[propext, Classical.choice, Quot.sound]'


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def term(source):
    start = source.index('prime_cert%')
    opening = source.index('[', start)
    depth = 0
    for i in range(opening, len(source)):
        depth += (source[i] == '[') - (source[i] == ']')
        if depth == 0:
            return source[start:i+1]
    raise ValueError('unterminated PrimeCert term')


def audit(name):
    return f"\n/-- info: '{name}' depends on axioms: {AXIOMS} -/\n#guard_msgs in\n#print axioms {name}\n"


def build(cwd, modules, log):
    command = ['lake', 'build', *['+' + m + ':olean' for m in modules]]
    with log.open('w') as out:
        p = subprocess.run(command, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f'kernel replay failed; see {log}')
    return {'command': command, 'returncode': p.returncode, 'log_sha256': digest(log.read_text())}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reports', nargs='+', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--primecert', type=Path, required=True)
    p.add_argument('--allow-incomplete', action='store_true', help='check finished samples during a running sweep')
    args = p.parse_args()
    if args.output.exists():
        p.error('retain the existing manifest; choose a new output path')
    native, upstream, links = {}, {}, []
    for path in args.reports:
        report = json.loads(path.read_text())
        if not report['complete'] and not args.allow_incomplete:
            p.error(f'{path} is not complete')
        for index, row in enumerate(report['samples']):
            status = row.get('result', {}).get('status')
            if status not in ['success', 'generated']:
                continue
            assert row['state'] == 'finished'
            if status == 'success':
                certificate = row['result']['certificate']
                assert row['result']['subject'] == row['subject']
                sha = digest(certificate)
                if sha in native:
                    assert native[sha]['subject'] == row['subject']
                else:
                    native[sha] = {'subject': row['subject'], 'certificate': certificate}
                system = 'hex'
            else:
                certificate = term(row['stdout'])
                sha = digest(certificate)
                goal = re.search(r': Nat.Prime (\d+) := prime_cert%', row['stdout'])
                assert goal and int(goal[1]) == row['subject']
                if sha in upstream:
                    assert upstream[sha]['subject'] == row['subject']
                else:
                    upstream[sha] = {'subject': row['subject'], 'term': certificate}
                system = 'primecert'
            links.append({'report': path.name, 'sample': index, 'system': system,
                          'term_sha256': sha, 'subject': row['subject']})
    directory = ROOT / 'bench/HexPrimalityMathlib/ProofProbe/FactorCorpus'
    directory.mkdir(parents=True, exist_ok=True)
    modules, sources = [], {}
    chunks = []
    chunk = []
    lines = 0
    for sha, item in native.items():
        name = 'Hex.PrimalityCorpus.h' + sha[:20]
        proof = (f'/-- Frozen certificate for {item["subject"]}. -/\n'
                 f'theorem {name} : _root_.Nat.Prime {item["subject"]} :=\n'
                 f'  Hex.Nat.natPrime_of_checkPrimeAt (c := {item["certificate"]}) (by decide +kernel)\n'
                 + audit(name))
        count = len(proof.splitlines())
        if chunk and lines + count > 1400:
            chunks.append(chunk); chunk = []; lines = 0
        chunk.append((sha, proof)); lines += count
    if chunk:
        chunks.append(chunk)
    for i, chunk in enumerate(chunks):
        module = f'HexPrimalityMathlib.ProofProbe.FactorCorpus.Chunk{i:03}'
        source = (HEADER + '\nmodule\n\npublic import HexPrimalityMathlib.Prime\n\npublic section\n\n'
                  '/-! Exact frozen checker equations for factor-policy corpus outputs. -/\n\n'
                  'set_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\n\n'
                  + '\n'.join(proof for _, proof in chunk))
        path = directory / f'Chunk{i:03}.lean'
        if not path.exists() or path.read_text() != source:
            path.write_text(source)
        sources[str(path.relative_to(ROOT))] = digest(source)
        modules.append(module)
        for sha, _ in chunk:
            native[sha].update(module=module, theorem='Hex.PrimalityCorpus.h' + sha[:20])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    native_build = build(ROOT, modules, args.output.with_suffix('.hex.log')) if modules else None
    pc_modules = []
    for sha, item in upstream.items():
        module = 'PrimeCert.FactorCorpus.H' + sha[:20]
        name = 'PrimalityCorpus.h' + sha[:20]
        source = ('import PrimeCert\n\nset_option linter.style.longLine false\n'
                  'set_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\n\n'
                  f'theorem {name} : Nat.Prime {item["subject"]} := {item["term"]}\n' + audit(name))
        path = args.primecert / (module.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != source:
            path.write_text(source)
        item.update(module=module, theorem=name, source=source, source_sha256=digest(source))
        pc_modules.append(module)
    upstream_build = build(args.primecert, pc_modules, args.output.with_suffix('.primecert.log')) if pc_modules else None
    manifest = {'reports': {x.name: digest(x.read_text()) for x in args.reports},
                'partial': args.allow_incomplete, 'hex_sources': sources,
                'native_build': native_build, 'primecert_build': upstream_build,
                'primecert_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                          cwd=args.primecert, text=True).strip(),
                'native': native, 'primecert': upstream, 'links': links}
    args.output.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Replayed {len(native)} Hex and {len(upstream)} PrimeCert terms; {len(links)} positive samples')


if __name__ == '__main__':
    main()
