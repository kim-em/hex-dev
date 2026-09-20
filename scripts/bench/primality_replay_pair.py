#!/usr/bin/env python3
"""Adjacent before/after replay, fresh Nat.Prime tactic, and native construction.

Build both checkouts' HexPrimalityMathlib and hexprimality_bench targets first.
Every completed sample is retained; no load-based filtering or retry occurs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import run
from scripts.bench.primality_kernel_direct import SUFFIX


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--primecert', type=Path, help='add comparator to phase measurements')
    p.add_argument('--primecert-source', type=Path, help='supplied Curve25519 comparator proof')
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--kind', choices=['kernel', 'phases', 'native'], required=True)
    args = p.parse_args()
    if args.output.exists(): p.error('use a fresh output path')
    roots = dict(before=args.baseline.resolve(), after=ROOT)
    if args.primecert and (args.kind != 'phases' or not args.primecert_source):
        p.error('--primecert requires phases and --primecert-source')
    if args.primecert: roots['primecert'] = args.primecert.resolve()
    module = 'HexPrimality.ProofProbe.Curve25519.ReplayPair' + args.kind.capitalize()
    relative = Path(module.replace('.', '/')+'.lean')
    def location(arm):
        if arm == 'primecert':
            return 'PrimeCert.Comparator.ReplayPair', roots[arm]/'PrimeCert/Comparator/ReplayPair.lean'
        if args.kind == 'phases':
            # Mathlib proof experiments belong to the bridge library, outside
            # the Mathlib-free computational benchmark module tree.
            return 'HexPrimalityMathlib.ReplayPair', roots[arm]/'HexPrimalityMathlib/ReplayPair.lean'
        return module, roots[arm]/'bench'/relative
    paths = [] if args.kind == 'native' else [location(arm)[1] for arm in roots]
    for path in paths: path.parent.mkdir(parents=True,exist_ok=True)
    if any(path.exists() for path in paths): p.error('probe path exists')
    data = json.loads(args.record.read_text())
    sources = {}
    if args.kind == 'kernel':
        for case in data['cases']:
            row = next(r for r in data['rows'] if r['case'] == case['name'] and r['system'] == 'hex' and r['status'] in ('ok', 'prepared'))
            source = row['source'].split('meta partial def inlineLocal')[0]
            ns = re.findall(r'^namespace (\S+)', source, flags=re.M)
            source += SUFFIX.replace('RESULT_NAME', '.'.join([*ns, 'result'])).replace('SUBJECT', case['n'])
            sources[case['name']] = source
    elif args.kind == 'phases':
        base = 'module\npublic import HexPrimalityMathlib\npublic meta import HexPrimality.Elab\npublic section\nset_option maxRecDepth 100000\n'
        n = 2**255-19
        sources['imports'] = base
        sources['input'] = base + f'def input : Nat := {n}\n'
        for phase, filename in [('literal', 'Literal'), ('render', 'Render'), ('search', 'Search')]:
            body = (ROOT/f'bench/HexPrimality/ProofProbe/Curve25519/{filename}.lean').read_text()
            body = body[body.index('namespace Hex.PrimalityCurveProbe'):]
            sources[phase] = base + body
        body = (ROOT/'bench/HexPrimality/ProofProbe/Curve25519/Replay.lean').read_text()
        body = body[body.index('namespace Hex.PrimalityCurveProbe'):]
        sources['replay'] = base + body.replace('Hex.Nat.Prime ', '_root_.Nat.Prime ').replace('Hex.Nat.prime_of_checkPrimeAt', 'Hex.Nat.natPrime_of_checkPrimeAt')
        sources['complete'] = base + f'theorem result : Nat.Prime {n} := by primality?\n'
    else:
        sources = dict(construction='', checker='')
    pc_sources = {}
    if args.primecert:
        base = 'module\npublic import PrimeCert\npublic import PrimeCert.SieveBase\npublic meta import PrimeCert.Meta.Construction\npublic section\nset_option maxRecDepth 100000\n'
        pc_sources['imports'] = base
        pc_sources['input'] = base + f'def input : Nat := {n}\n'
        pc_sources['complete'] = base + f'theorem result : Nat.Prime {n} := by prime_cert?\n'
        pc_sources['replay'] = args.primecert_source.read_text()
        search = f"""open Lean Elab in
run_cmd Lean.Elab.Command.liftTermElabM do
  let budget : PrimeCert.Construction.Budget := {{}}
  let primes ← PrimeCert.Meta.constructionPrimes (budget.smoothBounds.foldl max (max 31 budget.trialBound))
  let (ok, state) := PrimeCert.Construction.run budget primes {n}
  unless ok do throwError "construction exhausted"
"""
        pc_sources['search'] = base + search + '  logInfo m!"attempts {state.attempts}"\n'
        pc_sources['render'] = base + search + f'  logInfo (PrimeCert.Meta.constructionSource {n} state)\n'
    cpu = pick()
    record = dict(schema='primality-replay-pair/1', kind=args.kind, cpu=cpu,
        host=platform.node(), platform=platform.platform(),
        protocol='four fixed trial-major blocks, adjacent AB/BA; every completed sample retained',
        versions={arm: dict(commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
            toolchain=(root/'lean-toolchain').read_text().strip(),
            diff=subprocess.check_output(['git','diff','HEAD'],cwd=root,text=True),
            checker_sha256=hashlib.sha256((root/('PrimeCert/Pocklington.lean' if arm == 'primecert' else 'HexPrimality/Cert.lean')).read_bytes()).hexdigest()) for arm,root in roots.items()},
        sources=sources, primecert_sources=pc_sources, rows=[])
    def save():
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(record,indent=2)+'\n')
    try:
        for block in range(4):
            for case, source in sources.items():
                arms = list(roots)
                for arm in (arms if block % 2 == 0 else list(reversed(arms))):
                    if arm == 'primecert' and case not in pc_sources: continue
                    body = pc_sources[case] if arm == 'primecert' else source
                    root = roots[arm]
                    if args.kind == 'native':
                        export = args.output.with_suffix(f'.{block}.{case}.{arm}.json').resolve()
                        if export.exists(): raise RuntimeError(f'refusing to overwrite {export}')
                        target = 'runConstruction' if case == 'construction' else 'runCurveChecker'
                        command = [str(root/'.lake/build/bin/hexprimality_bench'), 'run', 'Hex.PrimalityBench.'+target, '--export-file', str(export)]
                    else:
                        target_module, path = location(arm)
                        path.write_text(body)
                        (root/'.lake/build/lib/lean'/Path(target_module.replace('.', '/')+'.olean')).unlink(missing_ok=True)
                        command = ['lake','build','+'+target_module+':olean']
                    row = run(command, root, 180, cpu)
                    row.update(block=block, case=case, arm=arm)
                    if args.kind == 'kernel' and row['status'] == 'ok':
                        row['kernel_nanos'] = int(re.search(r'DIRECT_KERNEL_NS (\d+)',row['stdout'])[1])
                    if args.kind == 'native' and export.exists():
                        row['export'] = json.loads(export.read_text())
                        export.unlink()
                    record['rows'].append(row); save()
                    print(block,case,arm,row['status'],row.get('kernel_nanos',row['seconds']),flush=True)
                    if row['status'] != 'ok': raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        for path in paths: path.unlink(missing_ok=True)
        save()


if __name__ == '__main__': main()
