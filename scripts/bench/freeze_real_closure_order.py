#!/usr/bin/env python3
"""Freeze a clean complete-root executable for the registered Thom-order comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
EXE = 'hexrealclosure_trivial_bench'
FIXTURE = 'conformance-fixtures/HexRealClosure/trivial-distinct.jsonl'
FILES = ('bench/HexRealClosure/TrivialMeasurements.lean', 'HexRealClosure/RootOrder.lean',
         'HexRealClosure/RootOrderTests.lean', 'adapters/HexRealClosureTheory/RootOrder.lean',
         'adapters/HexRealClosureTheory/TrivialTowerTests.lean',
         'HexRealClosure/CompleteRoots.lean', 'HexRealClosure/Canonical.lean',
         'HexRealClosure/Trivial.lean', 'HexRealAlgebraic/Roots.lean',
         FIXTURE,
         'lake-manifest.json', 'lean-toolchain')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--oracle-python', type=Path, required=True)
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    compiler = os.environ.get('LEAN_CC')
    if not compiler:
        parser.error('set an explicit LEAN_CC for both arms')
    def git(*argv):
        return subprocess.check_output(['git', *argv], cwd=source, text=True).strip()
    if git('status', '--porcelain') or subprocess.check_output(
            ['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('freeze clean source and tooling commits')
    if source == output or source in output.parents or ROOT == output or ROOT in output.parents:
        parser.error('freeze outside source checkouts')
    output.mkdir(parents=True, exist_ok=False)
    metadata = dict(commit=git('rev-parse', 'HEAD'), cwd=str(source), status='',
                    freeze_status='preparing', commands=[], sources={}, source_git_blobs={},
                    binaries={}, compiler=compiler, panic_abort=True,
                    tooling_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    def save():
        (output/'metadata.json').write_text(json.dumps(metadata, indent=2)+'\n')
    def snapshot(path, name):
        shutil.copy2(path, output/(name.replace('/', '-')+'.txt'))
        metadata['sources'][name] = digest(path)
    def run(argv, label, cwd=source):
        argv = list(map(str, argv))
        with (output/(label+'.stdout.txt')).open('w') as out, (output/(label+'.stderr.txt')).open('w') as err:
            result = subprocess.run(argv, cwd=cwd, stdout=out, stderr=err,
                                    env={**os.environ, 'LEAN_ABORT_ON_PANIC':'1'})
        metadata['commands'].append(dict(argv=argv, cwd=str(cwd), exit_code=result.returncode,
                                        stdout=label+'.stdout.txt', stderr=label+'.stderr.txt'))
        save()
        result.check_returncode()
        return output/(label+'.stdout.txt')
    try:
        save()
        for name in FILES:
            snapshot(source/name, name)
            metadata['source_git_blobs'][name] = git('rev-parse', metadata['commit']+':'+name)
        for name in ('scripts/bench/freeze_real_closure_order.py', 'scripts/bench/fixed_conversion_paired.py',
                     'scripts/bench/analyze_real_closure_order.py',
                     'scripts/oracle/real_closure_trivial_measurements.py',
                     'reports/bench-results/real-closure-thom-order/protocol.md'):
            snapshot(ROOT/name, 'tooling/'+name)
        snapshot(Path(compiler), 'compiler-override')
        run([compiler, '--version'], 'compiler-version')
        manifest = json.loads((source/'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'].strip('«»') == 'lean-bench')
        package = source/'.lake/packages/lean-bench'
        if (subprocess.check_output(['git','-C',package,'rev-parse','HEAD'],text=True).strip()!=pin
                or subprocess.check_output(['git','-C',package,'status','--porcelain'],text=True).strip()):
            raise RuntimeError('LeanBench is not at its clean package pin')
        metadata['lean_bench_pin'] = pin
        run(['lake', 'build', EXE], 'build')
        binary = output/EXE
        shutil.copy2(source/'.lake/build/bin'/EXE, binary)
        metadata['binaries'][EXE] = dict(path=str(binary), sha256=digest(binary), size_bytes=binary.stat().st_size)
        snapshot(source/('.lake/build/bin/'+EXE+'.rsp'), 'link-recipe')
        for module in ('HexRealClosure/TrivialMeasurements', 'HexRealClosure/RootOrder', 'HexRealClosure/Trivial'):
            c = source/('.lake/build/ir/'+module+'.c')
            obj = c.with_name(c.name+'.o.export')
            trace = obj.with_name(obj.name+'.trace')
            commands = [shlex.split(r['message'][3:]) for r in json.loads(trace.read_text())['log']
                        if r['message'].startswith('.> ')]
            if len(commands)!=1 or commands[0][0]!=compiler or '-c' not in commands[0]:
                raise RuntimeError('actual C-object compiler differs: '+module)
            snapshot(c, 'compiled/'+module+'.c')
            snapshot(trace, 'compiled/'+module+'.trace')
            metadata.setdefault('objects',{})[module] = dict(sha256=digest(obj),size_bytes=obj.stat().st_size,command=commands[0])
        metadata['linked_objects']={}
        for arg in shlex.split((source/('.lake/build/bin/'+EXE+'.rsp')).read_text()):
            if not arg.endswith('.c.o.export'):
                continue
            obj=(source/arg).resolve() if not Path(arg).is_absolute() else Path(arg).resolve()
            key=str(obj.relative_to(source)) if obj.is_relative_to(source) else str(obj)
            c=Path(str(obj).removesuffix('.o.export'))
            row=dict(sha256=digest(obj),c_sha256=digest(c) if c.is_file() else None)
            if obj.is_relative_to(source):
                trace=json.loads(Path(str(obj)+'.trace').read_text())
                commands=[shlex.split(r['message'][3:]) for r in trace['log'] if r['message'].startswith('.> ')]
                if len(commands)!=1:
                    raise RuntimeError('ambiguous linked object compile trace: '+key)
                row.update(compiler=commands[0][0],command=[x.replace(str(source),'<source>') for x in commands[0]])
            metadata['linked_objects'][key]=row
        run(['lake','env','lean','--version'], 'lean-version')
        run(['lscpu','--json'], 'cpu-info')
        functional = run([binary,'emit-distinct'], 'functional')
        if functional.read_bytes()!=(source/FIXTURE).read_bytes():
            raise RuntimeError('functional output differs from the registered fixture')
        run([args.oracle_python,ROOT/'scripts/oracle/real_closure_trivial_measurements.py',
             '--suite','distinct',functional], 'oracle', ROOT)
        if git('status','--porcelain') or git('rev-parse','HEAD')!=metadata['commit']:
            raise RuntimeError('source changed while freezing')
        metadata['freeze_status']='frozen'
    except BaseException as error:
        metadata.update(freeze_status='failed',error=str(error))
        raise
    finally:
        metadata['artifacts']={p.name:digest(p) for p in output.iterdir() if p.is_file() and p.name!='metadata.json'}
        save()


if __name__=='__main__':
    main()
