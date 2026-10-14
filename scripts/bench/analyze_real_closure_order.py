#!/usr/bin/env python3
"""Audit the frozen, paired complete-root comparison before summarizing timings."""
import argparse
import hashlib
import json
import shlex
from fractions import Fraction
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.fixed_conversion_paired import validate_tower_row, check_tower_cohort
from scripts.bench.analyze_real_closure_trivial import summarize

EXE = 'hexrealclosure_trivial_bench'
FAMILIES = {'Rational':[2,4,6,8], 'Quadratic':[2,4,6,8]}
CHANGED = sorted(('HexRealClosure/RootOrder.lean','HexRealClosure/RootOrderTests.lean',
                  'adapters/HexRealClosureMathlib/RootOrder.lean',
                  'adapters/HexRealClosureMathlib/TrivialTowerTests.lean'))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def analyze(directory):
    directory = Path(directory)
    data = json.loads((directory/'metadata.json').read_text())
    if (data['mode']!='tower-order' or data['status']!='completed' or data['families']!=FAMILIES
            or data['trials']!=list(range(6)) or data['floor_seconds']!=.5
            or data['affinity']!=[data['cpu']] or data['binaries_unchanged'] is not True
            or data['panic_abort'] is not True or data['compiled_source_differences']!=CHANGED):
        raise ValueError('capture differs from the registered protocol')
    for name, expected in data['artifacts'].items():
        if Path(name).name!=name or digest(directory/name)!=expected:
            raise ValueError('retained artifact changed: '+name)
    sources = data['sources']
    if set(sources)!={'Before','After'} or sources['Before']['lean_bench_pin']!=sources['After']['lean_bench_pin']:
        raise ValueError('source arms or package pins differ')
    check_tower_cohort(sources)
    for arm, source in sources.items():
        if source['status'] or source['freeze_status']!='frozen' or source['tooling_commit']!=data['collector_commit']:
            raise ValueError('source is not frozen with the registered tooling')
        for name, expected in source['sources'].items():
            snapshot=directory/(arm+'-'+name.replace('/','-')+'.txt')
            if digest(snapshot)!=expected:
                raise ValueError('source snapshot changed: '+name)
        for name, blob in source['source_git_blobs'].items():
            content=(directory/(arm+'-'+name.replace('/','-')+'.txt')).read_bytes()
            if hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()!=blob:
                raise ValueError('source snapshot differs from Git: '+name)
        binary=source['binaries'][EXE]
        for name, expected in source['artifacts'].items():
            if name==EXE:
                if expected!=binary['sha256']:
                    raise ValueError('binary identity differs from the freeze ledger')
            elif digest(directory/(arm+'-'+name))!=expected:
                raise ValueError('frozen preparation artifact changed: '+name)
        for module in ('HexRealClosure/RootOrder','HexRealClosure/Trivial','HexRealClosure/TrivialMeasurements'):
            linked=source['linked_objects']['.lake/build/ir/'+module+'.c.o.export']
            obj=source['objects'][module]
            c_name='compiled/'+module+'.c'
            trace_name=arm+'-compiled-'+module.replace('/','-')+'.trace.txt'
            trace=json.loads((directory/trace_name).read_text())
            commands=[shlex.split(r['message'][3:]) for r in trace['log'] if r['message'].startswith('.> ')]
            if (linked['c_sha256']!=source['sources'][c_name] or linked['sha256']!=obj['sha256']
                    or type(obj['size_bytes']) is not int or obj['size_bytes']<=0
                    or commands!=[obj['command']]
                    or len(commands)!=1 or commands[0][0]!=source['compiler']
                    or [x.replace(source['cwd'],'<source>') for x in commands[0]]!=linked['command']):
                raise ValueError('linked object differs from retained generated C or compiler trace')
        if len(source['commands'])!=6 or any(c['exit_code']!=0 for c in source['commands']):
            raise ValueError('source preparation failed or incomplete')
        fixture=directory/(arm+'-conformance-fixtures-HexRealClosure-trivial-distinct.jsonl.txt')
        if (directory/(arm+'-functional.stdout.txt')).read_bytes()!=fixture.read_bytes():
            raise ValueError('native output differs from its committed fixture')
        oracle=json.loads((directory/(arm+'-oracle.stdout.txt')).read_text())
        if oracle['verified_arms']!=16 or oracle['oracle']!='python-flint 0.9.0 / FLINT 3.6.0':
            raise ValueError('exact oracle coverage differs')
        for label in ('functional','oracle'):
            if (directory/(arm+'-'+label+'.stderr.txt')).read_bytes():
                raise ValueError('functional/oracle run reported an error')
    for name in ('bench/HexRealClosure/TrivialMeasurements.lean',
                 'conformance-fixtures/HexRealClosure/trivial-distinct.jsonl','compiler-override'):
        if sources['Before']['sources'][name]!=sources['After']['sources'][name]:
            raise ValueError('matched input, consumer or compiler differs')
    expected=[(trial,family,size,arm) for trial in range(6) for family,sizes in FAMILIES.items()
              for size in sizes for arm in (('Before','After') if trial%2==0 else ('After','Before'))]
    rows=data['arms']
    if [(r['trial'],r['operation'],r['size'],r['arm']) for r in rows]!=expected:
        raise ValueError('trial-major adjacency or AB/BA order differs')
    timings={}
    details=[]
    for row in rows:
        trial,family,size,arm=row['trial'],row['operation'],row['size'],row['arm']
        label=f'{family}-{size}-{trial}-{arm}'
        target=f'Hex.RealClosure.TrivialMeasurements.{family}{size}.generic'
        command=[sources[arm]['binaries'][EXE]['path'],'run',target,'--repeats','1',
                 '--min-total-seconds','0.5','--export-file',str(Path(data['capture_root'])/(label+'.json'))]
        if row['command']!=command or row['exit_code']!=0 or row['output']!=label+'.json':
            raise ValueError('arm command differs from its source, function or export')
        export=json.loads((directory/row['output']).read_text())
        if export['export_schema_version']!=1 or len(export['results'])!=1:
            raise ValueError('benchmark export schema differs')
        result=export['results'][0]
        ms=validate_tower_row(result,target,sources[arm]['commit'])
        timings[trial,family,size,arm]=ms
        details.append(dict(**row,per_call_ms=ms,point=result['points'][0],config=result['config']))
    comparisons=[]
    for family,sizes in FAMILIES.items():
        for size in sizes:
            before=[timings[t,family,size,'Before'] for t in range(6)]
            after=[timings[t,family,size,'After'] for t in range(6)]
            comparisons.append(dict(case=family+str(size),before_ms=summarize(before),after_ms=summarize(after),
                before_over_after=summarize([b/a for b,a in zip(before,after)]),
                after_minus_before_ms=summarize([a-b for b,a in zip(before,after)])))
    return dict(sources={a:s['commit'] for a,s in sources.items()},host=data['host'],cpu=data['cpu'],
                observations=len(rows),comparisons=comparisons,raw_batches=details,
                inference='descriptive paired batches on the shared host; no significance or asymptotic claim')


def analyze_sort_rows(rows):
    """Check the untimed replay from assembly indices and production-sort ranks."""
    if [(row['index'], row['family'], row['degree']) for row in rows] != [
            (6+i, family.lower(), degree) for i, (family, degree) in
            enumerate((f,n) for f,sizes in FAMILIES.items() for n in sizes)]:
        raise ValueError('sort inventory cases differ')
    summaries=[]
    for row in rows:
        schema=row.get('comparison_schema',1)
        if type(schema) is not int or schema not in (1,2):
            raise ValueError('unknown comparison schema')
        entries=row['assembled']
        n=row['degree']
        order=row['sorted_indices']
        if (len(entries)!=n or [e['index'] for e in entries]!=list(range(n))
                or sorted(order)!=list(range(n))):
            raise ValueError('sort inventory lost an assembly index')
        rank={index:i for i,index in enumerate(order)}
        def endpoint(raw):
            if raw in ('negInf','posInf'):
                return None
            if (type(raw) is not dict or set(raw)!={'finite'} or
                    type(raw['finite']) is not list or len(raw['finite'])!=2 or
                    any(type(x) is not int for x in raw['finite']) or raw['finite'][1]<=0):
                raise ValueError('invalid finite endpoint')
            return Fraction(*raw['finite'])
        for entry in entries:
            root=entry['root']
            if 'point' not in root:
                fields={'head','indices','signs'}
                if schema==2:
                    fields|={'lower','upper'}
                if set(root)!=fields:
                    raise ValueError('descriptor inventory differs from comparison schema')
                if schema==2:
                    endpoint(root['lower'])
                    endpoint(root['upper'])
        def route(left,right):
            a,b=entries[left]['root'],entries[right]['root']
            if 'point' in a and 'point' in b:
                return 'points'
            if 'point' in a or 'point' in b:
                return 'mixed'
            if all(len(d['head'])==2 and d['head'][-1]==[1,1] for d in (a,b)):
                return 'linear'
            if a['head']==b['head'] and all(d['indices']==list(range(1,len(d['head']))) for d in (a,b)):
                return 'full'
            if schema==2:
                for left,right in ((a,b),(b,a)):
                    upper,lower=endpoint(left['upper']),endpoint(right['lower'])
                    if upper is not None and lower is not None and upper<=lower:
                        return 'interval'
            return 'common-product'
        expected=[]
        sorted_entries=[]
        for left in reversed(range(n)):
            at=0
            while at<len(sorted_entries):
                right=sorted_entries[at]
                less=rank[left]<rank[right]
                expected.append(dict(left=left,right=right,route=route(left,right),order='lt' if less else 'gt'))
                if less:
                    break
                at+=1
            sorted_entries.insert(at,left)
        if row['comparisons']!=expected or sorted_entries!=order:
            raise ValueError('sort replay differs from production ranks or comparison routes')
        summaries.append(dict(case=row['family'].capitalize()+str(n), comparisons=len(expected),
            routes={r:sum(e['route']==r for e in expected)
                    for r in (('points','mixed','linear','full','interval','common-product')
                              if schema==2 else ('points','mixed','linear','full','common-product'))}))
    return summaries


def analyze_sort_inventory(directory):
    directory=Path(directory)
    metadata=json.loads((directory/'sort-source.json').read_text())
    for name,expected in metadata['files'].items():
        if Path(name).name!=name or digest(directory/name)!=expected:
            raise ValueError('sort inventory artifact changed')
    source=(directory/'sort-benchmark.lean.txt').read_bytes()
    if hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()!=metadata['benchmark_git_blob']:
        raise ValueError('sort benchmark snapshot differs from Git blob')
    if (directory/'sort.jsonl').read_bytes()!=(directory/'sort-launcher.stdout').read_bytes():
        raise ValueError('sort inventory differs from complete launcher stdout')
    rows=[json.loads(line) for line in (directory/'sort.jsonl').read_text().splitlines()]
    # Link the earlier descriptor inventory to the new actual assembly and sort.
    selection=json.loads((directory/'selection-source.json').read_text())
    for name,expected in selection['files'].items():
        if digest(directory/name)!=expected:
            raise ValueError('selection inventory artifact changed')
    old=[json.loads(line) for line in (directory/'selection.jsonl').read_text().splitlines()]
    if len(old)!=len(rows):
        raise ValueError('selection/sort case count differs')
    for before,row in zip(old,rows):
        roots=[row['assembled'][i]['root'] for i in row['sorted_indices']]
        descriptors=[r for r in roots if 'point' not in r]
        complete=sum(d['indices']==list(range(1,len(d['head']))) for d in descriptors)
        eligible=sum(a['head']==b['head'] and all(d['indices']==list(range(1,len(d['head']))) for d in (a,b))
                     for i,a in enumerate(descriptors) for b in descriptors[i+1:])
        if (before['index']!=row['index'] or before['degree']!=row['degree']
                or before['family']!=row['family'] or before['descriptors']!=[
                    {k:d[k] for k in ('head','indices','signs')} for d in descriptors]
                or before['selected']!=len(descriptors) or before['points']!=len(roots)-len(descriptors)
                or before['full']!=complete or before['eligible_pairs']!=eligible
                or before['all_selected_pairs']!=len(descriptors)*(len(descriptors)-1)//2):
            raise ValueError('earlier selection inventory differs from actual assembled roots')
    return analyze_sort_rows(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--archive-index',type=Path)
    args=parser.parse_args()
    if args.archive_index:
        index=json.loads(args.archive_index.read_text())
        if digest(args.archive_index.parent/'capture.tar.gz')!=index['capture_sha256']:
            raise ValueError('archive digest differs')
        for name, expected in index['files'].items():
            if digest(args.directory/name)!=expected:
                raise ValueError('archive file digest differs: '+name)
    args.output.write_text(json.dumps(analyze(args.directory),indent=2)+'\n')


if __name__=='__main__':
    main()
