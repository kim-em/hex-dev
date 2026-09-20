#!/usr/bin/env python3
"""Summarize complete adjacent policy pairs without treating exhaustion as success.

Incomplete collections have no acceptance verdict. Native gate time comes only
from lean-bench; interpreted construction uses the fresh-module wall time.
Search-only interpreted clocks remain diagnostic phase attribution.
"""
import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path
from statistics import median

CORPUS={'secp256k1','P384','Curve448','P521'}


def continuation(e):
    return e.get('requestedB2') is not None and e.get('candidates',0)>0 and not e.get('reason')


def category(name):
    fields=name.split('-')
    if fields[0]=='extra':
        return ('opportunity-' if int(fields[2])<=4093 else 'miss-')+fields[1]
    if fields[0]=='parent':
        return 'opportunity-'+fields[1]
    if name in CORPUS:
        return 'field-corpus'
    return fields[0]


def summarize(paths, interpreted=False):
    records=[]
    modes=set()
    complete=True
    sources=[]
    root=Path(__file__).resolve().parents[2]
    inputs=[json.loads(l) for l in (root/'conformance-fixtures/HexPrimality/pminusone-stage2.jsonl').read_text().splitlines()]
    subjects={(r['bits'],r['q']):r['n'] for r in inputs if r['family']=='primitive'}
    for path in paths:
        raw=path.read_bytes()
        data=gzip.decompress(raw) if path.suffix=='.gz' else raw
        rows=[json.loads(l) for l in data.splitlines()]
        sources.append({'path':str(path),'sha256':hashlib.sha256(data).hexdigest()})
        modes.add(rows[0]['mode'])
        complete &= rows[-1]['type']=='complete'
        records.extend(r for r in rows if r['type']=='sample' and r.get('exit_code')==0)
    by_case=defaultdict(lambda:defaultdict(list))
    keys=set()
    for row in records:
        assert type(row['enabled']) is bool and 0<=row['block']<8
        key=(row['case'],row['seed'],row['block'],row['enabled'])
        assert key not in keys, f'duplicate measured arm: {key}'
        keys.add(key)
        if not interpreted:
            assert row['lean_bench']['status']=='ok'
            assert row['repeats']==row['lean_bench']['inner_repeats']
            assert row['elapsed_ns']==row['lean_bench']['total_nanos']
        by_case[(row['case'],row['seed'])][row['enabled']].append(row)
    assert len(modes)==1
    if modes=={'factor'}:
        names={f"extra-{r['bits']}-{r['q']}" for r in inputs if r['family']=='integration'}
        names|={f'balanced-{bits}' for bits in range(32,81,8)}
        names|={f'smooth-{i}' for i in range(8)}|{f'table-{i}' for i in range(16)}
        expected={(name,seed) for name in names for seed in range(5)}
    else:
        assert modes in ({'parents'},{'interpreted'})
        names=CORPUS|{f"parent-{r['bits']}-{r['q']}" for r in inputs if r['family']=='primitive'}
        names|={f'smooth-{bits}' for bits in (31,61,123,256,511,512)}
        names|={f'table-{n}' for n in (2,3,7,23,97,997,65521)}|{f'balanced-{i}' for i in range(3)}
        expected={(name,0) for name in names}
    assert set(by_case)<=expected
    complete &= set(by_case)==expected
    summaries=[]
    groups=defaultdict(list)
    for (name,seed),arms in sorted(by_case.items()):
        if any(len(arms[arm])!=8 for arm in (False,True)):
            complete=False
        if not all(arms[arm] for arm in (False,True)):
            continue
        for arm in (False,True):
            outcomes={json.dumps(r['result'],sort_keys=True) for r in arms[arm]}
            assert len(outcomes)==1, f'nondeterministic checked outcome: {name}, {seed}, {arm}'
        results={arm:arms[arm][0]['result'] for arm in (False,True)}
        checked={arm:results[arm]['checked'] for arm in (False,True)}
        events=[e for e in results[True]['events'] if continuation(e)]
        target=arms[True][0]['n']
        if name.startswith('parent-'):
            _,bits,q=name.split('-')
            target=subjects[(int(bits),int(q))]
        opportunity_events=[e for e in events if e.get('subject')==target]
        timings={arm:[(r['wall_seconds'] if interpreted else r['elapsed_ns']/r['repeats']/1e9)
                      for r in arms[arm]] for arm in (False,True)}
        cat=category(name)
        summary={'case':name,'seed':seed,'family':cat,
                 'samples_disabled':len(arms[False]),'samples_enabled':len(arms[True]),
                 'checked_disabled':checked[False],'checked_enabled':checked[True],
                 'continuations':len(events),'opportunity_continuations':len(opportunity_events),'continuation_factors':sum(e['outcome']=='factor' for e in events),
                 'all_continuations_miss':bool(events) and all(e['outcome']=='noFactor' for e in events),
                 'attempts_disabled':results[False]['attempts'],'attempts_enabled':results[True]['attempts'],
                 'median_disabled_s':median(timings[False]),'median_enabled_s':median(timings[True]),
                 'ratio':median(timings[True])/median(timings[False]),
                 'gain':checked[True] and not checked[False],
                 'loss':checked[False] and not checked[True]}
        summaries.append(summary)
        groups[cat].append((summary,timings))
        if modes!={'factor'} and summary['all_continuations_miss']:
            groups['miss-construction'].append((summary,timings))
    families=[]
    for name,entries in sorted(groups.items()):
        success_entries=[(s,t) for s,t in entries if s['checked_disabled'] and s['checked_enabled']
                         and s['opportunity_continuations']>0]
        chosen=success_entries if name.startswith('opportunity') else entries
        ratio=None
        if chosen:
            ratio=median(v for _,t in chosen for v in t[True])/median(v for _,t in chosen for v in t[False])
        families.append({'family':name,'cases':len(entries),
                         'checked_disabled':sum(s['checked_disabled'] for s,_ in entries),
                         'checked_enabled':sum(s['checked_enabled'] for s,_ in entries),
                         'gains':sum(s['gain'] and s['opportunity_continuations']>0 for s,_ in entries),
                         'losses':sum(s['loss'] for s,_ in entries),
                         'participating_cases':sum(s['continuations']>0 for s,_ in entries),
                         'timing_cases':len(chosen),'median_ratio':ratio})
    useful=any(f['family'].startswith('opportunity') and
               (f['gains']>0 or (f['median_ratio'] is not None and f['median_ratio']<=0.9)) for f in families)
    controls=[f for f in families if f['family'].startswith('miss') or f['family'] in ('balanced','smooth','table')]
    regression=any(f['family'].startswith('miss') for f in controls) and all(f['median_ratio'] is not None and f['median_ratio']<=1.1 for f in controls)
    retained=not any(s['loss'] for s in summaries)
    return {'complete':complete,'timing':'fresh-module wall time' if interpreted else 'lean-bench fixed child',
            'sources':sources,'expected_sample_count':16*len(expected),
            'sample_count':len(records),'case_count':len(by_case),'expected_case_count':len(expected),'families':families,'cases':summaries,
            'gate':('pass' if useful and regression and retained else 'fail') if complete else 'incomplete',
            'useful':useful,'regression':regression,'retains_all_checked_successes':retained}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files',nargs='+',type=Path)
    parser.add_argument('--interpreted',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=summarize(args.files,args.interpreted)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end='')

if __name__=='__main__':
    main()
