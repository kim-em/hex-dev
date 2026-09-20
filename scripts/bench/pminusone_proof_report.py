#!/usr/bin/env python3
"""Audit fresh-module construction outcomes and baseline-subtracted family costs."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

FAMILIES = {'Parents64':10, 'Parents128':7, 'Exhausted128':3, 'Parents256':10,
            'Parents512':10, 'FullMiss':2, 'Fields':2, 'Smooth':6, 'Table':7, 'Balanced':3}

def summarize(path):
    raw=path.read_bytes()
    data=gzip.decompress(raw) if path.suffix=='.gz' else raw
    record=json.loads(data)
    assert record['measurement_state']=='complete'
    assert record['config']['samples']==8
    assert record['config']['import_baseline_control']=='imports'
    results=record['results']
    assert set(results)==set(FAMILIES)|{'imports'}
    cases={}; families=[]
    for family,count in FAMILIES.items():
        result=results[family]
        samples=result['samples']
        assert len(samples)==8
        expected={}
        for sample in samples:
            round_index=sample['round']
            assert sample['build_order']==(['reference','candidate'] if round_index%2 else ['candidate','reference'])
            for role,enabled in [('reference',False),('candidate',True)]:
                rows=[json.loads(line) for line in sample[role]['compiler_output'].splitlines()
                      if line.startswith('{"case":')]
                assert len(rows)==count, (family,role,len(rows))
                names=set()
                for row in rows:
                    name=row['case'];names.add(name)
                    assert row['enabled']==enabled
                    key=(name,enabled)
                    value=row['result']
                    if key in cases: assert cases[key]==value, f'nondeterministic result: {key}'
                    else: cases[key]=value
                assert len(names)==count
                if role in expected: assert expected[role]==names
                expected[role]=names
        assert expected['reference']==expected['candidate']
        names=expected['reference']
        disabled=sum(cases[(n,False)]['checked'] for n in names)
        enabled=sum(cases[(n,True)]['checked'] for n in names)
        losses=[n for n in names if cases[(n,False)]['checked'] and not cases[(n,True)]['checked']]
        gains=[n for n in names if cases[(n,True)]['checked'] and not cases[(n,False)]['checked']]
        ref=result['median_reference_workload_wall_nanos']
        cand=result['median_candidate_workload_wall_nanos']
        resolved=result['workload_ratio_resolution']=='resolved'
        families.append({'family':family, 'cases':count, 'checked_disabled':disabled,
                         'checked_enabled':enabled, 'losses':losses,'gains':gains,
                         'median_disabled_workload_s':ref/1e9,
                         'median_enabled_workload_s':cand/1e9,
                         'ratio':cand/ref if ref>0 and cand>0 else None,
                         'resolution':result['workload_ratio_resolution'],
                         'resolved_useful':family in ('Parents64','Parents128') and
                             resolved and cand>0 and cand<=0.9*ref})
    assert len(cases)==120
    release=record['validity']['release_quality']
    return {'source':str(path),'sha256':hashlib.sha256(data).hexdigest(),
            'measurement_release_quality':release,'families':families,
            'retains_all_checked_successes':not any(f['losses'] for f in families),
            'checked_disabled':sum(f['checked_disabled'] for f in families),
            'checked_enabled':sum(f['checked_enabled'] for f in families),
            'resolved_usefulness':release and any(f['resolved_useful'] for f in families),
            'interpretation':'Construction-search attribution; unresolved regression timings do not pass a default-enable gate.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=json.dumps(summarize(args.file),indent=2)+'\n'
    if args.output: args.output.write_text(result)
    else: print(result,end='')
