#!/usr/bin/env python3
"""Check and summarize all retained policy measurements and actual callback traces."""
import hashlib
import json
from pathlib import Path
from statistics import median
HERE=Path(__file__).resolve().parent
OUT=HERE/'results'/'policy'
traces={}
active=None
for line in (OUT/'trace.log').read_text().splitlines():
    parts=line.split(',')
    if parts[0]=='BEGIN': active=(int(parts[1]),int(parts[2])); traces[active]={'counts':[0,0]}
    elif parts[0]=='zero' and active is not None: traces[active]['counts'][int(parts[1])]+=1
    elif parts[0]=='END': traces[active]['hash']=int(parts[1]); active=None
assert len(traces)==40
samples=[json.loads(s) for s in (OUT/'timing'/'samples.jsonl').read_text().splitlines()]
assert len(samples)==180, len(samples)
rows=[]
for case in range(10):
    for pair in range(3):
        times=[[],[]]
        for block in range(6):
            r,=[s['report']['results'] for s in samples if (s['case'],s['pair'],s['block'])==(case,pair,block)]
            expected=[f'policy_{pair}_{case}',f'policy_{pair+1}_{case}']
            if block%2: expected.reverse()
            assert [x['function'] for x in r]==expected
            assert r[0]['observed_hash']==r[1]['observed_hash']
            for x in r:
                policy=int(x['function'].split('_')[1])
                assert int(x['observed_hash'],16)==traces[policy,case]['hash']
                assert x['hashes_agree'] and not x['budget_truncated']
                assert len(x['points'])==1 and x['points'][0]['status']=='ok'
                times[policy-pair].append(x['median_nanos']/1e6)
        ratios=[a/b for a,b in zip(*times)]
        rows.append(dict(case=case,pair=pair,a_ms=median(times[0]),b_ms=median(times[1]),
                         ratio=median(ratios),low=min(ratios),high=max(ratios)))
(OUT/'summary.json').write_text(json.dumps({'trace_source_sha256':hashlib.sha256((HERE/'PolicyTrace.lean').read_bytes()).hexdigest(),
    'trace_sha256':hashlib.sha256((OUT/'trace.log').read_bytes()).hexdigest(),
    'comparisons':rows,'zero_tests':[
    dict(policy=k[0],case=k[1],**v) for k,v in sorted(traces.items())]},indent=2)+'\n')
print('| Field / length / operation | Retain remainder (0/1) | Smaller descriptor (1/2) | Irreducible fast path (2/3) |')
print('|---|---:|---:|---:|')
for case in range(10):
    label=f"{'base' if case<6 else 'nested'} / {[2,3,4,2,3][case//2]} / {'division' if case%2==0 else 'gcd'}"
    vals=[f"{r['ratio']:.2f}× ({r['low']:.2f}–{r['high']:.2f})" for r in rows if r['case']==case]
    print('| '+label+' | '+' | '.join(vals)+' |')
