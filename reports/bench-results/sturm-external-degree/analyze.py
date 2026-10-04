#!/usr/bin/env python3
"""Join every retained count pair and plot measured times, not model fits."""
from pathlib import Path
import csv
import json
from statistics import median
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

HERE=Path(__file__).resolve().parent
meta=json.loads((HERE/'metadata.json').read_text())
if not (meta['source_unchanged'] and meta['binary_unchanged']):
    raise SystemExit('Source or executable changed during collection')
observations=[]
failed=[]
for arm in meta['arms']:
    output=HERE/arm['output']
    if not output.exists():
        failed.append({**arm,'reason':'no result file'});continue
    r=json.loads(output.read_text())['results'][0]
    if arm['exit_code'] or r['budget_truncated'] or any(p['status']!='ok' for p in r['points']):
        failed.append({**arm,'result':r});continue
    if r['expected_hash_check']['status']!='match' or not r['hashes_agree']:
        raise ValueError('Exact expected-result/hash check failed')
    ns=median(p['total_nanos']/p['inner_repeats'] for p in r['points'])
    observations.append({**arm,'per_call_nanos':ns,'hash':r['observed_hash'],
                         'peak_rss_kb':max(p['peak_rss_kb'] for p in r['points'])})
# Preserve failed and censored observations explicitly. No rerun or filter is used.
summary=[];pairs=[]
for degree in meta['degrees']:
    for backend in ['Flint','Z3']:
        group=[p for p in observations if p['degree']==degree and p['comparator']==backend]
        joined=[]
        for block in range(4):
            native=next((p for p in group if p['block']==block and p['backend']=='Native'),None)
            external=next((p for p in group if p['block']==block and not p['protocol'] and p['backend']==backend),None)
            protocol=next((p for p in group if p['block']==block and p['protocol']),None)
            if not (native and external and protocol):continue
            if not (native['hash']==external['hash']==protocol['hash']):
                raise ValueError('Full result hashes differ between arms')
            n,e,p=[r['per_call_nanos'] for r in [native,external,protocol]]
            if e<=p:raise ValueError('Adjusted timing is below measured protocol floor')
            joined.append(dict(degree=degree,backend=backend,block=block,native_nanos=n,
                               external_nanos=e,protocol_nanos=p,raw_ratio=e/n,adjusted_ratio=(e-p)/n))
        pairs.extend(joined)
        if joined:
            summary.append(dict(degree=degree,backend=backend,complete_pairs=len(joined),
                 native_ms=median(p['native_nanos'] for p in joined)/1e6,
                 external_ms=median(p['external_nanos'] for p in joined)/1e6,
                 protocol_us=median(p['protocol_nanos'] for p in joined)/1e3,
                 raw_ratio=median(p['raw_ratio'] for p in joined),
                 adjusted_ratio=median(p['adjusted_ratio'] for p in joined),
                 hex_raw_ratio=median(p['native_nanos']/p['external_nanos'] for p in joined),
                 hex_adjusted_ratio=median(p['native_nanos']/(p['external_nanos']-p['protocol_nanos']) for p in joined),
                 protocol_fraction=median(p['protocol_nanos'] for p in joined)/median(p['external_nanos'] for p in joined)))
result=dict(source_commit=meta['source_commit'],summary=summary,pairs=pairs,failed_or_censored=failed,
            completed_observations=observations,classification=meta['classification'])
(HERE/'analysis.json').write_text(json.dumps(result,indent=2)+'\n')
with (HERE/'summary.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(summary[0]),lineterminator='\n');w.writeheader();w.writerows(summary)
plt.rcParams['svg.hashsalt']='hex'
fig,ax=plt.subplots(1,2,figsize=(12,4.8))
fig.suptitle('Exact root count: Hex Sturm, Z3 RCF and FLINT qqbar',fontsize=16)
for backend,label in [('Native','Hex Sturm'),('Z3','Z3 RCF'),('Flint','FLINT qqbar driver')]:
    xs=[];ys=[];low=[];high=[]
    for degree in meta['degrees']:
        vals=[p['per_call_nanos']/1e6 for p in observations if p['degree']==degree and p['backend']==backend and not p['protocol']]
        if vals:
            xs.append(degree);ys.append(median(vals));low.append(min(vals));high.append(max(vals))
    line,=ax[0].plot(xs,ys,'o-',label=label,lw=2)
    ax[0].fill_between(xs,low,high,color=line.get_color(),alpha=.13)
    for p in observations:
        if p['backend']==backend and not p['protocol']:
            ax[0].scatter(p['degree'],p['per_call_nanos']/1e6,s=12,color=line.get_color(),alpha=.3)
for backend in ['Z3','Flint']:
    rows=[s for s in summary if s['backend']==backend]
    line,=ax[1].plot([s['degree'] for s in rows],[s['hex_raw_ratio'] for s in rows],'o-',label=f'{backend}: raw',lw=2,color={'Z3':'#ff7f0e','Flint':'#2ca02c'}[backend])
    ax[1].plot([s['degree'] for s in rows],[s['hex_adjusted_ratio'] for s in rows],'--',color=line.get_color(),label=f'{backend}: protocol-adjusted')
ax[1].axhline(1,color='#444444',ls=':',lw=1)
for a in ax:
    a.set_xscale('log',base=2);a.set_xticks(meta['degrees'],meta['degrees']);a.set_yscale('log');a.grid(alpha=.2);a.legend(fontsize=8);a.set_xlabel('Chebyshev degree n (coefficient height also grows)')
ax[0].set_ylabel('Complete query time per call (ms, log scale)')
ax[1].set_ylabel('Hex / external (>1: Hex slower)')
fig.text(.015,.015,f"Shared host {meta['host']}, leased CPU {meta['cpu']}; 4 adjacent AB/BA pairs per backend/rung. Exact result n on (−2,2).\nPrepared inputs; root/chain production, checks, JSON and cleanup timed. No driver root cache. All samples retained; no fitted model.\nSource {meta['source_commit'][:9]}; protocol-adjusted curves are framing controls, not isolated pure algorithm timings. Failed/censored observations: {len(failed)}.",fontsize=8)
fig.tight_layout(rect=(0,.1,1,.95))
for fmt in ['png','svg','pdf']:
    p=HERE/f'comparison.{fmt}'
    metadata={'Date':None} if fmt=='svg' else {'CreationDate':None} if fmt=='pdf' else None
    fig.savefig(p,dpi=170,metadata=metadata)
    if fmt=='svg':p.write_text('\n'.join(line.rstrip() for line in p.read_text().splitlines())+'\n')
print(json.dumps(summary,indent=2))
