#!/usr/bin/env python3
"""Plot retained exact-operation observations without fitting complexity models."""
from pathlib import Path
import hashlib
import json
from statistics import median
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DATA = ROOT / 'reports/bench-results'
inputs = {}

def read(name):
    p = DATA / name
    inputs[name] = hashlib.sha256(p.read_bytes()).hexdigest()
    return json.loads(p.read_text())

def curve(ax, result, label, unit=1e6):
    ss = result['trial_summaries']
    xs = np.array([s['param'] for s in ss])
    ys = np.array([s['median_per_call_nanos'] / unit for s in ss])
    low = np.array([s['min_per_call_nanos'] / unit for s in ss])
    high = np.array([s['max_per_call_nanos'] / unit for s in ss])
    line, = ax.plot(xs, ys, 'o-', label=label, lw=2, ms=5)
    ax.fill_between(xs, low, high, color=line.get_color(), alpha=.13)
    # Include every completed trial, including leading points excluded by old model verdicts.
    for point in result['points']:
        if point['status'] != 'ok':
            raise ValueError('Non-completed observation needs explicit censored rendering')
        ax.scatter(point['param'], point['per_call_nanos'] / unit,
                   color=line.get_color(), alpha=.3, s=12)
    ax.set_xscale('log', base=2)
    ax.set_xticks(xs, [f'{x:,}' for x in xs])
    ax.grid(alpha=.2)
    return xs, ys

def save(fig, stem, note):
    fig.text(.02, .012, note, fontsize=8, color='#444444')
    fig.tight_layout(rect=(0,.065,1,.95))
    for fmt in ['png', 'svg', 'pdf']:
        fig.savefig(HERE / f'{stem}.{fmt}', dpi=170)
    plt.close(fig)

plt.rcParams.update({'font.size': 10, 'axes.spines.top':False, 'axes.spines.right':False})
short = read('sturm-short-chain-degree/results.json')['results']
short = {r['function'].split('.')[-1]:r for r in short}
prepared = read('prerequisite-prepared-query-degree/prepared-query.json')['results']
fig, axes = plt.subplots(1,3,figsize=(15,4.7))
fig.suptitle('Sturm: elapsed time and memory versus polynomial size', fontsize=16)
for key,label in [('runSparseQuery','Complete rational query'),('runSparseInteger','Complete integer query'),('runSparsePrepared','Prepared rational query')]:
    curve(axes[0], short[key], label)
axes[0].set(title='Sparse head 2Xⁿ − 1, query 1 on (−1,1)',xlabel='Head degree n',ylabel='Time per call (ms)')
axes[0].legend(fontsize=8)
for r,label in zip(prepared,['Value query','Certificate query']):
    curve(axes[1],r,label,unit=1e9)
axes[1].set(title='Fixed head X² − 2, query Xᵐ + 1',xlabel='Query degree m',ylabel='Time per call (seconds)')
axes[1].legend(fontsize=8)
for r,label in zip(prepared,['Value query','Certificate query']):
    ps = sorted({p['param'] for p in r['points']})
    vals = [median([p['peak_rss_kb']/1048576 for p in r['points'] if p['param']==m]) for m in ps]
    axes[2].plot(ps,vals,'o-',label=label,lw=2)
axes[2].set_xscale('log',base=2);axes[2].set_xticks(ps,[f'{x:,}' for x in ps])
axes[2].set(title='Growing query: whole-child peak RSS',xlabel='Query degree m',ylabel='Peak RSS (GiB)')
axes[2].grid(alpha=.2);axes[2].legend(fontsize=8)
save(fig,'sturm-growth','Shared host chungus2, AMD EPYC 9455; 4 trials per rung. Dots: every trial; shaded area: min–max.\nRetained source scopes: c5efa57c (head degree), 4f44b806 (query degree). Prepared inputs excluded; whole-child RSS includes preparation. No fitted curve or budget line.')

arr = read('prerequisite-readiness-models/arrays.json')['results']
roots = read('real-algebraic-root-phases/results.json')['results']
fig,axes=plt.subplots(1,3,figsize=(15,4.7));fig.suptitle('Real algebraic operations: cheap list handling, expensive canonical arithmetic',fontsize=16)
for r,label in zip(arr,['Root-list construction','Membership scan','Access stored root set']):
    curve(axes[0],r,label,unit=1e3)
axes[0].set(title='Stored roots of a repeated-factor polynomial',xlabel='Stored list length',ylabel='Time per call (µs)');axes[0].legend(fontsize=8)
curve(axes[1],roots[1],'Merge sort',unit=1e3)
axes[1].set(title='Sort distinct rational root records',xlabel='Root count',ylabel='Time per call (µs)');axes[1].legend(fontsize=8)
ops=['Add','Sub','Mul','Div','Neg','Inv','NatPow','IntPow']
x=np.arange(len(ops));width=.38
for j,arm in enumerate(['Hard','HardBare']):
    vals=[];lo=[];hi=[]
    for op in ops:
        runs=[]
        for block in range(4):
            r=read(f'real-algebraic-hard-arithmetic/{op}-{block}-{arm}.json')['results'][0]
            if not r['hashes_agree']:raise ValueError('Result hashes disagree')
            ns=[p['total_nanos']/p['inner_repeats'] for p in r['points']]
            runs.append(median(ns)/1e6)
        vals.append(median(runs));lo.append(min(runs));hi.append(max(runs))
    vals=np.array(vals)
    axes[2].bar(x+(j-.5)*width, vals,width,label=['Real-algebraic wrapper','Bare number-field parent'][j],yerr=[vals-np.array(lo),np.array(hi)-vals],capsize=2)
axes[2].set_xticks(x,ops,rotation=35);axes[2].set_yscale('log')
axes[2].set(title='Fixed inputs of degrees 6 and 2',ylabel='Time per call (ms, log scale)');axes[2].legend(fontsize=8)
axes[2].grid(axis='y',alpha=.2)
save(fig,'real-algebraic-costs','Shared host; all retained trials shown, including leading points from earlier model checks. Sources: 4f44b806 (lists), 6d78bf3 (sort/arithmetic).\nArithmetic fixture: positive root of X⁶−2 and √3; Add/Sub yield degree 12 and take ≈6.5 s. Fixed-size bars do not establish a growth rate. Paired wrappers return identical complete hashes.')

external=read('sturm-external-comparisons/analysis.json')
fig,axes=plt.subplots(1,2,figsize=(12,4.7));fig.suptitle('Exact Sturm query comparisons: Chebyshev T₈ on (−2,2)',fontsize=16)
queries=['Count','Mixed','Negative','Common'];x=np.arange(4);width=.26
# Native medians come from the adjacent native arms of each comparator pair.
for j,backend in enumerate(['Native','Z3','Flint']):
    vals=[]
    for fixture in queries:
        rows=[r for r in external['summary'] if r['fixture']==fixture]
        vals.append(median([r['native_median_us'] for r in rows]) if backend=='Native' else next(r['external_median_us'] for r in rows if r['comparator']==backend))
    axes[0].bar(x+(j-1)*width,vals,width,label={'Native':'Hex Sturm','Z3':'Z3 RCF','Flint':'FLINT qqbar driver'}[backend])
axes[0].set_xticks(x,['1','X','X − 1','T₈']);axes[0].set_yscale('log');axes[0].set(xlabel='Query polynomial',ylabel='Complete query (µs, log scale)');axes[0].legend(fontsize=8);axes[0].grid(axis='y',alpha=.2)
for j,backend in enumerate(['Z3','Flint']):
    rows=[next(r for r in external['summary'] if r['fixture']==fixture and r['comparator']==backend) for fixture in queries]
    raw=[r['median_paired_external_over_native'] for r in rows]
    adj=[r['median_paired_protocol_adjusted_external_over_native'] for r in rows]
    xpos=x+(j-.5)*.32
    axes[1].bar(xpos,raw,.3,label=f'{backend}: raw external / Hex')
    axes[1].scatter(xpos,adj,marker='_',s=100,color='black',zorder=3)
axes[1].axhline(1,color='#333333',ls='--',lw=1);axes[1].set_yscale('log');axes[1].set_xticks(x,['1','X','X − 1','T₈'])
axes[1].set(xlabel='Query polynomial',ylabel='Paired ratio (>1: Hex faster)');axes[1].legend(fontsize=8);axes[1].grid(axis='y',alpha=.2)
save(fig,'external-fixed-comparison','4 adjacent AB/BA pairs per endpoint, identical complete result hashes; source bc94cd3e, pinned Z3 4.15.4 / FLINT 3.6.\nExternal timings include JSON and cleanup; black ticks subtract measured protocol median. FLINT uses generic qqbar Horner evaluation (Common especially costly).\nThese are fixed-degree observations, not size-growth evidence or a portable ranking.')
(HERE/'plot-inputs.json').write_text(json.dumps({'input_sha256':inputs,'scope':'Replot retained raw observations; no new measurements, model fits, sample rejection or phase advancement.'},indent=2)+'\n')
print('Generated three figures in PNG, SVG and PDF; recorded every input checksum.')
