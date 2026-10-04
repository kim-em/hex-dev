#!/usr/bin/env python3
"""Plot all retained query or scalar observations with failures kept visible."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from statistics import median
import matplotlib
matplotlib.use('Agg')
matplotlib.rcParams['svg.hashsalt']='real-algebraic-readiness'
import matplotlib.pyplot as plt


def read_result(path):
    if not path.exists():return None,'missing export'
    result=json.loads(path.read_text())['results'][0]
    points=result['points']
    if not points or any(p['status']!='ok' for p in points):return result,'failed or censored batch'
    if result.get('kind')=='fixed':
        if result.get('expected_hash_check',{}).get('status')!='match' or not result.get('hashes_agree'):
            raise ValueError(f'Exact result guard failed: {path}')
    hashes={p['result_hash'] for p in points}
    if len(hashes)!=1:raise ValueError(f'Result changed: {path}')
    return result,None


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--kind',choices=('scalar','sturm'),required=True)
    args=p.parse_args();root=args.input;meta=json.loads((root/'metadata.json').read_text())
    output=args.output;output.mkdir(parents=True,exist_ok=True)
    rows,failures=[],[]
    if args.kind=='scalar':
        for arm in meta['arms']:
            r,error=read_result(root/arm['output'])
            if error or arm['exit_code']:
                failures.append(dict(arm=arm,reason=error,result=r));continue
            rows.append(dict(**arm,nanos=median(pt['total_nanos']/pt['inner_repeats'] for pt in r['points']),
                             result_hash=r['observed_hash']))
        fig,axes=plt.subplots(2,3,figsize=(15,9))
        for ax,operation in zip(axes.flat,meta['families']):
            sizes=meta['families'][operation]
            for backend,control in [('Native',False),('Flint',False),('Z3',False),('Flint',True),('Z3',True)]:
                selected=[r for r in rows if r['operation']==operation and r['arm']==backend and r['control']==control]
                color={('Native',False):'#1f77b4',('Flint',False):'#ff7f0e',('Z3',False):'#2ca02c',('Flint',True):'#d62728',('Z3',True):'#9467bd'}[(backend,control)]
                xs=[];ys=[];lo=[];hi=[]
                for size in sizes:
                    values=[r['nanos']/1e6 for r in selected if r['size']==size]
                    if not values:continue
                    xs.append(size);ys.append(median(values));lo.append(min(values));hi.append(max(values))
                    ax.scatter([size]*len(values),values,s=10,alpha=.25,color=color)
                if not xs:continue
                line,=ax.plot(xs,ys,':o' if control else '-o',label=backend+(' protocol' if control else ''),color=color)
                ax.fill_between(xs,lo,hi,color=line.get_color(),alpha=.1)
            failed=[f for f in failures if f['arm']['operation']==operation]
            if failed:ax.text(.02,.98,f'{len(failed)} failed/censored arms; see analysis.json',transform=ax.transAxes,va='top',fontsize=8)
            ax.set_title(operation);ax.set_xscale('log',base=2);ax.set_yscale('log')
            ax.set_xticks(sizes,sizes);ax.set_ylabel('Operation + exact result guard (ms)')
            ax.set_xlabel('Algebraic degree' if operation in ['Add','Sqrt'] else 'Coefficient bits' if operation=='Rational' else 'Separation exponent k (shift 2⁻ᵏ)')
            ax.grid(alpha=.2);ax.legend(fontsize=8)
        fig.suptitle('Shipped real-algebraic scalar APIs vs FLINT qqbar and Z3 RCF')
        footer='Prepared operands; native arithmetic checks canonical polynomial/sign and external arithmetic checks exact annihilation/sign.\nNo expected algebraic root is prepared. External JSON/cleanup remain timed; protocol curves are separate, without subtraction.\nMissing Z3 floor/ceil arms denote an unavailable matching API. Whole-child caps include setup; see retained failures.'
    else:
        for run in meta['runs']:
            if run['label']=='reduced-declared-ladder':continue
            trial,size,backend=run['label'].split('-');r,error=read_result(root/(run['label']+'.json'))
            if error or run['exit_code']:
                failures.append(dict(run=run,reason=error,result=r));continue
            rows.append(dict(trial=int(trial[5:]),size=int(size),backend=backend,
                             nanos=median(pt['per_call_nanos'] for pt in r['points']),
                             peak_rss_mib=run['peak_rss_kib']/1024,result_hash=r['points'][0]['result_hash']))
        for trial in range(4):
            for size in sorted({r['size'] for r in rows}):
                pair=[r for r in rows if r['trial']==trial and r['size']==size]
                if len(pair)==2 and pair[0]['result_hash']!=pair[1]['result_hash']:
                    raise ValueError('Paired signed query values differ')
        fig,axes=plt.subplots(1,2,figsize=(12,5))
        for ax,field,label in [(axes[0],'nanos','Kernel time (ms)'),(axes[1],'peak_rss_mib','Whole-invocation peak RSS (MiB)')]:
            for backend in ['original','reduced']:
                xs=[];ys=[];lo=[];hi=[]
                for size in sorted({r['size'] for r in rows}):
                    values=[r[field]/(1e6 if field=='nanos' else 1) for r in rows if r['size']==size and r['backend']==backend]
                    if not values:continue
                    xs.append(size);ys.append(median(values));lo.append(min(values));hi.append(max(values))
                    ax.scatter([size]*len(values),values,s=10,alpha=.3)
                line,=ax.plot(xs,ys,'o-',label=backend);ax.fill_between(xs,lo,hi,color=line.get_color(),alpha=.15)
            ax.set_xscale('log',base=2);ax.set_yscale('log');ax.set_xlabel('Query degree m: Xᵐ + 1, head X² − 2')
            ax.set_ylabel(label);ax.grid(alpha=.2);ax.legend()
        fig.suptitle('Remainder-only Sturm value query: runtime and storage')
        footer='Four adjacent AB/BA arms per rung, identical rational value-only inputs; no unrelated integer certificate in preparation.\nKernel timings exclude preparation. Peak RSS includes preparation, child execution and native process baseline.\nAll complete signed-result hashes agree. The paired ladder is descriptive evidence, not a complexity verdict.'
    fig.text(.015,.018,footer+f'\nSource {meta["source"][:10]}, {meta["host"]}, leased CPU {meta["cpu"]}. All completed arms and failures retained; no load filtering or rerun.',fontsize=8)
    fig.tight_layout(rect=(0,.16,1,.94))
    stem='scalar-comparison' if args.kind=='scalar' else 'sturm-reduced-comparison'
    for fmt in ['png','svg','pdf']:
        fig.savefig(output/(stem+'.'+fmt),dpi=160,metadata={'Date':None} if fmt=='svg' else {'CreationDate':None} if fmt=='pdf' else None)
    (output/'analysis.json').write_text(json.dumps(dict(observations=rows,failures=failures),indent=2)+'\n')
    print(f'{len(rows)} complete arms; {len(failures)} failed/censored arms')


if __name__=='__main__':main()
