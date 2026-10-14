#!/usr/bin/env python3
"""Plot all retained paired complete-root batches and ratios without a scaling fit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('analysis',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    data=json.loads(args.analysis.read_text())
    cases={r['case']:r for r in data['comparisons']}
    if data['observations']!=96 or set(cases)!={f+str(n) for f in ('Rational','Quadratic') for n in (2,4,6,8)}:
        parser.error('expected the registered complete 96-arm comparison')
    args.output.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({'svg.hashsalt':data['sources']['After'],'pdf.fonttype':42,
                         'font.size':9,'axes.spines.top':False,'axes.spines.right':False})
    outputs=[]
    for stem,ratio in [('paired-times',False),('paired-ratios',True)]:
        fig,axes=plt.subplots(1,2,figsize=(10,4.6),sharey=True)
        for ax,family,title in zip(axes,('Rational','Quadratic'),('Integer roots 1,...,N','Quadratic factors X²-p')):
            series=[('before_over_after',0,'#2864ad','Before / after')] if ratio else [
                ('before_ms',-.10,'#2864ad','Before'),('after_ms',.10,'#c96719','After')]
            for field,offset,color,label in series:
                summaries=[cases[family+str(n)][field] for n in (2,4,6,8)]
                xs=[n+offset for n in (2,4,6,8)]
                for x,s in zip(xs,summaries):
                    if s['samples']!=6 or len(s['values'])!=6:
                        parser.error('a case lost a retained batch')
                    ax.scatter([x+(i-2.5)*.015 for i in range(6)],s['values'],s=12,color=color,alpha=.4)
                ax.errorbar(xs,[s['median'] for s in summaries],
                    yerr=[[s['median']-s['minimum'] for s in summaries],
                          [s['maximum']-s['median'] for s in summaries]],
                    color=color,label=label,marker='o',markersize=4,capsize=3,linewidth=1.1)
            if ratio:
                ax.axhline(1,color='#666666',linestyle='--',linewidth=.8)
                ax.set_ylim(bottom=0)
            else:
                ax.set_yscale('log')
            ax.set_title(title);ax.set_xticks((2,4,6,8));ax.set_xlim(1.5,8.5)
            ax.set_xlabel('Distinct real roots = input degree');ax.grid(axis='y',alpha=.2)
        axes[0].set_ylabel('Paired before / after' if ratio else 'Complete roots + exact consumer (ms)')
        axes[0].legend(frameon=False,fontsize=8)
        fig.suptitle('Complete Thom encodings in generic root comparison',fontsize=12)
        context=(f"Before {data['sources']['Before'][:10]}; after {data['sources']['After'][:10]}; "
                 f"{data['host']}, CPU {data['cpu']}")
        fig.text(.5,.025,'Six paired batches; medians and full ranges; every point retained. No scaling fit.\n'+context,
                 ha='center',va='bottom',fontsize=8)
        fig.tight_layout(rect=(0,.12,1,.94))
        for extension in ('png','svg','pdf'):
            path=args.output/(stem+'.'+extension)
            meta=({'CreationDate':None,'ModDate':None} if extension=='pdf' else {'Date':None} if extension=='svg' else {})
            fig.savefig(path,dpi=180,metadata=meta);outputs.append(dict(path=path.name,sha256=digest(path)))
        plt.close(fig)
    (args.output/'figure-source.json').write_text(json.dumps(dict(sources=data['sources'],
        analysis_sha256=digest(args.analysis),script_sha256=digest(__file__),command=sys.argv,
        python=sys.version,matplotlib=matplotlib.__version__,runtime_library_path=os.environ.get('LD_LIBRARY_PATH'),
        figures=outputs),indent=2)+'\n')


if __name__=='__main__':
    main()
