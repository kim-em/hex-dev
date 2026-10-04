from pathlib import Path
import json,statistics
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
native=json.loads((HERE/'root-pairs/analysis.json').read_text())['cases']
external=json.loads((HERE.parent/'real-algebraic-poly-roots-comparison-after/analysis.json').read_text())['completed_observations']
fig,axes=plt.subplots(1,2,figsize=(10.6,5.2),sharey=True)
for ax,family,degrees in zip(axes,['Rational','Quadratic'],[[2,4,8],[1,2,4]]):
 for arm,color in [('Before','#c45b46'),('After','#256eaa')]:
  rows=[native[f'{family}Roots{n}'] for n in degrees]
  ys=[r[arm.lower()+'_median_ms'] for r in rows]
  low=[min(a['median_ms'] for a in r['arms'] if a['arm']==arm) for r in rows]
  high=[max(a['median_ms'] for a in r['arms'] if a['arm']==arm) for r in rows]
  ax.plot(degrees,ys,'o-',color=color,label='Hex '+arm.lower())
  ax.fill_between(degrees,low,high,color=color,alpha=.12)
 for backend,color in [('Z3','#668343'),('Flint','#95629c')]:
  ys=[statistics.median(x['per_call_nanos']/1e6 for x in external if x['family']==family and x['degree']==n and x['backend']==backend and not x['protocol']) for n in degrees]
  ax.plot(degrees,ys,'s--',color=color,label=('Z3 RCF' if backend=='Z3' else 'FLINT qqbar')+' (retained reference)')
 ax.set_xscale('log',base=2);ax.set_xticks(degrees,[str(n) for n in degrees]);ax.set_yscale('log');ax.grid(True,alpha=.22);ax.set_xlabel('Polynomial degree');ax.set_title('Xⁿ − 2' if family=='Rational' else 'Xⁿ − √2')
axes[0].set_ylabel('Milliseconds per operation (log scale)')
axes[1].legend(fontsize=8,loc='upper left')
fig.suptitle('Canonical real roots: certified isolation reuse',fontsize=14)
fig.text(.5,.015,'Native: four adjacent AB/BA pairs per degree; band = all observed native values.\nExternal curves reuse edb3ef9566 observations; they are not paired with the new native samples.',ha='center',fontsize=8)
fig.tight_layout(rect=[0,.09,1,.94])
for extension in ['png','svg','pdf']:fig.savefig(HERE/('roots-comparison.'+extension),dpi=180)
