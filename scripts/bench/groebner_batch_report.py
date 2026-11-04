#!/usr/bin/env python3
"""Verify retained bounded monomial-batch observations and regenerate the report."""
import argparse
from collections import Counter
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import source,require,mean
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_xor_report import sweep,verify_checks
from scripts.bench.groebner_comparator_report import msolve


def kernels(cap,a,b):
    status=cap.json('batch/kernel-status.json')
    require(status['manifest']=={'A':a,'B':b} and status['threads']==1,'kernel sources/thread differ')
    require(status['binary_sha256']==status['binary_sha256_after']==
            {arm:m['binary_sha256']['bench']for arm,m in [('A',a),('B',b)]},'kernel binaries differ')
    rows=status['samples'];shapes=['monomialProducts','productWide','productMisses'];sizes=[256,512,1024,2048,4096]
    expected=[f'complexity/{f}/{a}'for f in shapes for a in ['A','B']]
    expected += [f'matched/{f}/b{block}-{n}-{a}'for block in [0,1]for f in shapes for n in sizes
                 for a in (['A','B']if block==0 else['B','A'])]
    require([r['label']for r in rows]==expected and len(rows)==66,'kernel schedule differs')
    matched={};flags=Counter()
    for row in rows:
        label=row['label'];result=cap.json('batch/kernels/'+label+'/result.json')['results'][0]
        require(row['exit_code']in [0,2] and all(p['status']=='ok'for p in result['points']),'kernel failure')
        require(row['cpu']==rows[0]['cpu'] and row['function']in shapes,'kernel affinity/function differs')
        require(result['function']=='Hex.Groebner.Bench.'+row['function'],'kernel result function differs')
        require(row['command'][row['command'].index('--target-inner-nanos')+1]=='500000000','kernel duration differs')
        if label.startswith('matched/'):
            require(len(result['points'])==1,'matched kernel point count differs')
            point=result['points'][0];n=point['param'];block=int(label.split('/')[2][1]);arm=row['arm']
            require(label==f'matched/{row["function"]}/b{block}-{n}-{arm}' and n in sizes,'kernel case differs')
            matched[row['function'],n,block,arm]=point
            flags[row['function']]+=int(point['below_signal_floor'])
        else:
            require([(p['trial_index'],p['param'])for p in result['points']]==
                    [(trial,n)for trial in range(3)for n in sizes],'kernel trial-major schedule differs')
    answer={}
    for f in shapes:
        ratios=[]
        for n in sizes:
            points=[matched[f,n,block,arm]for block in [0,1]for arm in ['A','B']]
            require(len({p['result_hash']for p in points})==1,'complete kernel hashes differ')
            for block in [0,1]:ratios.append(matched[f,n,block,'B']['per_call_nanos']/matched[f,n,block,'A']['per_call_nanos'])
        answer[f]=dict(ratio=mean(ratios),minimum=min(ratios),maximum=max(ratios),flags=flags[f])
    return answer


class Comparator:
    def __init__(self,cap,name):self.cap,self.name=cap,name
    def json(self,path):return self.cap.json(path.replace('batch/msolve/','batch/'+self.name+'/'))
    def read(self,path):return self.cap.read(path.replace('batch/msolve/','batch/'+self.name+'/'))
    def text(self,path):return self.read(path).decode()


def normalized(value):
    result=[]
    for row in value['generators']:
        coefficients={}
        for powers,c in row:
            key=tuple(powers);coefficients[key]=(coefficients.get(key,0)+c)%value['p']
        terms=tuple(sorted((powers,c)for powers,c in coefficients.items()if c))
        if terms:result.append(terms)
    return sorted(set(result))


def analyze(cap):
    a,b=[source(cap,label)for label in ['baseline','batch']]
    x,y=[listing(m['source_manifest'])for m in [a,b]]
    require(set(x)==set(y) and {p for p in x if x[p]!=y[p]}=={
        'HexGroebner/Monomial.lean','HexGroebner/ffi/monomial_hit.c','bench/HexGroebner/Bench/Products.lean'},'runtime change scope differs')
    require(a['compilers']==b['compilers'] and a['native_options']==b['native_options'] and
            b['native_options']['hexGroebnerAVX512']is False,'production compiler/options differ')
    identity=verify_checks(cap,b);observations=[]
    for label,count,flags in [('f2-false',10,{'A':'false','B':'false'}),('prime-control',14,{'A':None,'B':None})]:
        for suffix in ['', '-repeat']:
            name=label+suffix
            if 'batch/'+name+'/metadata.json'in cap.payloads:
                observations.append((name,sweep(cap,'batch/'+name,a,b,flags,count)))
        if len(observations)>=2 and observations[-1][0].endswith('-repeat'):
            require(observations[-1][1]['metadata']['input_sha256']==observations[-2][1]['metadata']['input_sha256'],'repeat inputs differ')
    f2counts={'cyclic':2,'kat':2,'eco':2,'noon':2,'reimer':2,'minrank':2,'dense-quadratic':2,'mq':6}
    for label,row in observations:
        if label.startswith('f2'):
            require(Counter(s['family']for s in row['metadata']['samples'])=={k:2*v for k,v in f2counts.items()} and
                    all(s['p']==2 for s in row['metadata']['samples']),'F2 coverage differs')
    comparisons=[]
    for label,counts,moduli,paired in [('msolve-f2',f2counts,{2},'f2-false'),
            ('msolve-prime',None,{32003,2147483647},'prime-control')]:
        if 'batch/'+label+'/metadata.json'not in cap.payloads:continue
        rec,meta=msolve(Comparator(cap,label),'batch',expected_families=counts,moduli=moduli)
        baseline=next(r for name,r in observations if name==paired)['metadata']
        require(meta['requested_scheduling']=={'A':'degree','B':None} and
                meta['requested_dense_pivots']=={'A':'false','B':None},'comparator controls differ')
        families={r['case']:r['family']for r in baseline['samples']}
        require(all(r['family']==families[r['case']]for r in meta['samples']),'comparator families differ')
        require({r['case']for r in meta['samples']}=={r['case']for r in baseline['samples']},'comparator case set differs')
        for case in {r['case']for r in meta['samples']}:
            raw=cap.json(f'batch/{paired}/inputs/{case}.json');inp=cap.json(f'batch/{label}/inputs/{case}.json')
            require(raw['p']==inp['p'] and raw['variables']==inp['variables'] and
                    raw['order']==inp['order']=='grevlex' and normalized(raw)==normalized(inp),'comparator ideal differs')
            for block in [0,1]:
                require(cap.json(f'batch/{label}/{case}-b{block}-A.stdout')['basis']==
                        cap.json(f'batch/{paired}/{case}-b{block}-B.stdout')['basis'],'comparator complete basis differs')
        comparisons.append((label,rec,meta))
    return a,b,identity,observations,kernels(cap,a,b),comparisons


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--initial',type=Path,required=True)
    parser.add_argument('--capsule',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--current',action='store_true')
    args=parser.parse_args();initial,final=[Capsule(p)for p in [args.initial,args.capsule]]
    results=[analyze(c)for c in [initial,final]]
    if args.current:
        current=source_identity();require(all(current[k]==v for k,v in results[-1][2].items()if k!='source_commit'),'current sources differ')
    require(results[0][0]==results[1][0],'baseline differs between experiments')
    versions={k:v['version'].splitlines()[0].split(' (')[0]for k,v in results[-1][1]['compilers'].items()}
    lines=['# Bounded monomial batch insertion','',
        'Product slices preflight up to 64 terms and 4096 charged work units in a private virtual table. Successful slices publish stable monomial identifiers, collision links, metadata and the final workspace together. Widening, rehashing, malformed representations and exhausted allowances defer the unchanged table. The portable contract and its scalar-equivalence theorem cover the expanded admission. Explicit borrowed aliases retain their contents; marked-linear copies preserve their mark.','',
        f'Manual shared-host measurements use one algorithm thread, leased CPUs and adjacent AB followed by BA. Native C uses {versions["native"]}; Lean-generated C uses SDK {versions["lean"]}. Production AVX-512 is disabled. All completed samples, variability, memory and failures are retained. Each inconclusive unchanged full-system campaign has at most one repeat. The revised source has separate observations after the alias fix.','',
        '| Source | Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU | Peak RSS A/B KiB |',
        '|---|---|---:|---:|---:|---:|---:|---:|']
    for a,b,identity,obs,ks,comparisons in results:
        for label,row in obs:
            samples=row['metadata']['samples'];rss=[max(r['peak_rss_kib']for r in samples if r['arm']==arm)for arm in ['A','B']]
            lines.append(f"| {b['source_fingerprint']} | {label} | {row['process']:.6f} | {row['candidate']:.6f} | {row['balanced']:.6f} | {row['minimum']:.6f}–{row['maximum']:.6f} | {row['metadata']['cpu']} | {rss[0]}/{rss[1]} |")
    lines+=['','| Source / comparison | Family | Process B/A |','|---|---|---:|']
    for a,b,identity,obs,ks,comparisons in results:
        for label,row in obs:
            for family,ratio in row['families'].items():
                lines.append(f"| {b['source_fingerprint']} / {label} | {family} | {ratio:.6f} |")
    lines+=['','All full-system pairs return equal complete reduced bases with no failures or timeouts. These are development inputs: fourteen systems in seven families over 32003 and 2147483647, plus ten F2 systems in eight families. F2 inputs include ordinary polynomial squares, degenerations and three seeded quadratic systems. The comparator receives canonical generators of the same ideals. This is not the fixed balanced acceptance suite or a held-out evaluation.','',
        '| Source | Kernel | B/A | Pair range | Matched below-signal-floor flags |','|---|---|---:|---:|---:|']
    for a,b,identity,obs,ks,comparisons in results:
        for name,row in ks.items():lines.append(f"| {b['source_fingerprint']} | {name} | {row['ratio']:.6f} | {row['minimum']:.6f}–{row['maximum']:.6f} | {row['flags']} |")
    lines+=['','Each kernel experiment retains six fixed trial-major complexity invocations and sixty adjacent matched invocations over sizes 256–4096. Every matched complete-data hash agrees. Matched flags and outliers remain in the aggregates; the complexity runs and their flags are retained separately. The missing-product kernel improves; lookup-only overhead and full-system variability limit the conclusion.','',
        '| Source | Comparator suite | Hex/msolve | Equal-family | Pair range | CPU | Peak RSS Hex/msolve KiB |','|---|---|---:|---:|---:|---:|---:|']
    for a,b,identity,obs,ks,comparisons in results:
        for label,row,meta in comparisons:
            lines.append(f"| {b['source_fingerprint']} | {label} | {row['geomean']:.6f} | {row['family_balanced_geomean']:.6f} | {row['minimum']:.6f}–{row['maximum']:.6f} | {meta['cpu']} | {row['peak_rss_kib']['A']}/{row['peak_rss_kib']['B']} |")
    lines+=['','| Source / comparator | Family | Hex/msolve |','|---|---|---:|']
    for a,b,identity,obs,ks,comparisons in results:
        for label,row,meta in comparisons:
            for family,ratio in row['per_family'].items():
                lines.append(f"| {b['source_fingerprint']} / {label} | {family} | {ratio:.6f} |")
    lines+=['','msolve commit `3672113ee2c696a2ac9c637636e0f7214f500ba1` uses Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. Compiler and tuning differences are part of the observed gap. Hex remains behind msolve overall on these inputs. No fastest-open-source milestone or language-impossibility claim follows. Candidate production, certificate generation, independent native verification and kernel checking remain separate; only candidate/process performance is timed here.','',
        'Both source versions pass all twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project gates. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. Revised tests construct RC=1 tables directly, compare all output arenas, cover spare-capacity growth, every borrowed arena alias, marked-linear buffers, intra-table aliases and malformed forward/cyclic links. The `compute-reference` executable uses full initialization of the same native arithmetic; it is not a portable-arithmetic timing.','']
    for cap,result in zip([initial,final],results):
        a,b,identity,*_=result
        lines.append(f"Runtime `{b['source_fingerprint']}`; checks `{identity['checks_fingerprint']}`. `{cap.path.name}`: SHA-256 `{cap.sha256}`.")
    lines+=['',f'Regenerate with `python3 scripts/bench/groebner_batch_report.py --initial reports/bench-results/raw/{args.initial.name} --capsule reports/bench-results/raw/{args.capsule.name} --report reports/bench-results/hexgroebner-monomial-batches.md --check`. Add `--current` to bind the checkout.','']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report differs')
    else:args.report.write_text(text)
    print('verified both source trees, checks, full bases, kernels and comparator observations')


if __name__=='__main__':main()
