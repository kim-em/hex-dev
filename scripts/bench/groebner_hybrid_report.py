#!/usr/bin/env python3
"""Verify retained sampled-F4 policy comparisons and regenerate their report."""
import argparse
import hashlib
import math
import statistics
from collections import Counter
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import source,require,mean
from scripts.bench.groebner_xor_report import verify_checks
from scripts.bench.groebner_comparator_report import msolve


def campaign(cap,label,manifest,*,sampled_baseline,block,zeros,minimum=0,count=14):
    meta=cap.json(label+'/metadata.json');rec=cap.json(label+'/analysis.json')
    require(meta['source_unchanged'] and meta['threads']==1 and
            meta['source_manifest']==manifest['source_manifest'] and meta['baseline_manifest']==manifest,'source/threads differ')
    keys={'A':'sample'if sampled_baseline else'compute','B':'sample'}
    require(meta['binary_sha256']==meta['binary_sha256_after']==
            {arm:manifest['binary_sha256'][key]for arm,key in keys.items()},'executables differ')
    require(meta['sampled'] and meta['baseline_sampled']==sampled_baseline and
            meta['requested_scheduling']=={'A':'degree','B':'degree'},'algorithm controls differ')
    require(meta['sampling_controls']['seed']==10987 and meta['sampling_controls']['block_rows']==block and
            meta['sampling_controls']['total_zero_tests']==zeros and meta['sampling_controls'].get('minimum_targets',0)==minimum,'sampling controls differ')
    if sampled_baseline:require(meta['baseline_sampling_min_targets']==0,'baseline cutoff differs')
    for name,digest in meta['input_sha256'].items():
        require(hashlib.sha256(cap.read(label+'/inputs/'+name)).hexdigest()==digest,'input differs')
    samples=meta['samples'];order=[r['case']for r in samples if r['block']==0 and r['arm']=='A']
    require(len(order)==len(set(order))==count and len(samples)==4*count and
            [(r['case'],r['block'],r['arm'])for r in samples]==[(case,round,arm)for round in [0,1]for case in order for arm in (['A','B']if round==0 else['B','A'])],'AB/BA schedule differs')
    index={(r['case'],r['block'],r['arm']):r for r in samples};ratios=[];candidate=[];families={};sampling={}
    for case in order:
        inp=cap.json(label+'/inputs/'+case+'.json')
        for round in [0,1]:
            pair=[index[case,round,arm]for arm in ['A','B']];outputs=[]
            for row in pair:
                arm=row['arm'];value=cap.json(f'{label}/{case}-b{round}-{arm}.stdout')
                require(row['status']=='ok'and row['returncode']==0 and row['complete_basis_equal'],'failed sample')
                require(value['kind']=='unchecked_candidate'and value['p']==inp['p']and value['variables']==inp['variables'] and
                        value['order']==inp['order']=='grevlex'and value['scheduling']=='degree','candidate identity differs')
                counters=dict(row['statistics']);require(counters.pop('candidate_nanos')==value['candidateNanos'] and counters==value['statistics'],'counter record differs')
                require(int(cap.text(f'{label}/{case}-b{round}-{arm}.rss'))==row['peak_rss_kib'],'RSS differs')
                if sampled_baseline or arm=='B':
                    cutoff=minimum if arm=='B'else 0
                    require(value['algorithm']=='f4-sampled' and value['seed']==10987 and value['blockRows']==block and value['totalZeroTests']==zeros and value.get('minimumTargets',0)==cutoff,'sampled policy differs')
                    require(value['randomState']==(10987+value['sampling']['randomWords']*0x9e3779b97f4a7c15)%2**64,'advanced random state differs')
                else:require(value['randomState']==0,'deterministic random state differs')
                outputs.append(value)
            require(outputs[0]['basis']==outputs[1]['basis'] and outputs[0]['batchSize']==outputs[1]['batchSize'],'complete bases/contract differ')
            ratios.append(pair[1]['wall_nanos']/pair[0]['wall_nanos']);candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
            families.setdefault(pair[0]['family'],[]).append(ratios[-1])
            if sampled_baseline:
                counters=sampling.setdefault(pair[0]['family'],{'callsA':0,'callsB':0,'wordsA':0,'wordsB':0})
                for arm,value in zip(['A','B'],outputs):
                    counters['calls'+arm]+=value['sampling']['calls']
                    counters['words'+arm]+=value['sampling']['randomWords']
    expected=dict(geomean=mean(ratios),family_balanced_geomean=mean([mean(v)for v in families.values()]),median=statistics.median(ratios),minimum=min(ratios),maximum=max(ratios))
    require(all(math.isclose(rec[key],value,rel_tol=1e-12)for key,value in expected.items()),'recorded ratios differ')
    require(rec['samples']==4*count and rec['complete_bases_equal']==2*count and rec['failed_processes']==rec['timeouts']==0,'coverage differs')
    require(set(rec['per_family'])==set(families)and all(math.isclose(rec['per_family'][k],mean(v),rel_tol=1e-12)for k,v in families.items()),'family ratios differ')
    require(({r['p']for r in samples}=={32003,2147483647}and len(families)==7 and all(len(v)==4 for v in families.values()))if count==14 else
            {r['p']for r in samples}=={2}and Counter(r['family']for r in samples)=={'cyclic':4,'kat':4,'eco':4,'noon':4,'reimer':4,'minrank':4,'dense-quadratic':4,'mq':12},'field/family coverage differs')
    rss={arm:max(r['peak_rss_kib']for r in samples if r['arm']==arm)for arm in ['A','B']}
    require(rss==rec['peak_rss_kib'],'peak RSS differs')
    if sampled_baseline and minimum:
        require(sum(v['callsB']for v in sampling.values())<sum(v['callsA']for v in sampling.values()),'cutoff did not reduce sampled calls')
    return dict(rec=rec,meta=meta,candidate=mean(candidate),rss=rss,sampling=sampling)


class Comparator:
    def __init__(self,cap):self.cap=cap
    def json(self,path):return self.cap.json(path.replace('hybrid/msolve/','hybrid/msolve-prime/'))
    def read(self,path):return self.cap.read(path.replace('hybrid/msolve/','hybrid/msolve-prime/'))
    def text(self,path):return self.read(path).decode()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capsule',type=Path,required=True)
    parser.add_argument('--guards',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--direct',type=Path,required=True)
    parser.add_argument('--check',action='store_true');parser.add_argument('--current',action='store_true')
    args=parser.parse_args();cap=Capsule(args.capsule);guards=Capsule(args.guards);direct_cap=Capsule(args.direct)
    baseline,hybrid=[source(cap,label)for label in ['baseline','hybrid']]
    require(baseline['compilers']==hybrid['compilers']and baseline['native_options']==hybrid['native_options'] and
            baseline['binary_sha256']['compute']==hybrid['binary_sha256']['compute'] and
            baseline['binary_sha256']['compute-reference']==hybrid['binary_sha256']['compute-reference'],'deterministic drivers or production options changed')
    require(source(direct_cap,'hybrid')==hybrid,'direct comparison runtime differs')
    initial_identity=verify_checks(cap,hybrid);guard_manifest=source(guards,'hybrid');identity=verify_checks(guards,guard_manifest)
    require(guard_manifest==hybrid,'guard runtime differs')
    require('sampled driver: explicit zero/huge cutoff and malformed values pass on both initializers'in guards.text('full/oracles.log'),'cutoff CLI did not run in the final oracle gate')
    if args.current:
        current=source_identity();require(all(current[k]==v for k,v in identity.items()if k!='source_commit'),'current source differs')
    retained=[]
    for snapshot in ['1391d0dd95e7','332b0af770f9']:
        path=args.guards.parent/('f4-sampler-hybrid-checks-'+snapshot+'.tar.xz')
        old=Capsule(path);old_manifest=source(old,'hybrid');require(old_manifest==hybrid,'retained guard runtime differs');old_identity=verify_checks(old,old_manifest)
        require(old_identity['checks_fingerprint']==snapshot,'retained guard identity differs');retained.append((path.name,old.sha256))
    observations=[]
    for name,block,zeros in [('deterministic-prime',32,3),('deterministic-prime-b32-z1',32,1),('deterministic-prime-b128-z1',128,1),('deterministic-prime-b128-z3',128,3)]:
        observations.append((name,campaign(cap,'baseline/'+name,baseline,sampled_baseline=False,block=block,zeros=zeros)))
    observations.append(('deterministic-f2',campaign(cap,'baseline/deterministic-f2',baseline,sampled_baseline=False,block=32,zeros=3,count=10)))
    policies=[]
    for name,zeros,count in [('cutoff128-prime',1,14),('cutoff128-prime-repeat',1,14),('cutoff128-f2',3,10)]:
        policies.append((name,campaign(cap,'hybrid/'+name,hybrid,sampled_baseline=True,block=32,zeros=zeros,minimum=128,count=count)))
    direct=[]
    for name in ['hybrid-versus-deterministic-prime','hybrid-versus-deterministic-prime-repeat']:
        direct.append((name,campaign(direct_cap,'hybrid/'+name,hybrid,sampled_baseline=False,block=32,zeros=1,minimum=128)))
    require(policies[0][1]['meta']['input_sha256']==policies[1][1]['meta']['input_sha256'],'unchanged repeat input differs')
    comparison,meta=msolve(Comparator(cap),'hybrid',candidate_key='sample',moduli={32003,2147483647})
    require(meta['sampled']and meta['sampling_controls']=={'seed':10987,'block_rows':32,'total_zero_tests':1,'minimum_targets':128},'comparator policy differs')
    for row in meta['samples']:
        if row['arm']=='A':
            value=cap.json(f"hybrid/msolve-prime/{row['case']}-b{row['block']}-A.stdout")
            require(value['minimumTargets']==128 and value['totalZeroTests']==1 and value['blockRows']==32 and value['seed']==10987 and
                    value['randomState']==(10987+value['sampling']['randomWords']*0x9e3779b97f4a7c15)%2**64,'comparator random policy differs')
    cli=cap.json('hybrid/cli/status.json');require(len(cli)==12 and all(r['exit_code']==(2 if r['minimum_targets']is None else 0)for r in cli),'CLI boundary result differs')
    lines=['# Deterministic elimination below a sampling cutoff','',
        'The sampled candidate producer accepts an explicit minimum target count. Pair matrices below it use deterministic elimination after shared selection and symbolic preprocessing. The sealed continuation retains the cutoff and advanced random state. Deterministic batches consume parent allowances and no random words. The default cutoff is zero, preserving the existing policy; ordinary deterministic driver executables are byte-identical. Every output remains an unchecked candidate requiring independent complete-basis certification.','',
        'Manual shared-host observations use one algorithm thread, runtime auxiliary threads, an automatically leased CPU and adjacent AB followed by BA. All completed processes, failures, variability and RSS are retained. The prime policy and direct hybrid-versus-deterministic comparisons each have one unchanged repeat; no further unchanged repeat is collected. Native C uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0, with production AVX-512 disabled.','',
        '| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU | Peak RSS A/B KiB |','|---|---:|---:|---:|---:|---:|---:|']
    for name,row in observations+policies+direct:
        r=row['rec'];lines.append(f"| {name} | {r['geomean']:.6f} | {row['candidate']:.6f} | {r['family_balanced_geomean']:.6f} | {r['minimum']:.6f}–{r['maximum']:.6f} | {row['meta']['cpu']} | {row['rss']['A']}/{row['rss']['B']} |")
    lines+=['','The first five rows compare sampled B against deterministic A on the parent runtime `ddde8c89c095`. They retain a 2×2 prime-field comparison (block sizes 32/128 and one/three total zero tests) plus the F2 default. The three cutoff128 rows compare cutoff 128 against cutoff zero within the same sampled executable: one zero test on prime fields, three on F2. These are separate campaigns on different binaries and leased CPUs: multiplying their ratios does not establish a hybrid-versus-deterministic speedup. The final two rows directly compare the hybrid cutoff 128 against deterministic F4, using the same runtime and one unchanged repeat. These observations remain specific to the development suite and shared host. Every complete reduced basis agrees. No sampling independence or probability bound is claimed for SplitMix64.','',
        '| Family | Prime cutoff first | Prime cutoff repeat | F2 cutoff |','|---|---:|---:|---:|']
    for family in policies[-1][1]['rec']['per_family']:
        lines.append('| '+family+' | '+' | '.join(f"{row['rec']['per_family'][family]:.6f}"if family in row['rec']['per_family']else'—'for _,row in policies)+' |')
    for label,row in policies:
        improved=', '.join(k for k,v in row['rec']['per_family'].items()if v<1)
        regressed=', '.join(k for k,v in row['rec']['per_family'].items()if v>1)
        lines+=['',f'{label}: observed lower time in {improved}; observed higher time in {regressed}.']
    lines+=['','| Family | First sampled calls A/B | Repeat sampled calls A/B | F2 sampled calls A/B |',
        '|---|---:|---:|---:|']
    for family in policies[-1][1]['sampling']:
        lines.append('| '+family+' | '+' | '.join(f"{row['sampling'][family]['callsA']}/{row['sampling'][family]['callsB']}"if family in row['sampling']else'—'for _,row in policies)+' |')
    lines+=['',f"The direct hybrid-versus-deterministic comparison is inconclusive: first process B/A {direct[0][1]['rec']['geomean']:.6f}, unchanged repeat {direct[1][1]['rec']['geomean']:.6f}. The opposite directions and broad pair ranges do not establish a speedup."]
    lines+=['','The call totals verify that the cutoff actually reduced sampling; they include all completed processes. The prime cutoff reduces observed time primarily on Noon and Reimer. The F2 MQ inputs regress, so the cutoff remains explicit and no default change is selected. The cutoff 128 was selected using these development inputs; it has no held-out validation or demonstrated optimality. The cutoff comparison contains only zero and 128; it is not a sweep establishing an optimal threshold. The diagnostic suites are development inputs, not a balanced acceptance suite or held-out evaluation. Sampling counters describe sampled batches only; there is no direct counter of deterministic fallback batches.','',
        f"The current msolve comparison uses commit `{meta['msolve_commit']}`, Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. All 56 processes complete with 28 equal complete bases. Hex/msolve process geometric mean is {comparison['geomean']:.6f}, range {comparison['minimum']:.6f}–{comparison['maximum']:.6f}. Compiler/tuning differences are part of this observed gap. Candidate production, certificate generation, independent native verification and kernel checking remain separate; only candidate/process times are measured here. No fastest-open-source milestone is demonstrated.",'',
        '| Family | Hybrid Hex/msolve |','|---|---:|']
    for family,ratio in comparison['per_family'].items():lines.append(f'| {family} | {ratio:.6f} |')
    lines+=['','Both initial and final checks pass all twelve Clang/GCC ASan+UBSan variants and all nine project gates. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. Cutoff tests cover deterministic-only/no-draw operation with identical ordinary statistics, a run with strictly fewer but nonzero sampled calls, mixed one-slice resumption, deterministic-batch exhaustion after random draws, sampled-matrix exhaustion after deterministic commit, scheduling suspension, exhaustion after symbolic preprocessing has submitted a deterministic matrix, exhausted parent work and resumed policy identity. Twelve archived CLI checks cover both initializers, default/zero/huge cutoffs, repeated flags and malformed values. The existing CI runner also checks zero/two huge cutoffs and malformed values on both initializers. A failed deterministic batch is selected again on retry: changing the resumed batch-size cap can change whether it crosses the cutoff. A pending sampled matrix retains its original selection. Full initialization is the same native arithmetic, not a portable arithmetic timing.','',
        'The retained diagnostic profiles comprise four completed Eco processes, one MQ process exhausted under an accidentally omitted larger matrix-entry limit, and four corrected MQ processes. The failed command/output is retained. Profiles explain costs and are not timing comparisons. Raw trace hashes and reports are archived; raw perf data remain in the measurement workspace.','',
        f"Earlier checks remain retained and verified separately: {', '.join('`'+name+'` (SHA-256 `'+digest+'`)'for name,digest in retained)}. They are superseded by the final checks below. Direct comparison capsule `{args.direct.name}`: SHA-256 `{direct_cap.sha256}`.",'',
        f"Runtime `{hybrid['source_fingerprint']}`; initial checks `{initial_identity['checks_fingerprint']}`; final checks `{identity['checks_fingerprint']}`. `{args.capsule.name}`: SHA-256 `{cap.sha256}`. `{args.guards.name}`: SHA-256 `{guards.sha256}`.",'',
        f'Regenerate with `python3 scripts/bench/groebner_hybrid_report.py --capsule reports/bench-results/raw/{args.capsule.name} --guards reports/bench-results/raw/{args.guards.name} --direct reports/bench-results/raw/{args.direct.name} --report reports/bench-results/hexgroebner-hybrid.md --check`. Add `--current` to bind the checkout.','']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report differs')
    else:args.report.write_text(text)
    print('verified archived policies, complete bases, source/check snapshots and comparator observations'+('; checkout matches'if args.current else''))


if __name__=='__main__':main()
