#!/usr/bin/env python3
"""Verify retained scalar-XOR measurements and regenerate their report."""
import argparse
import hashlib
import math
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_trie_report import source, require, mean
from scripts.bench.groebner_retirement_report import listing
from scripts.bench.groebner_comparator_report import msolve


def close(actual, expected, message):
    require(math.isclose(actual, expected, rel_tol=1e-12), message)


def sweep(capsule, label, a, b, flags, count=10):
    metadata = capsule.json(label+'/metadata.json')
    recorded = capsule.json(label+'/analysis.json')
    require(metadata['source_unchanged'] and metadata['threads'] == 1 and
            metadata['source_manifest'] == b['source_manifest'] and metadata['baseline_manifest'] == a and
            metadata['binary_sha256'] == metadata['binary_sha256_after'] ==
            {'A':a['binary_sha256']['compute'],'B':b['binary_sha256']['compute']}, 'sweep source/ELF binding differs')
    require(metadata['requested_scheduling'] == {'A':'degree','B':'degree'} and
            metadata['requested_dense_pivots'] == flags, 'sweep controls differ')
    samples = metadata['samples']
    order = [r['case'] for r in samples if r['block'] == 0 and r['arm'] == 'A']
    require(len(order) == len(set(order)) == count and len(samples) == count*4 and
            [(r['case'],r['block'],r['arm']) for r in samples] ==
            [(case,block,arm) for block in [0,1] for case in order for arm in (['A','B'] if block == 0 else ['B','A'])],
            'AB/BA schedule differs')
    for name,digest in metadata['input_sha256'].items():
        require(hashlib.sha256(capsule.read(label+'/inputs/'+name)).hexdigest() == digest, 'sweep input differs')
    index = {(r['case'],r['block'],r['arm']):r for r in samples}
    families = {}; process = []; candidate = []
    for case in order:
        inp = capsule.json(label+'/inputs/'+case+'.json')
        for block in [0,1]:
            pair = [index[case,block,arm] for arm in ['A','B']]
            outputs = []
            for row in pair:
                arm = row['arm']; command = row['command']
                require(row['status'] == 'ok' and row['returncode'] == 0 and row['complete_basis_equal'], 'sample failed')
                if flags[arm] is None:
                    require('--dense-pivots'not in command,'unexpected explicit dense control')
                else:
                    require(command[command.index('--dense-pivots')+1] == flags[arm], 'dense control differs')
                output = capsule.json(f'{label}/{case}-b{block}-{arm}.stdout')
                require(output['kind'] == 'unchecked_candidate' and output['p'] == inp['p'] and
                        output['variables'] == inp['variables'] and output['order'] == inp['order'] == 'grevlex' and
                        output['scheduling'] == 'degree', 'candidate contract differs')
                stats = dict(row['statistics'])
                require(stats.pop('candidate_nanos') == output['candidateNanos'] and stats == output['statistics'] and
                        int(capsule.text(f'{label}/{case}-b{block}-{arm}.rss')) == row['peak_rss_kib'], 'sample counters/RSS differ')
                outputs.append(output)
            process.append(pair[1]['wall_nanos']/pair[0]['wall_nanos'])
            candidate.append(outputs[1]['candidateNanos']/outputs[0]['candidateNanos'])
            families.setdefault(pair[0]['family'],[]).append(process[-1])
            for output in outputs:
                output.pop('candidateNanos'); output['statistics'].pop('work'); output['statistics'].pop('allocatedBytes')
            require(outputs[0] == outputs[1], 'complete bases or other counters differ')
    expected = dict(geomean=mean(process),median=statistics.median(process),minimum=min(process),maximum=max(process),
                    family_balanced_geomean=mean([mean(v) for v in families.values()]))
    for key,value in expected.items(): close(recorded[key],value,'recorded '+key+' differs')
    require(recorded['samples'] == count*4 and recorded['complete_bases_equal'] == count*2 and
            recorded['timeouts'] == recorded['failed_processes'] == 0 and set(recorded['per_family']) == set(families), 'sweep coverage differs')
    if count == 14:
        require({row['p'] for row in samples} == {32003,2147483647} and
                set(families) == {'cyclic','kat','eco','noon','reimer','minrank','dense-quadratic'} and
                all(len(rows) == 4 for rows in families.values()), 'prime-field suite coverage differs')
    for key,values in families.items(): close(recorded['per_family'][key],mean(values),'family ratio differs')
    return dict(process=mean(process),candidate=mean(candidate),balanced=expected['family_balanced_geomean'],
                minimum=min(process),maximum=max(process),families=recorded['per_family'],metadata=metadata)


def verify_checks(capsule, manifest):
    identity=capsule.json('identity.json');text=capsule.text('checks.manifest')
    require(identity['source_fingerprint']==manifest['source_fingerprint'] and
            identity['source_manifest_sha256']==hashlib.sha256(manifest['source_manifest'].encode()).hexdigest() and
            identity['checks_manifest_sha256']==hashlib.sha256(text.encode()).hexdigest(), 'check identities differ')
    for path,oid in listing(text).items():
        data=capsule.read('checks-sources/'+path)
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,'check source differs')
    native=capsule.json('native-status.json');full=capsule.json('full-status.json')
    require([r['name']for r in native]==['clang','gcc'] and all(r['variants']==[
        'Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'] and
        r['sanitize']==['address','undefined']for r in native),'native variants differ')
    require([r['name']for r in full]==['build','oracles','driver','bench','dag','phase4','manifest','headers','lines'],
            'project coverage differs')
    require(all(r['exit_code']==0 and all(r[k]==v for k,v in identity.items())for r in native+full),'failed/stale checks')
    require('clang version 23.1.3'in capsule.text('native-clang.log') and
            '16.2.0'in capsule.text('native-gcc.log'),'sanitizer compiler differs')
    require('567 unique reduced bases match SymPy'in capsule.text('full/oracles.log') and
            '567 reduced bases match Singular'in capsule.text('full/oracles.log'),'independent oracle coverage differs')
    return identity


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capsule',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--current',action='store_true')
    args=parser.parse_args();cap=Capsule(args.capsule)
    before,after=[source(cap,label)for label in ['baseline','xor']]
    a,b=listing(before['source_manifest']),listing(after['source_manifest'])
    require(set(a)==set(b) and {p for p in a if a[p]!=b[p]}=={'HexGroebner/ffi/matrix_scan.c'},'runtime edit differs')
    path='root-sources/HexGroebner/ffi/matrix_scan.c';original=cap.text('baseline/'+path)
    needle='    if(a>=p) return 0;\n'
    addition=('    /* In F2 validation gives b=1 and a,factor in {0,1}. Keep the same\n'
              '       validation/error prefix, then subtract by exact XOR. */\n'
              '    if(p==2) {wr(data+(size_t)j*w,w,a^factor);return 1;}\n')
    require(original.count(needle)==1 and cap.text('xor/'+path)==original.replace(needle,needle+addition,1),
            'scalar shortcut differs')
    require(before['compilers']==after['compilers'] and before['native_options']==after['native_options'],
            'production compiler/options differ')
    identity=verify_checks(cap,after)
    if args.current:
        current=source_identity()
        require(all(current[k]==v for k,v in identity.items()if k!='source_commit'),'current sources differ')
    observations=[]
    for label,count,flags in [('f2-false',10,{'A':'false','B':'false'}),
                              ('prime-control',14,{'A':None,'B':None}),
                              ('prime-control-repeat',14,{'A':None,'B':None})]:
        observations.append((label,sweep(cap,'xor/'+label,before,after,flags,count)))
    require(observations[1][1]['metadata']['input_sha256']==observations[2][1]['metadata']['input_sha256'],
            'unchanged control inputs differ')
    comparison,meta=msolve(cap,'xor',10)
    require(meta['requested_scheduling']=={'A':'degree','B':None} and
            meta['requested_dense_pivots']=={'A':'false','B':None},'comparator controls differ')
    from scripts.oracle.groebner_singular import expression
    def normalized(value):
        result=[]
        for row in value['generators']:
            coefficients={}
            for powers,c in row:
                key=tuple(powers);coefficients[key]=(coefficients.get(key,0)+c)%2
            terms=tuple(sorted((powers,c)for powers,c in coefficients.items()if c))
            if terms:result.append(terms)
        return sorted(set(result))
    for case in {r['case']for r in meta['samples']}:
        raw=cap.json('xor/f2-false/inputs/'+case+'.json')
        value=cap.json('xor/msolve/inputs/'+case+'.json')
        require(raw['p']==value['p']==2 and raw['variables']==value['variables'] and
                raw['order']==value['order']=='grevlex' and normalized(raw)==normalized(value), 'comparator ideal differs')
        text=','.join('x'+str(i)for i in range(value['variables']))+'\n2\n'+',\n'.join(expression(g)for g in value['generators'])+'\n'
        require(all(c for g in value['generators']for powers,c in g) and
                cap.text('xor/msolve/inputs/'+case+'.ms')==text,'canonical export differs')
        for block in [0,1]:
            require(cap.json(f'xor/msolve/{case}-b{block}-A.stdout')['basis']==
                    cap.json(f'xor/f2-false/{case}-b{block}-B.stdout')['basis'],'comparator basis differs')
    lines=['# Scalar characteristic-two subtraction','',
           'The scalar sparse-row update keeps its existing validation and failure prefix. For modulus two, validation gives source coefficient one and target/factor values in {0,1}; subtraction then uses exact XOR. The runtime change adds only this shortcut. Ordinary polynomial powers, including squares, retain their usual meaning.','',
           'These manual shared-host measurements use one algorithm thread, automatically leased CPUs and adjacent AB followed by BA. Every completed process is retained. The inconclusive prime control has exactly one unchanged repeat; the F2 comparison has no repeat. Native C uses Clang 21.1.8 and Lean-generated C uses SDK Clang 23.1.0. Production AVX-512 is disabled. Candidate production, native verification, certificate generation and kernel checking are distinct; only candidate/process times appear below.','',
           '| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Process pair range |',
           '|---|---:|---:|---:|---:|']
    for label,row in observations:
        lines.append(f"| {label} | {row['process']:.6f} | {row['candidate']:.6f} | {row['balanced']:.6f} | {row['minimum']:.6f}–{row['maximum']:.6f} |")
    lines+=['','All 152 processes (76 pairs) return equal complete bases, with no failures or timeouts. The F2 development suite improves; the prime controls do not establish a general timing benefit. These inputs are not the fixed balanced acceptance suite or held-out inputs. No fastest-open-source milestone is claimed.','',
            '| Family | F2 | Prime first | Prime repeat |','|---|---:|---:|---:|']
    for family in observations[0][1]['families']:
        values=[f"{r['families'][family]:.6f}"if family in r['families']else'—'for _,r in observations]
        lines.append('| '+family+' | '+' | '.join(values)+' |')
    lines+=['','| Comparison | Leased CPU | Peak RSS A/B (KiB) |','|---|---:|---:|']
    for label,row in observations:
        samples=row['metadata']['samples']
        rss=[max(r['peak_rss_kib']for r in samples if r['arm']==arm)for arm in ['A','B']]
        lines.append(f"| {label} | {row['metadata']['cpu']} | {rss[0]}/{rss[1]} |")
    lines.append(f"| msolve | {meta['cpu']} | {comparison['peak_rss_kib']['A']}/{comparison['peak_rss_kib']['B']} |")
    lines+=['','The ten F2 systems comprise seven centered signed lifts of the existing prime-field families and three seeded quadratic systems (8, 9 and 10 variables) including squares. Degenerations and zero terms are retained in the A/B inputs. The comparator receives canonical generators for the same ideals. These are development observations, with unequal input counts by family; both input-weighted and equal-family aggregates are shown.','',
            f"A separate current comparison with msolve `{meta['msolve_commit']}` completes forty processes with twenty equal full bases. Hex/msolve process ratios are {comparison['geomean']:.6f} by input and {comparison['family_balanced_geomean']:.6f} with equal family weights, with pair range {comparison['minimum']:.6f}–{comparison['maximum']:.6f}. msolve uses Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. This leaves a performance gap.",'',
            '| F2 family | Hex/msolve |','|---|---:|']
    for family,ratio in comparison['per_family'].items():lines.append(f'| {family} | {ratio:.6f} |')
    lines+=['','All twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project checks pass. Existing conformance covers native/portable sparse updates, malformed prefixes, aliases, budgets, resumptions and complete F4 outputs. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. The `compute-reference` executable is the full-initialization build of the same native driver; its name does not imply portable arithmetic.','',
            f"Baseline runtime `{before['source_fingerprint']}`; XOR runtime `{after['source_fingerprint']}`; checks `{identity['checks_fingerprint']}`. The capsule includes both full runtime source trees, the check source tree, compiler identities, raw process output, complete bases, memory, variability and collector scripts.",
            f"`{args.capsule.name}`: SHA-256 `{cap.sha256}`.",'',
            'Regenerate with `python3 scripts/bench/groebner_xor_report.py --capsule reports/bench-results/raw/'+args.capsule.name+' --report reports/bench-results/hexgroebner-xor.md --check`. Add `--current` to bind the checkout.','']
    text='\n'.join(lines)
    if args.check:require(args.report.read_text()==text,'report differs; regenerate')
    else:args.report.write_text(text)


if __name__=='__main__':main()
