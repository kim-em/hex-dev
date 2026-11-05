#!/usr/bin/env python3
"""Replay source-bound sparse-F2 measurements and complete candidate outputs."""
from __future__ import annotations
import argparse
import hashlib
import gc
import io
import tarfile
import json
import math
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_prime_report import blobs
from scripts.bench.groebner_trie_report import require,source


def mean(values):
    return math.exp(sum(math.log(value)for value in values)/len(values))


def verification(cap,manifest):
    full=cap.json('checks/full/status.json')
    native=cap.json('checks/native/status.json')
    names=['build','oracles','driver','bench','dag','phase4','manifest','headers','lines']
    variants=['Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder']
    require([row['name']for row in full]==names and len(native)==2,'missing verification gates')
    listing=cap.text('checks/source-manifest.txt');blobs(cap,'checks/sources',listing)
    checks=hashlib.sha256(listing.encode()).hexdigest()
    runtime=hashlib.sha256(manifest['source_manifest'].encode()).hexdigest()
    identity=full[0]['source_commit'];rows=full+native
    for kind in ['forced','packed']:
        for compiler in ['clang','gcc']:
            status=cap.json(f'checks/{kind}/{compiler}/{kind}-status.json')
            require(status['build_exit_code']==0 and
                    [row['variant']for row in status['results']]==variants and
                    all(row['exit_code']==0 for row in status['results']),kind+' profile failed')
            require(status['sanitize']==['address','undefined'],'sanitizer controls differ')
            require(status['force_sparse'if kind=='forced'else'keep_packed']is True,
                    'backend control missing')
            rows.append(status)
    for row in rows:
        require(row['source_commit']==identity and row['source_manifest_sha256']==runtime and
                row['checks_manifest_sha256']==checks,'verification source identity differs')
    for row in full+native:
        require(row['exit_code']==0,'project or native verification failed')
    require({row['name']for row in native}=={'clang','gcc'} and all(
        row['variants']==variants and row['sanitize']==['address','undefined']for row in native),
        'regular strict profiles differ')
    return listing


def fixed_inputs(cap):
    raw=cap.read('checks/sources/reports/bench-results/raw/f4-fixed-corpus-v2.tar.xz')
    require(hashlib.sha256(raw).hexdigest()==
            '56ec21d063e39e27605c37456166cca47dcad446daea018d7afcd81b97782812',
            'fixed corpus archive differs')
    with tarfile.open(fileobj=io.BytesIO(raw))as archive:
        names=[m for m in archive.getmembers()if m.isfile()and m.name.endswith('/suite.json')]
        require(len(names)==1,'fixed corpus suite differs')
        suite=json.loads(archive.extractfile(names[0]).read())
    selected=[case for case in suite['cases']if case['split']=='heldout']
    require(len(selected)==27,'fixed held-out coverage differs')
    return suite['cases']


def systems(cap,candidate,baseline,fixed):
    prefix='measurements/systems';meta=cap.json(prefix+'/metadata.json')
    require(meta['manifest']==candidate and meta['threads']==1 and
            meta['source_bindings']==meta['source_bindings_after']and meta['sources_unchanged'],
            'system executable/source/thread identity changed')
    cases=meta['cases'];samples=meta['samples'];suite=cap.json(prefix+'/suite.json')
    require(suite['cases']==[case for case in fixed if case['split']=='primary'],
            'primary inputs differ from the fixed corpus')
    first=[];seen=set()
    for case in suite['cases']:
        key=case['family'],case['p']
        if case['split']=='primary'and(key not in seen or case['name']in['eco14-2','eco15-2']):
            seen.add(key);first.append(case)
    require(cases==first and len(cases)==32,'fixed system selection differs')
    expected=[(case['name'],block,arm)for block in [0,1]for case in cases
              for arm in (['A','B']if block==0 else['B','A'])]
    require([(r['case'],r['block'],r['arm'])for r in samples]==expected,'AB/BA schedule differs')
    require(len(samples)==128,'system campaign incomplete')
    indexed={key:row for key,row in zip(expected,samples)};ratios=[]
    for case in cases:
        payload=cap.read(prefix+'/'+case['name']+'.input.json');given=json.loads(payload)
        require(hashlib.sha256(payload).hexdigest()==case['input_sha256'],'input differs from fixed corpus')
        for block in [0,1]:
            outputs=[];pair=[]
            for arm,manifest in [('A',baseline),('B',candidate)]:
                row=indexed[case['name'],block,arm];pair.append(row)
                require(row['status']=='ok'and row['returncode']==0 and
                        row['complete_output_and_counters_equal'],'process failed or output differs')
                require(row['input_sha256']==case['input_sha256'],'sample input digest differs')
                binary=row['command'][0]
                require(meta['source_bindings'][binary]==manifest['binary_sha256']['compute'],
                        'sample executable differs')
                value=cap.json(prefix+'/'+case['name']+f'-b{block}-{arm}.stdout')
                require(value['kind']=='unchecked_candidate'and all(value[k]==given[k]for k in
                        ['p','variables','order']),'candidate output metadata differs')
                require(value['scheduling']=='degree'and value['binaryPivots']and
                        not value.get('densePivots',False)and value['delayedReduction'],
                        'candidate policy differs')
                require(value['candidateNanos']==row['candidate_nanos'],'candidate time differs')
                require(int(cap.text(prefix+'/'+case['name']+f'-b{block}-{arm}.rss').strip())==
                        row['peak_rss_kib'],'memory record differs')
                outputs.append({k:v for k,v in value.items()if k!='candidateNanos'})
            require(outputs[0]==outputs[1],'complete bases, metadata or counters differ')
            ratios.append(dict(case=case['name'],family=case['family'],p=case['p'],block=block,
                candidate_ratio=pair[1]['candidate_nanos']/pair[0]['candidate_nanos'],
                process_ratio=pair[1]['wall_nanos']/pair[0]['wall_nanos']))
    require(ratios==cap.json(prefix+'/paired-ratios.json'),'recorded pair ratios differ')
    return ratios,samples


def render(cap):
    candidate=source(cap,'candidate');baseline=source(cap,'baseline')
    listing=verification(cap,candidate);fixed=fixed_inputs(cap)
    ratios,samples=systems(cap,candidate,baseline,fixed)
    functional=cap.json('supplement/production-eco14-functional/status.json')
    require(functional['exit_code']==0 and functional['sources_unchanged']and
            functional['complete_basis_equal']and functional['all_statistics_equal'],
            'independent production functional check failed')
    wrapper=cap.read('supplement/lean-cc-wrapper')
    require(hashlib.sha256(wrapper).hexdigest()==candidate['compilers']['lean']['sha256'],
            'generated-C compiler wrapper differs')
    lines=['# Sparse F₂ elimination: measured snapshot','',
        f"This campaign compares frozen runtime `{candidate['source_fingerprint']}` with `{baseline['source_fingerprint']}`. Both produce unchecked complete monic reduced bases in ordinary polynomial rings; `x` and `x²` remain distinct over F₂. These observations do not establish the fastest-open-source milestone.",'',
        'Requested binary-pivot frames use borrowed sparse pivots and a UInt64 parity accumulator beyond the packed dimension ceilings. A bounded header pass also chooses sparse elimination when the packed private payload cannot fit, or even maximal four-row table savings cannot meet its word-work cap. Every table consumes four dense known rows, so their count divided by four bounds the possible savings. Each call tries one backend; successful packed admissions are preserved.','',
        'Sparse limits are 2²⁰ columns and known reducers, 4096 targets, a 2³⁸ conservative shape bound and at most 2³⁴ charged work. Extra payload is `7*columns + 40*min(rows,columns)`, reserved in addition to the complete reference payload. Unsupported or exhausted native frames release private state and continue with exact reference rows, labels and counters. A discarded prefix is bounded per frame.','',
        'All 128 processes completed and all 64 adjacent pairs have identical complete outputs and all logical counters. The fixed selection contains the first primary size of each of ten families in all three fields, plus Eco-14 and Eco-15 over F₂. Runs use one automatically leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled. Adjacent arm order alternates AB/BA.','',
        '| First-size field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |',
        '|---|---:|---:|---:|---:|']
    for p in [2,32003,2147483647]:
        selected=[r for r in ratios if r['p']==p and r['case']not in['eco14-2','eco15-2']]
        require(len(selected)==20 and len({r['family']for r in selected})==10,'field/family coverage differs')
        rss={arm:max(r['peak_rss_kib']for r in samples if r['p']==p and r['arm']==arm and
                     r['case']not in['eco14-2','eco15-2'])for arm in ['A','B']}
        values=[r['candidate_ratio']for r in selected]
        lines.append(f"| {p} | {mean(values):.4f} | {mean([r['process_ratio']for r in selected]):.4f} | {min(values):.4f}–{max(values):.4f} | {rss['A']}/{rss['B']} |")
    lines+=['','The odd-prime arithmetic routes are unchanged controls. F₂ first-size cases include header-selection overhead. These are descriptive point estimates with every completed sample and outlier retained; no control-adjusted improvement is inferred. The selection does not replace the complete fixed balanced suite or held-out acceptance.','','| In-sample F₂ case | Candidate B/A | Pair ratios |','|---|---:|---|']
    for name in ['eco14-2','eco15-2']:
        values=[r['candidate_ratio']for r in ratios if r['case']==name]
        require(len(values)==2,'targeted case coverage differs')
        lines.append(f"| {name} | {mean(values):.4f} | "+', '.join(f'{v:.4f}'for v in values)+' |')
    lines+=['','The host is AMD EPYC 9455. Native production code uses Clang 21.1.8 and Lean-generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3. Source blobs, complete outputs, build inputs, executable/compiler hashes, CPU assignment, host activity, all observations and failures are retained. Limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with the fixed corpus’s large explicit parent allowances. The data do not establish timing or admission under library default budgets.','',
        'Verification records all nine project gates and 36 strict Clang/GCC ASan/UBSan configurations: regular dispatch, forced sparse small/large frames and packed-only admission controls. Tests compare all rows, labels and eight counters, independent remainders, exact work/byte/input/output boundaries, malformed buffers, duplicate heads, shared inputs, near-UInt64 parity offsets and zero-accumulator reuse. Kernel replay and axiom audits remain separate from timed candidate production.','',
        'Certificate generation, independent native certification, kernel checking and full checked calls are excluded from these candidate timings. Finite-extension adapters, deterministic producer correctness/termination, full balanced and held-out comparator acceptance, equal-thread parallel comparisons and the overall-fastest gap remain open under issue #10987. Scientific claims use manual shared-host observations, never CI timings.','',
        f'Raw capsule `{cap.path.name}` has SHA-256 `{cap.sha256}`. Its per-payload hashes, exact runtime/check-source manifests, all 64 full-output comparisons and actual gate receipts are replayed by this generator. `--current` additionally requires the checkout’s runtime and verification sources to match the recorded snapshot.','']
    return '\n'.join(lines),candidate,listing,[case for case in fixed if case['split']=='heldout']


def comparator(cap,manifest,expected):
    from scripts.bench.groebner_comparator_report import msolve
    candidate=source(cap,'candidate')
    require(candidate==manifest,'held-out production executable/source differs')
    result,meta=msolve(cap,'candidate',expected_families={
        'dense-quadratic':18,'sparse-structured':18,'positive-dimensional':18},
        moduli={2,32003,2147483647})
    require(meta['requested_scheduling']=={'A':'degree','B':None}and
            meta['requested_binary_pivots']=={'A':'true','B':None}and
            meta['requested_dense_pivots']=={'A':'false','B':None}and
            meta['requested_delayed_reduction']=={'A':'true','B':None},
            'held-out algorithm policy differs')
    suite=cap.json('candidate/msolve/inputs/suite.json')
    require(suite['cases']==expected,'held-out selection differs from fixed corpus')
    for sample in meta['samples']:
        if sample['arm']=='A':
            output=cap.json('candidate/msolve/'+sample['case']+f"-b{sample['block']}-A.stdout")
            given=cap.json('candidate/msolve/inputs/'+sample['case']+'.json')
            require(all(output[k]==given[k]for k in ['p','variables','order']),
                    'held-out field/order/variable metadata differs')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path,required=True);parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--experiments',type=Path,required=True)
    parser.add_argument('--heldout',type=Path,required=True)
    parser.add_argument('--check',action='store_true');parser.add_argument('--current',action='store_true')
    args=parser.parse_args();production=Capsule(args.archive)
    text,manifest,checks,expected=render(production)
    del production
    gc.collect()
    from scripts.bench.groebner_sparse_experiments import experiments
    experimental=Capsule(args.experiments);observations=experiments(experimental)
    lines=['','| Private in-sample Eco-14 experiment | Candidate B/A | Process B/A | Pair ratios |',
           '|---|---:|---:|---|']
    for row in observations:
        lines.append(f"| {row['label']} | {row['candidate']:.4f} | {row['process']:.4f} | "+
                     ', '.join(f'{value:.4f}'for value in row['pairs'])+' |')
    lines+=['','These are seven distinct private executables and source snapshots, with 28 successful samples and 14 complete output/counter comparisons. The original four permission-denied launches are retained separately. The continuation, factor-only, bit-accumulator and constant-prime variants are unselected. The retry and upfront-selector experiments motivated the production change, but their source/executable identities differ from production. Ratios from different stages are not multiplied. All observations and rejected routes remain included.','',
        'The retry experiment’s discarded-work counter covers only its sparse retry. A separate production admission trace records 202062207 charged units discarded by the preceding packed attempts across 15 frames; the last of 16 packed refusals occurs before charged work. The upfront selector avoids those preceding attempts. The prototype counts do not substitute for current-production instrumentation.','',
        f'Experimental capsule `{args.experiments.name}` has SHA-256 `{experimental.sha256}`. Source blobs, all complete prototype outputs, input bindings, schedules, failed launches and admission accounting are independently replayed.','']
    text+='\n'.join(lines)
    del experimental
    gc.collect()
    from scripts.bench.groebner_parts import load_capsule
    held=load_capsule(args.heldout);result=comparator(held,manifest,expected)
    lines=['','| Held-out family | Hex/msolve process ratio |','|---|---:|']
    for family,value in result['per_family'].items():lines.append(f'| {family} | {value:.4f} |')
    lines+=['',f"The complete held-out sweep contains all 27 fixed inputs in three families across all three fields. All 108 processes succeeded, all 54 complete bases agree and there were no timeouts or missing observations. The equal-family process ratio is {result['family_balanced_geomean']:.4f}× Hex/msolve; the implementation remains slower overall on this held-out suite. Peak RSS is {result['peak_rss_kib']['A']}/{result['peak_rss_kib']['B']} KiB for Hex/msolve. These measurements do not establish a language/runtime limit.",'',
        'The comparator is msolve commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, built with Clang 23.1.3, `-O3 -march=native`, full reduced output (`-g 2`), linear algebra mode 2 and one thread. Both arms use the same GNU time wrapper and adjacent AB/BA scheduling on one automatically leased CPU. Ratios include process startup, parsing and complete output; checking lies outside candidate timing. Field/order/output contracts, comparator engine hashes and recorded compile commands are retained.','',
        f'Held-out archive stream SHA-256 is `{held.sha256}`. '+
        (f'Parts index `{args.heldout.name}` has SHA-256 `{held.index_sha256}`. 'if hasattr(held,'index_sha256')else f'Archive file: `{args.heldout.name}`. ')+
        'All complete bases, source/executable/compiler bindings, fixed inputs, samples, memory observations and family ratios are replayed independently. Full primary balanced acceptance and parallel comparisons remain outstanding.','']
    text+='\n'.join(lines)
    if args.current:
        from scripts.bench.groebner_measure import FAMILY
        from scripts.bench.groebner_checks import CHECKS,source_identity
        from scripts.bench.sweep_freshness import index_listing
        source_identity()
        require(index_listing(FAMILY)==manifest['source_manifest'],'current runtime differs')
        require(index_listing(CHECKS)==checks,'current verification sources differ')
    if args.check:require(args.report.read_text()==text,'report differs from evidence')
    else:args.report.write_text(text)
    print('PASS sparse F2 source/verification/output evidence replay')

if __name__=='__main__':main()
