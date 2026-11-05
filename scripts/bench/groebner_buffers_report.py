#!/usr/bin/env python3
"""Replay exact sparse-buffer executables, functional checks and matched samples."""
from __future__ import annotations
import argparse
import gc
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_sparse_report import verification,fixed_inputs,systems,comparator,mean
from scripts.bench.groebner_trie_report import source,require

CHECKPOINT='c08492f62a6f06728106980b7cafc88acc93466acd33192b21beb925674dcc14'


def digest(data):return hashlib.sha256(data).hexdigest()



def execution(cap,candidate):
    measured=source(cap,'measured')
    require(candidate['compilers']==measured['compilers'] and
            candidate['native_options']==measured['native_options'] and
            candidate['compiler_inputs']==measured['compiler_inputs'],
            'measured compiler configuration differs')
    for name in ['compute','compute-reference','bench']:
        require(candidate['binary_sha256'][name]==measured['binary_sha256'][name],
                'measured executable identity differs')
    def listing(manifest):
        return {line.split('\t',1)[1]:line.split(' ',2)[1]
                for line in manifest['source_manifest'].splitlines()}
    a=listing(candidate);b=listing(measured)
    changed={path for path in a.keys()|b.keys()if a.get(path)!=b.get(path)}
    allowed='bench/HexGroebner/Bench/SparseBinary.lean'
    require(changed <= {allowed,'lakefile.lean'}, 'runtime source changes exceed the execution bridge')
    if 'lakefile.lean' in changed:
        require((b['lakefile.lean'],a['lakefile.lean'])==
                ('f5d84133663d5296b92cbc611e0c1602c613e607',
                 '1fbef2521c139867cced94d2492ee8a911c5f13e'),
                'unrecognized upstream Lake registration change')
    if allowed in changed:
        current=cap.text('candidate/root-sources/'+allowed).splitlines()
        old=cap.text('measured/root-sources/'+allowed).splitlines()
        require(len(current)==len(old) and all(x==y or
                (x.lstrip().startswith('--') and y.lstrip().startswith('--'))
                for x,y in zip(current,old)), 'executable source changed in comment bridge')
    return measured


def functional(cap,candidate):
    prior=source(cap,'prior')
    bridge=cap.json('functional/sparse-buffer-final-executable-bridge.json')
    require(bridge['prior_manifest_sha256']==digest(cap.read('prior/manifest.json')) and
            bridge['final_manifest_sha256']==digest(cap.read('candidate/manifest.json')),
            'executable identity manifests differ')
    for name in ['compute','compute-reference']:
        require(candidate['binary_sha256'][name]==prior['binary_sha256'][name]==
                bridge['binary_sha256'][name],'functional executable differs')
    status=cap.json('functional/eco14/status.json')
    require(status['exit_code']==0 and status['sources_unchanged'] and
            status['source_bindings']==status['source_bindings_after'] and
            status['complete_basis_equal'] and status['all_statistics_equal'],
            'functional comparison failed')
    for path,value in status['source_bindings'].items():
        if path.endswith('/binaries/compute'):
            require(value==candidate['binary_sha256']['compute'],'functional binary differs')
        elif path.endswith('/manifest.json'):
            require(value==digest(cap.read('prior/manifest.json')),'functional manifest differs')
        elif '/root-sources/' in path:
            require(value==digest(cap.read('prior/root-sources/'+path.split('/root-sources/',1)[1])),
                    'functional source differs')
        else:
            require(value==digest(cap.read('functional/validate-sparse-index-frozen.py')),
                    'functional collector differs')
    actual=cap.read('functional/eco14/run.stdout');expected=cap.read('functional/expected.stdout')
    require(digest(actual)==status['actual_stdout_sha256'] and
            digest(expected)==status['expected_stdout_sha256'],'functional output digest differs')
    a=json.loads(actual);b=json.loads(expected);given=cap.json('functional/eco14/input.json')
    require(a['kind']=='unchecked_candidate' and all(a[k]==given[k]for k in
            ['p','variables','order']),'functional metadata differs')
    # The retained F2 reference predates the odd-prime delayed-reduction flag.
    # That flag is inactive in characteristic two; every other field must agree.
    require(given['p']==2 and a.get('delayedReduction') is True and
            b.get('delayedReduction') in [None,True], 'legacy F2 policy differs')
    a.pop('delayedReduction');b.pop('delayedReduction',None)
    a.pop('candidateNanos');b.pop('candidateNanos')
    require(a==b,'complete functional outputs differ')
    log=cap.text('functional/sparse-index-frozen-driver.log')
    require(log.count('candidate driver: 1134 complete corpus outputs/counters and input/resource boundaries passed')==2,
            'both frozen driver checks missing')
    require('all 85 benchmark(s) passed' in
            cap.text('functional/sparse-buffer-final-frozen-bench-verify-verb.log'),
            'frozen benchmark verification missing')
    endian=cap.json('functional/sparse-index-endian-clean-status.json')
    test=cap.read('functional/sparse-index-endian-selftest.c')
    require(len(endian)==4 and {row['mode']for row in endian}=={'native','portable'} and
            len({row['compiler']for row in endian})==2,'index representation profiles missing')
    for row in endian:
        require(row['build_exit']==row['exit_code']==0 and
                row['selftest_sha256']==digest(test) and
                '327680 aligned/unaligned little-endian index boundaries' in row['stdout'],
                'index representation check failed')
    wrapper=cap.read('functional/lean-cc-wrapper')
    require(digest(wrapper)==candidate['compilers']['lean']['sha256'],'compiler wrapper differs')


def kernels(cap,measured):
    lines=['', '| Kernel campaign | Function | Verdict | Flagged samples |',
           '|---|---|---|---:|']
    hashes={}
    for campaign in ['first','longer']:
        prefix='measurements/kernels/'+campaign
        meta=cap.json(prefix+'/metadata.json')
        require(meta['manifest']==measured and meta['exit_code']==0 and
                meta['threads']==1 and meta['sources_unchanged'] and
                meta['source_bindings']==meta['source_bindings_after'] and
                meta['source_bindings'][meta['command'][0]]==measured['binary_sha256']['bench'],
                'kernel executable/source identity differs')
        results=cap.json(prefix+'/results.json')['results']
        require([r['function']for r in results]==['Hex.Groebner.Bench.sparseBinary',
                'Hex.Groebner.Bench.sparseBinaryReference'],'kernel selection differs')
        for row in results:
            params=[64,128,256,512,1024,2048]if row['function'].endswith('.sparseBinary')else[64,128,256]
            require(row['complexity_formula']=='131073+n*n' and
                    row['config']['outer_trials']==3 and row['config']['signal_floor_multiplier']==10 and
                    [(v['trial_index'],v['param'])for v in row['points']]==
                    [(trial,n)for trial in range(3)for n in params], 'kernel schedule differs')
            for point in row['points']:
                require(point['status']=='ok','kernel process failed')
                n=point['param'];value=point['result_hash']
                require(hashes.setdefault(n,value)==value,'kernel output hash differs')
            flags=sum(v['below_signal_floor']for v in row['points'])
            lines.append(f"| {campaign} | {row['function'].rsplit('.',1)[1]} | {row['verdict']} | {flags}/{len(row['points'])} |")
    return lines+['', 'Both ordinary complexity campaigns are retained, including the sole longer-batch repeat and all signal-floor flags. Their verdicts are inconclusive; no empirical complexity acceptance or matched implementation speed ratio is inferred.', '']


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--heldout',type=Path)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--check',action='store_true')
    current=parser.add_mutually_exclusive_group()
    current.add_argument('--current',action='store_true')
    current.add_argument('--current-runtime',action='store_true')
    args=parser.parse_args();cap=Capsule(args.archive)
    candidate=source(cap,'candidate');baseline=source(cap,'baseline')
    measured=execution(cap,candidate)
    functional(cap,candidate);checks=None
    if cap.sha256==CHECKPOINT:
        require(cap.json('scope.json')['kind']=='functional-checkpoint','checkpoint scope differs')
        text='\n'.join(['# Sparse matrix buffers: functional checkpoint','',
            f"Current runtime source `{candidate['source_fingerprint']}` reproduces all three executables from measured source `{measured['source_fingerprint']}` byte for byte. Their source differences are a checked benchmark cost-model comment and the exact pinned upstream Lake registrations for unrelated HexRCF targets. The computation and full-initialization drivers also match the preceding independently checked snapshot; the benchmark executable includes the new sparse kernels.",'',
            'Both exact driver executables passed all 1,134 corpus and resource/input-boundary cases. The complete Eco-14 basis, metadata and all logical counters agree with the retained reference output. All 85 frozen benchmark verifications pass. Four Clang/GCC ASan/UBSan index-load checks each cover 327,680 aligned/unaligned boundary cases, including the bytewise fallback.','',
            'This capsule records functional evidence only. It contains no comparative timing or final 36-configuration/nine-gate receipt claim. Candidate production remains separate from certificate generation, independent certification and kernel checking. The fastest-open-source milestone and remaining issue #10987 obligations are not established.','',
            f'Capsule SHA-256: `{cap.sha256}`. Source blobs, compiler and executable identities, complete outputs and functional records are replayed independently. Only this exact capsule is accepted as a functional checkpoint.',''])
    else:
        require(cap.json('scope.json')['kind']=='performance','performance scope missing')
        checks=verification(cap,candidate);fixed=fixed_inputs(cap)
        ratios,samples=systems(cap,measured,baseline,fixed)
        lines=['# Sparse matrix buffers: measured snapshot','',
            f"Measured runtime `{measured['source_fingerprint']}` is compared directly with `{baseline['source_fingerprint']}`. Current source `{candidate['source_fingerprint']}` reproduces the computation, full-initialization and benchmark executables byte for byte; source differences are a checked cost-model comment and exact pinned upstream Lake registrations for unrelated HexRCF targets. The native F₂ scan resolves its stable private buffers once, and loads packed UInt32 indices with unaligned-safe native loads only on known little-endian hosts. Other hosts retain bytewise decoding. Mathematical results, row order, labels, budgets and all eight logical counters are preserved.",'',
            'All 128 processes and 64 adjacent AB/BA pairs have identical complete outputs and counters. The fixed sweep covers the first size of ten primary families over F₂, F₃₂₀₀₃ and F₂₁₄₇₄₈₃₆₄₇, plus Eco-14/Eco-15 over F₂. Runs use one leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled.','',
            '| Field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |',
            '|---|---:|---:|---:|---:|']
        for p in [2,32003,2147483647]:
            selected=[r for r in ratios if r['p']==p and r['case']not in ['eco14-2','eco15-2']]
            require(len(selected)==20,'field coverage differs')
            values=[r['candidate_ratio']for r in selected]
            rss={arm:max(row['peak_rss_kib']for row in samples if row['p']==p and
                     row['arm']==arm and row['case']not in ['eco14-2','eco15-2'])for arm in ['A','B']}
            lines.append(f"| {p} | {mean(values):.4f} | {mean([r['process_ratio']for r in selected]):.4f} | {min(values):.4f}–{max(values):.4f} | {rss['A']}/{rss['B']} |")
        lines+=['','| F₂ case | Candidate B/A | Pair ratios |','|---|---:|---|']
        for name in ['eco14-2','eco15-2']:
            values=[r['candidate_ratio']for r in ratios if r['case']==name]
            require(len(values)==2,'targeted coverage differs')
            lines.append(f"| {name} | {mean(values):.4f} | "+', '.join(f'{v:.4f}'for v in values)+' |')
        lines+=['','These are descriptive point estimates. Every completed observation, outlier and failure is retained; ratios from preliminary optimization stages are not multiplied. Host activity is recorded on the shared AMD EPYC 9455. Production native code uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3. Both builds disable the opt-in AVX-512 route; existing exact AVX2 dispatch remains available. Limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with explicit fixed-corpus parent allowances. The measurements do not establish default-budget admission or complete balanced/parallel acceptance.','',
            'All nine project gates and 36 strict Clang/GCC ASan/UBSan configurations are source-bound, including regular, forced-sparse and packed-only profiles. Compiler families, actual Lake compiler/flag declarations, generated driver templates, source manifests and all complete functional outputs are replayed. Native and portable wide-sparse kernels are registered with lean-bench using the O(C+n²) operation model, C=131073, eight targets and complete output/counter consumption. All 85 frozen benchmark verifications pass.','',
            f'Production capsule SHA-256: `{cap.sha256}`. Candidate production, certificate generation, independent native certification and kernel checking remain separate costs. Ordinary F₂ polynomial exponents retain their usual meaning; x and x² are distinct.','']
        lines+=kernels(cap,measured)
        text='\n'.join(lines)
        del cap;gc.collect()
        require(args.heldout is not None,'held-out evidence missing')
        from scripts.bench.groebner_parts import load_capsule
        held=load_capsule(args.heldout)
        result=comparator(held,measured,[c for c in fixed if c['split']=='heldout'])
        lines=['','| Held-out family | Hex/msolve process ratio |','|---|---:|']
        for family,value in result['per_family'].items():lines.append(f'| {family} | {value:.4f} |')
        lines+=['',f"All 27 fixed held-out inputs have 108 successful processes, 54 equal complete bases and no missing/failed observations. The family-balanced process ratio is {result['family_balanced_geomean']:.4f}× Hex/msolve. Peak RSS is {result['peak_rss_kib']['A']}/{result['peak_rss_kib']['B']} KiB. These observations do not establish a language/runtime limitation.",'',
            'The comparator is msolve commit 3672113ee2c696a2ac9c637636e0f7214f500ba1, Clang 23.1.3, -O3 -march=native, full reduced output, linear algebra mode 2 and one thread. Full primary solved coverage, equal-thread parallel comparisons, finite-extension coverage, deterministic producer correctness/termination and the fastest-open-source milestone remain required by issue #10987.','',
            f'Held-out stream SHA-256: `{held.sha256}`. All full bases, fixed inputs, failures, source/executable/compiler identities, raw samples, memory and family ratios are retained and independently replayed. Scientific performance claims never depend on CI timings.','']
        text+='\n'.join(lines)
    if args.current or args.current_runtime:
        from scripts.bench.groebner_checks import CHECKS,source_identity
        from scripts.bench.groebner_measure import FAMILY
        from scripts.bench.sweep_freshness import index_listing
        source_identity()
        require(index_listing(FAMILY)==candidate['source_manifest'],'current runtime differs')
        if args.current:
            require(checks is not None and index_listing(CHECKS)==checks,'current verification sources differ')
    if args.check:require(args.report.read_text()==text,'report differs from evidence')
    else:args.report.write_text(text)
    print('PASS sparse buffer source/functional/measurement evidence replay')

if __name__=='__main__':main()
