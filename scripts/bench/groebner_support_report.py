#!/usr/bin/env python3
"""Validate symbolic support experiments and reproduce their retained report."""
import argparse
import hashlib
import math
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_checks import source_identity
from scripts.bench.groebner_binary_guards import blobs
from scripts.bench.groebner_trie_report import source, require, mean


def close(a,b,message):
    require(math.isclose(a,b,rel_tol=1e-12),message)


def campaign(cap, label, before, after, count=10, expected_binary=None):
    meta, recorded = cap.json(label + "/metadata.json"), cap.json(label + "/analysis.json")
    require(meta["source_unchanged"] and meta["threads"] == 1 and
            meta["source_manifest"] == after["source_manifest"] and meta["baseline_manifest"] == before and
            meta["binary_sha256"] == meta["binary_sha256_after"] ==
            {"A": before["binary_sha256"]["compute"], "B": after["binary_sha256"]["compute"]},
            "sweep source/executable binding differs")
    require(meta["requested_scheduling"] == {"A": "degree", "B": "degree"}, "scheduling differs")
    for name, digest in meta["input_sha256"].items():
        require(hashlib.sha256(cap.read(label + "/inputs/" + name)).hexdigest() == digest, "input differs")
    require(meta["requested_binary_pivots"] == expected_binary, "binary policy controls differ")
    samples = meta["samples"]
    order = [r["case"] for r in samples if r["block"] == 0 and r["arm"] == "A"]
    require(len(order) == len(set(order)) == count and len(samples) == count * 4 and
            [(r["case"], r["block"], r["arm"]) for r in samples] ==
            [(case, block, arm) for block in [0, 1] for case in order
             for arm in (["A", "B"] if block == 0 else ["B", "A"])], "AB/BA schedule differs")
    index = {(r["case"], r["block"], r["arm"]): r for r in samples}
    ratios, candidates, families = [], [], {}
    for case in order:
        inp = cap.json(label + "/inputs/" + case + ".json")
        for block in [0, 1]:
            outputs, pair = [], [index[case, block, a] for a in ["A", "B"]]
            for row in pair:
                arm = row["arm"]
                value = cap.json(f"{label}/{case}-b{block}-{arm}.stdout")
                require(row["status"] == "ok" and row["returncode"] == 0 and row["complete_basis_equal"],
                        "failed sample")
                require(value["kind"] == "unchecked_candidate" and value["p"] == inp["p"] and
                        value["variables"] == inp["variables"] and value["order"] == inp["order"] == "grevlex" and
                        value["scheduling"] == "degree", "candidate contract differs")
                flag = meta["requested_binary_pivots"][arm]
                require(value.get("binaryPivots", False) == (flag == "true"), "binary policy differs")
                if flag is not None:
                    require(row["command"][row["command"].index("--binary-pivots") + 1] == flag,
                            "binary command differs")
                counters = dict(row["statistics"])
                require(counters.pop("candidate_nanos") == value["candidateNanos"] and
                        counters == value["statistics"] and
                        int(cap.text(f"{label}/{case}-b{block}-{arm}.rss")) == row["peak_rss_kib"],
                        "counters/RSS differ")
                outputs.append(value)
            a_stats,b_stats = [dict(v["statistics"]) for v in outputs]
            extra_work = b_stats.pop("work")-a_stats.pop("work")
            extra_bytes = b_stats.pop("allocatedBytes")-a_stats.pop("allocatedBytes")
            require(extra_work == extra_bytes and extra_bytes >= 0,
                    "bitmap work/allocation charges differ")
            require(outputs[0]["basis"] == outputs[1]["basis"] and a_stats == b_stats and
                    outputs[0]["batchSize"] == outputs[1]["batchSize"] and
                    outputs[0]["randomState"] == outputs[1]["randomState"] == 0,
                    "complete bases or logical statistics differ")
            ratios.append(pair[1]["wall_nanos"] / pair[0]["wall_nanos"])
            candidates.append(outputs[1]["candidateNanos"] / outputs[0]["candidateNanos"])
            families.setdefault(pair[0]["family"], []).append(ratios[-1])
    values = dict(geomean=mean(ratios), family_balanced_geomean=mean([mean(v) for v in families.values()]),
                  minimum=min(ratios), maximum=max(ratios), median=statistics.median(ratios))
    for key, value in values.items():
        close(recorded[key], value, "recorded " + key + " differs")
    require(recorded["samples"] == count * 4 and recorded["complete_bases_equal"] == count * 2 and
            recorded["failed_processes"] == recorded["timeouts"] == 0, "sweep coverage differs")
    for family, values in families.items():
        close(recorded["per_family"][family], mean(values), "family ratio differs")
    require(recorded['cpu']==meta['cpu'] and recorded['successful_processes']=={'A':count*2,'B':count*2} and
            recorded['peak_rss_kib']=={arm:max(r['peak_rss_kib']for r in samples if r['arm']==arm)for arm in ['A','B']},
            'sweep CPU/coverage/peak RSS differs')
    return dict(recorded=recorded, meta=meta, candidate=mean(candidates))


def native_checks(cap, manifest, full=False, support=True):
    identity=cap.json('identity.json')
    require(identity['source_fingerprint']==manifest['source_fingerprint'] and
            identity['source_manifest_sha256']==hashlib.sha256(manifest['source_manifest'].encode()).hexdigest(),
            'check/runtime binding differs')
    checks=cap.text('checks.manifest')
    require(identity['checks_manifest_sha256']==hashlib.sha256(checks.encode()).hexdigest(),
            'check manifest differs')
    blobs(cap,checks,'checks-sources/')
    rows=cap.json('native-status.json')
    require([r['name']for r in rows]==['clang','gcc'] and all(r['exit_code']==0 and
            r['variants']==['Native','AVX2','AVX2Remainder','Scalar','Remainder','ScalarRemainder'] and
            r['sanitize']==['address','undefined'] and
            all(r[k]==v for k,v in identity.items())for r in rows),'native checks differ')
    for compiler,version in [('clang','clang version 23.1.3'),('gcc','16.2.0')]:
        log=cap.text('native-'+compiler+'.log')
        require(version in log,'sanitizer compiler differs')
        if support:
            require(log.count('native support queue calls:')==6,'native support coverage differs')
    if full:
        rows=cap.json('full-status.json')
        require([r['name']for r in rows]==['build','oracles','driver','bench','dag','phase4','manifest','headers','lines'] and
                all(r['exit_code']==0 and all(r[k]==v for k,v in identity.items())for r in rows),
                'full checks differ')
        log=cap.text('full/oracles.log')
        require('567 unique reduced bases match SymPy' in log and '567 reduced bases match Singular' in log,
                'independent oracle coverage differs')
    return identity


def kernels(cap, manifest, suffix):
    status=cap.json('candidate/kernel'+('-long'if suffix else'')+'-status.json')
    require(status['identity']==cap.json('identity.json') and
            status['manifest']=={'A':manifest,'B':manifest} and status['threads']==1 and
            status['binary_sha256']==status['binary_sha256_after']==
            {a:manifest['binary_sha256']['bench']for a in ['A','B']},'kernel provenance differs')
    rows=[r for r in status['samples']if r['label'].startswith('matched/')]
    sizes=[256,1024,4096,16384,65536]
    require([r['label']for r in rows]==[f'matched/supportQueue/b{b}-{n}-{a}'for b in [0,1]
            for n in sizes for a in (['A','B']if b==0 else['B','A'])] and
            len({r['cpu']for r in rows})==1,'kernel schedule/lease differs')
    result=[]
    for n in sizes:
        points={}
        for b in [0,1]:
            for a in ['A','B']:
                label=f'matched/supportQueue/b{b}-{n}-{a}'
                row=next(r for r in rows if r['label']==label)
                require(row['exit_code']in [0,2],'kernel command failed')
                command=row['command'];function='supportPortable'if a=='A'else'supportNative'
                require('Hex.Groebner.Bench.'+function in command and
                        command[command.index('--target-inner-nanos')+1]==('8000000000'if suffix else'1000000000'),
                        'kernel controls differ')
                p=cap.json('candidate/kernels'+suffix+'/'+label+'/result.json')['results'][0]['points'][0]
                require(p['status']=='ok' and p['param']==n and p['result_hash']is not None,'kernel point failed')
                points[b,a]=p
        require(len({p['result_hash']for p in points.values()})==1,'complete kernel hashes differ')
        result.append((n,mean([points[b,'B']['per_call_nanos']/points[b,'A']['per_call_nanos']for b in [0,1]]),
                       sum(p['below_signal_floor']for p in points.values())))
    return result


def stage(cap, support, full=False):
    before,after=source(cap,'baseline'),source(cap,'candidate')
    require(before['compilers']==after['compilers'] and before['native_options']==after['native_options'],
            'matched compilers/options differ')
    identity=native_checks(cap,after,full,support)
    result={}
    for label,count in [('f2-false',10),('f2-false-repeat',10),('prime-control',14),('prime-control-repeat',14)]:
        binary={a:('true'if label.startswith('f2')else None)for a in ['A','B']}
        v=campaign(cap,'candidate/'+label,before,after,count,binary)
        dense={a:('false'if label.startswith('f2')else None)for a in ['A','B']}
        require(v['meta']['requested_dense_pivots']==dense,'dense policy differs')
        result[label]=v
    return before,after,identity,result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['bitmap','prototype','selected']:
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--current',action='store_true')
    args=parser.parse_args()
    caps={name:Capsule(getattr(args,name))for name in ['bitmap','prototype','selected']}
    stages={name:stage(cap,name!='bitmap',name=='selected')for name,cap in caps.items()}
    require({name:value[1]['source_fingerprint']for name,value in stages.items()}==
            {'bitmap':'1778a37c808c','prototype':'531625070811','selected':'f2430e4fd007'},
            'experimental cohorts differ')
    require(stages['bitmap'][0]==stages['prototype'][0], 'prototype baselines differ')
    selected=stages['selected']
    require(selected[0]['source_fingerprint']=='e5f7b7d0de7e','selected baseline differs')
    if args.current:
        current=source_identity()
        require(all(current[k]==selected[2][k]for k in ['source_fingerprint','source_manifest_sha256',
                'checks_fingerprint','checks_manifest_sha256']),'current implementation/checks differ')
    short=kernels(caps['prototype'],stages['prototype'][1],'')
    long=kernels(caps['prototype'],stages['prototype'][1],'-long')
    lines=['# Symbolic support queues','','Support batching preserves the first-occurrence queue order and the complete reduced basis. '
        'A dynamically growing arena bitmap replaces support hash lookup; a bounded native operation validates at most 4096 u32 IDs before updating the bitmap and pending queue. '
        'The portable definition has the same result, rejection and ownership contract. Bitmap initialization and growth add equal explicit work and packed-byte charges. '
        'The pending queue still uses Lean’s array of natural numbers; this change does not establish fully packed F4 scheduling storage.','',
        'These are shared-host development measurements, not a fastest-open-source milestone. Candidate production excludes certificate generation, independent final certification and kernel replay. '
        'The verification gates below check correctness separately. All completed samples, outliers, failures and measurement flags are retained.','',
        '## Full-system comparisons','',
        'One thread, one leased CPU per campaign, grevlex, degree scheduling, fixed resource caps, adjacent AB then BA. '
        'F₂ uses ordinary polynomial rings, including squares, with binary pivots explicitly enabled and dense pivots disabled in both arms. '
        'Odd-prime inputs use both archived drivers’ default disabled pivot policies. Every successful comparison matches the full reduced basis, all structural counters and all other output metadata. '
        'Only work and allocation differ, by the bitmap’s explicit payload growth.','',
        '| Implementation and campaign | Process B/A | Family-balanced B/A | Candidate B/A | CPU | Peak RSS A/B KiB |',
        '| --- | ---: | ---: | ---: | ---: | ---: |']
    for name,(_,_,_,runs)in stages.items():
        for label,v in runs.items():
            j=v['recorded'];rss=j['peak_rss_kib']
            lines.append(f"| {name}: {label} | {j['geomean']:.6f} | {j['family_balanced_geomean']:.6f} | {v['candidate']:.6f} | {j['cpu']} | {rss['A']}/{rss['B']} |")
    lines += ['', 'The selected F₂ family-balanced results do not establish an overall speedup. '
        'The selected odd-prime process observations are about 2–3% lower, with per-family variability and regressions retained below. '
        'These small development sweeps do not establish the SPEC’s solved-coverage, held-out or leadership requirements.']
    lines += ['', 'Each F₂ campaign contains 40 processes/20 comparisons across 8 families; each odd-prime campaign contains 56 processes/28 comparisons across 7 families. '
        'There are no failed processes, timeouts or basis mismatches in these campaigns. The bitmap-only and batched prototypes share an experimental packed-table baseline. '
        'The selected comparison uses the packed-pivot implementation from PR #11030 and excludes the experimental metadata, known-pivot projection and XOR tables. '
        'Prototype and selected ratios measure different complete implementations and must not be multiplied.','',
        '| Selected campaign/family | Initial process B/A | Repeat process B/A |', '| --- | ---: | ---: |']
    for field,label in [('F₂','f2-false'),('Odd prime','prime-control')]:
        a,b=[selected[3][label+suffix]['recorded']['per_family']for suffix in ['', '-repeat']]
        require(set(a)==set(b),'family coverage differs')
        for family in a:lines.append(f'| {field}: {family} | {a[family]:.6f} | {b[family]:.6f} |')
    lines += ['', '## Queue kernel','',
        'Same frozen prototype executable for both arms: portable versus native support queue, including bitmap initialization, slice validation, output validation and complete structural hashing. '
        'Input generation is excluded. Three interleaved occurrences of each ID exercise both insertion and repeated membership. The fixed cost model is linear. '
        'The initial matched run targets 1 second per point; the single longer repeat targets 8 seconds. Kernel ratios do not predict full-system speedups.','',
        '| Arena IDs | Initial native/portable | Initial flags | Longer native/portable | Longer flags |',
        '| ---: | ---: | ---: | ---: | ---: |']
    for a,b in zip(short,long):
        require(a[0]==b[0],'kernel sizes differ')
        lines.append(f'| {a[0]} | {a[1]:.6f} | {a[2]} | {b[1]:.6f} | {b[2]} |')
    environment=caps['prototype'].json('candidate/kernels/matched/supportQueue/b0-256-B/result.json')['results'][0]['env']
    require(environment['hostname']=='chungus2' and environment['cpu_model']=='AMD EPYC 9455 48-Core Processor' and
            environment['lean_version']=='4.35.0-rc3','host/toolchain differs')
    lines += ['', 'The shared filesystem filled during the longer run after seven completed arms. Those samples remain unchanged; only unfinished arms resumed, using the original leased CPU. '
        'The same event interrupted a prototype usage check, an integration build and a frozen checkout. Original failure logs are retained. '
        'Fresh recovered verification runs and the recovered frozen carrier supply the successful checks; no completed timing sample was discarded or repeated.','',
        '## Verification and provenance','',
        'Measurements use the shared host `chungus2`, an AMD EPYC 9455 48-Core Processor, with Lean 4.35.0-rc3. '
        'The queue operation itself uses scalar exact byte/word operations; matrix SIMD dispatch options and full compiler manifests are retained in every capsule.','',
        'Each stage has twelve passing ASan/UBSan variants: Clang 23.1.3 and GCC 16.2.0, automatic/AVX2/scalar paths with wide-product and remainder implementations. '
        'The native batch stages assert actual instrumented calls and check malformed slices, duplicate IDs, byte boundaries, shared and exclusive ownership, borrowed aliases and marked-linear buffers. '
        'The selected stage also passes the library/theory build, independent SymPy and Singular oracles (567 bases each), driver checks, benchmark verification, DAG, phase, release-manifest, copyright and line-count gates. '
        'Kernel replay and axiom audits remain separate from native verification.','']
    for name,cap in caps.items():
        _,manifest,identity,_=stages[name]
        native=manifest['compilers']['native']['version'].splitlines()[0]
        lean=manifest['compilers']['lean']['version'].splitlines()[0]
        lines.append(f"- {name}: runtime `{manifest['source_fingerprint']}`, checks `{identity['checks_fingerprint']}`; native compiler {native}; generated Lean C compiler {lean}.")
        lines.append(f"  Capsule [{cap.path.name}](raw/{cap.path.name}), SHA-256 `{cap.sha256}`.")
    lines += ['', 'Regenerate and validate every source blob, check snapshot, output, counter, input hash, compiler manifest, timing ratio and kernel hash:', '',
        '`python3 scripts/bench/groebner_support_report.py '+ ' '.join('--'+name+' '+str(getattr(args,name))for name in caps)+
        ' --output '+str(args.output)+' --check --current`','']
    text='\n'.join(lines)
    if args.check:
        require(args.output.read_text()==text,'committed report differs')
    else:
        args.output.write_text(text)
    print('Symbolic support report and retained evidence verified')


if __name__=='__main__':
    main()
