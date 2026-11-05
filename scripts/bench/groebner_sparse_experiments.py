#!/usr/bin/env python3
"""Check all retained sparse-F2 prototypes, including rejected routes and launch failures."""
import argparse
import hashlib
import math
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_trie_report import require,source


def experiments(cap):
    baselines={source(cap,label)['source_fingerprint']for label in ['baseline-c4','baseline-c935']}
    labels=['continuation','continuation-factor','wide-sparse','bit-accumulator',
            'retry','selector','constant-prime']
    require(cap.json('scope.json')['experiments']==labels,'experiment coverage differs')
    results=[]
    for label in labels:
        manifest=cap.json(label+'/manifest.json')
        require(manifest['base_runtime_manifest']['source_fingerprint']in baselines,
                'prototype runtime source differs')
        hashes=manifest['experimental_source_sha256']
        for name,digest in hashes.items():
            require(hashlib.sha256(cap.read(label+'/sources/'+name)).hexdigest()==digest,
                    'prototype source differs')
        prefix=label+'/measurements';meta=cap.json(prefix+'/metadata.json')
        require(meta['manifest']==manifest and meta['threads']==1 and meta['sources_unchanged']and
                meta['source_bindings']==meta['source_bindings_after'],'prototype identity changed')
        samples=meta['samples'];require(len(samples)==4,'incomplete private comparison')
        require([(r['block'],r['arm'])for r in samples]==[(0,'A'),(0,'B'),(1,'B'),(1,'A')],
                'private AB/BA schedule differs')
        pairs=[];process=[]
        for block in [0,1]:
            outputs=[];rows=[]
            for arm in ['A','B']:
                row=next(r for r in samples if r['block']==block and r['arm']==arm);rows.append(row)
                require(row['status']=='ok'and row['returncode']==0 and
                        row['complete_output_and_counters_equal'],'private process failed')
                require(meta['source_bindings'][row['command'][0]]==manifest['binary_sha256']['compute'],
                        'private executable differs')
                payload=cap.read(prefix+'/'+row['case']+'.input.json')
                require(hashlib.sha256(payload).hexdigest()==row['input_sha256'],'private input differs')
                value=cap.json(prefix+'/'+row['case']+f'-b{block}-{arm}.stdout')
                require(value['kind']=='unchecked_candidate'and value['p']==2 and
                        value['candidateNanos']==row['candidate_nanos'],'private candidate differs')
                require(value['variables']==cap.json(prefix+'/'+row['case']+'.input.json')['variables'],
                        'private variable count differs')
                outputs.append({k:v for k,v in value.items()if k!='candidateNanos'})
            require(outputs[0]==outputs[1],'private complete output/counters differ')
            pairs.append(rows[1]['candidate_nanos']/rows[0]['candidate_nanos'])
            process.append(rows[1]['wall_nanos']/rows[0]['wall_nanos'])
        results.append(dict(label=label,candidate=math.sqrt(math.prod(pairs)),
                            process=math.sqrt(math.prod(process)),pairs=pairs))
    failed=cap.json('failed-launches/metadata.json')['samples']
    require(len(failed)==4 and all(r['status']=='failed'and r['returncode']!=0 for r in failed),
            'original launch-failure coverage differs')
    admission=cap.json('admission/parsed-admission.json')
    rows=admission['frames']
    require(len(rows)==45 and sum(r['work']for r in rows if r['outcome']=='declined')==202062207,
            'packed discarded-work accounting differs')
    return results


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--archive',type=Path,required=True)
    args=p.parse_args();results=experiments(Capsule(args.archive))
    for row in results:print(row)
    print('PASS 28 successful private samples,14 complete pairs and4 retained launch failures')

if __name__=='__main__':main()
