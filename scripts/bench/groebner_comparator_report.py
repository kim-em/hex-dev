"""Verify matched full-basis msolve observations retained in F4 capsules."""
import hashlib
import math
from scripts.bench.groebner_trie_report import source,require,mean
from scripts.oracle.groebner_singular import polynomial,canonical


def msolve(capsule,source_label="native-compiler23"):
    label=source_label+'/msolve';meta=capsule.json(label+'/metadata.json');recorded=capsule.json(label+'/analysis.json')
    manifest=source(capsule,source_label)
    require(meta['source_fingerprint']==manifest['source_fingerprint'] and
            meta['source_manifest']==manifest['source_manifest'] and meta['source_unchanged'],'msolve source differs')
    require(meta['binary_sha256']['A']==manifest['binary_sha256']['compute'] and
            meta['binary_sha256']['B']==meta['msolve_cli_sha256'],'comparator executable binding differs')
    require(meta['msolve_build']['commit']==meta['msolve_commit'] and
            meta['msolve_build']['tracked_status']=='','comparator source state differs')
    commands=meta['msolve_build']['engine_recorded_compile_commands']
    require(commands is not None and '23.1.3' in commands and
            '-march=native' in commands.split() and '-O3' in commands.split(),'comparator compiler/tuning record differs')
    require(meta['threads']==1 and meta['msolve_mode']==2 and meta['msolve_commit']=='3672113ee2c696a2ac9c637636e0f7214f500ba1','comparator configuration differs')
    require(meta['binary_sha256']==meta['binary_sha256_after'] and
            meta['msolve_engine_sha256']==meta['msolve_engine_sha256_after'] and meta['msolve_build']==meta['msolve_build_after'],'comparator build changed')
    for name,digest in meta['input_sha256'].items():
        require(hashlib.sha256(capsule.read(label+'/inputs/'+name)).hexdigest()==digest,'comparator input differs')
    samples=meta['samples'];index={(s['case'],s['block'],s['arm']):s for s in samples}
    order=[s['case']for s in samples if s['block']==0 and s['arm']=='A']
    require(len(index)==len(samples)==56 and len(set(order))==14,'comparator coverage differs')
    require([(s['case'],s['block'],s['arm'])for s in samples]==[(case,block,arm)for block in [0,1]for case in order for arm in (['A','B']if block==0 else ['B','A'])],'comparator adjacency differs')
    families={}
    for case in order:
        input_data=capsule.json(label+'/inputs/'+case+'.json')
        for block in [0,1]:
            a,b=[index[case,block,arm]for arm in ['A','B']]
            require(all(s['status']=='ok'and s['returncode']==0 and s['complete_basis_equal']for s in [a,b]),'comparator failed')
            command=b['command']
            require(all(command[command.index(flag)+1]==value for flag,value in [('-g','2'),('-t','1'),('-l','2')]),'msolve command differs')
            text=''.join(line for line in capsule.text(f'{label}/{case}-b{block}-B.basis').splitlines()if not line.startswith('#')).strip()
            require(text.startswith('[')and text.endswith(']:'),'invalid msolve output')
            body=text[1:-2].strip();basis=sorted(polynomial(p,input_data['variables'],input_data['p'])for p in body.split(','))if body else []
            output=capsule.json(f'{label}/{case}-b{block}-A.stdout')
            require(output['kind']=='unchecked_candidate'and canonical(output['basis'])==basis,'complete comparator bases differ')
            families.setdefault(a['family'],[]).append(a['wall_nanos']/b['wall_nanos'])
    ratio=mean([mean(v)for v in families.values()])
    require(len(families)==7 and all(len(v)==4 for v in families.values())and
            recorded['ratio_direction']=='Hex/msolve process'and math.isclose(ratio,recorded['family_balanced_geomean'],rel_tol=1e-12),'comparator ratio differs')
    return recorded,meta

