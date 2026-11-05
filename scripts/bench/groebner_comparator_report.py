"""Verify matched full-basis msolve observations retained in F4 capsules."""
import hashlib
import math
import statistics
from scripts.bench.groebner_trie_report import source,require,mean
from scripts.oracle.groebner_singular import polynomial,canonical


def msolve(capsule,source_label,*,expected_families=None,moduli=None,candidate_key="compute",basis_check=None):
    if expected_families is not None:
        require(all(isinstance(n,int)and n>0 for n in expected_families.values())and
                sum(expected_families.values())%2==0,'invalid expected family counts')
    case_count=sum(expected_families.values())//2 if expected_families is not None else 14
    label=source_label+'/msolve';meta=capsule.json(label+'/metadata.json');recorded=capsule.json(label+'/analysis.json')
    manifest=source(capsule,source_label)
    require(meta['source_fingerprint']==manifest['source_fingerprint'] and
            meta['source_manifest']==manifest['source_manifest'] and meta['source_unchanged'],'msolve source differs')
    require(meta['binary_sha256']['A']==manifest['binary_sha256'][candidate_key] and
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
    require(len(index)==len(samples)==4*case_count and len(set(order))==case_count,'comparator coverage differs')
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
            output=capsule.json(f'{label}/{case}-b{block}-A.stdout')
            require(output['kind']=='unchecked_candidate','comparator candidate kind differs')
            if basis_check is None:
                body=text[1:-2].strip()
                basis=sorted(polynomial(p,input_data['variables'],input_data['p'])for p in body.split(','))if body else []
                require(canonical(output['basis'])==basis,'complete comparator bases differ')
            else:
                require(basis_check(output['basis'],text,input_data['variables'],input_data['p']),
                        'complete comparator bases differ')
            families.setdefault(a['family'],[]).append(a['wall_nanos']/b['wall_nanos'])
    ratio=mean([mean(v)for v in families.values()])
    coverage=(len(families)==7 and all(len(v)==4 for v in families.values()))if expected_families is None else (
        {family:len(values)for family,values in families.items()}==expected_families)
    require(moduli is None or {s['p']for s in samples}==set(moduli),'comparator moduli differ')
    require(coverage and recorded['samples']==4*case_count and recorded['complete_bases_equal']==2*case_count and
            recorded['failed_processes']==recorded['timeouts']==0 and
            recorded['ratio_direction']=='Hex/msolve process'and math.isclose(ratio,recorded['family_balanced_geomean'],rel_tol=1e-12),'comparator ratio differs')
    ratios=[r for values in families.values()for r in values]
    for key,value in [('geomean',mean(ratios)),('minimum',min(ratios)),('maximum',max(ratios)),('median',statistics.median(ratios))]:
        require(math.isclose(recorded[key],value,rel_tol=1e-12),'recorded comparator '+key+' differs')
    require(set(recorded['per_family'])==set(families) and
            all(math.isclose(recorded['per_family'][family],mean(values),rel_tol=1e-12)for family,values in families.items()),'recorded comparator family ratio differs')
    return recorded,meta

