"""Dependency-free integrity and paired-schedule checks for operand work."""
import hashlib
import json
from pathlib import Path
from scripts.bench.sign_det_trace_archive import check_retained

ROOT = Path(__file__).resolve().parents[2]/'reports/data/sign-det-operand-work'


def validate(root=ROOT):
    root=Path(root)
    manifest=json.loads((root/'manifest.json').read_text())
    for name,digest in manifest['files'].items():
        path=root/name
        if Path(name).is_absolute() or '..' in Path(name).parts:
            raise ValueError('invalid archive path')
        if hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('archive hash mismatch: '+name)
    for arm in ('A','B'):
        check_retained(root/arm/'observations.jsonl')
    paired=root/'paired'
    samples=[json.loads(s) for s in (paired/'samples.jsonl').read_text().splitlines()]
    expected=[(t,c,pos,a) for t in range(6) for c in ('depthOne','depthTwo')
              for pos,a in enumerate('AB' if t%2==0 else 'BA')]
    actual=[(s['trial'],s['case'],s['position'],s['arm']) for s in samples]
    if actual != expected:
        raise ValueError('missing/reordered paired observations')
    hashes={}
    for s in samples:
        if s['returncode']!=0: raise ValueError('failed retained observation')
        row=json.loads((paired/s['export']).read_text())['results']
        if len(row)!=1: raise ValueError('wrong export arity')
        r=row[0]
        if r['kind']!='fixed' or r['function']!='Hex.SignDetBench.InteractingBench.'+s['case'] or not r['hashes_agree']:
            raise ValueError('wrong fixed result')
        config=r['config']
        if config != {'warmup_first_iter':False,'warmup':True,'repeats':1,'min_total_seconds':0.1,
                      'max_seconds_per_call':10,'expected_hash':None}:
            raise ValueError('changed fixed settings')
        if len(r['points'])!=1 or r['points'][0]['status']!='ok':
            raise ValueError('incomplete observation')
        h=r['observed_hash']
        if h is None or h!=hashes.setdefault(s['case'],h): raise ValueError('answer hash mismatch')
        p=r['points'][0]
        if type(p['inner_repeats']) is not int or p['inner_repeats']<=0 or p['total_nanos']<=0:
            raise ValueError('invalid measurement')
    return samples


if __name__=='__main__':
    print(f'{len(validate())} retained paired observations and both reconstructed sources pass')
