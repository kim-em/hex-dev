"""Compare complete bases exactly while retaining only one normalized basis."""
import hashlib
import json
from scripts.oracle.groebner_singular import polynomial


def fingerprint(poly):
    return hashlib.sha256(json.dumps(poly,separators=(',',':')).encode()).digest()


def same_basis(rows,text,variables,p):
    """Consume decoded candidate rows; hashes only index exact-comparison buckets."""
    if not text.startswith('[')or not text.endswith(']:'):return False
    buckets={}
    for i,row in enumerate(rows):
        terms=[]
        for powers,coefficient in row:
            if len(powers)!=variables or type(coefficient)is not int or not 0<coefficient<p:
                return False
            if any(type(power)is not int or power<0 for power in powers):return False
            terms.append((tuple(powers),coefficient))
        rows[i]=None
        if not terms:continue
        terms.sort();buckets.setdefault(fingerprint(terms),[]).append(terms)
    row=None
    body=text[1:-2].strip()
    start=0
    while start<len(body):
        end=body.find(',',start)
        if end<0:end=len(body)
        terms=polynomial(body[start:end],variables,p);start=end+1
        key=fingerprint(terms);bucket=buckets.get(key)
        if bucket is None:return False
        for i,expected in enumerate(bucket):
            if terms==expected:
                bucket.pop(i)
                if not bucket:del buckets[key]
                break
        else:return False
    return not buckets
