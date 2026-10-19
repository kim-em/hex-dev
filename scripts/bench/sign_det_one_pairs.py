#!/usr/bin/env python3
"""Retain a short LeanBench comparison of the denominator-one fast paths."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
from cpu_lease import cpu_lease


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('baseline', type=Path); p.add_argument('candidate', type=Path)
    p.add_argument('output', type=Path)
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    binaries = {'A':a.baseline.resolve(), 'B':a.candidate.resolve()}
    cpu, lease = cpu_lease()
    with lease:
        previous = sorted(os.sched_getaffinity(0)); os.sched_setaffinity(0,{cpu})
        metadata = {'trials':6, 'cases':['depthOne','depthTwo'], 'order':'AB/BA alternating',
                    'host':platform.node(), 'platform':platform.platform(), 'cpu':cpu,
                    'originalAffinity':previous, 'loadBefore':os.getloadavg(),
                    'binaries':{k:{'path':str(v),'sha256':hashlib.sha256(v.read_bytes()).hexdigest()}
                                for k,v in binaries.items()},
                    'collectorSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        (a.output/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
        expected = {}; samples = []
        with (a.output/'samples.jsonl').open('w') as stream:
            for trial in range(6):
                for case in metadata['cases']:
                    for position,arm in enumerate('AB' if trial%2 == 0 else 'BA'):
                        path = a.output/f'{trial}-{case}-{arm}.json'
                        command = [str(binaries[arm]),'run','--filter',case,'--export-file',str(path.resolve())]
                        result = subprocess.run(command,capture_output=True)
                        path.with_suffix('.stdout').write_bytes(result.stdout)
                        path.with_suffix('.stderr').write_bytes(result.stderr)
                        sample = {'trial':trial,'case':case,'position':position,'arm':arm,
                                  'command':command,'returncode':result.returncode,'load':os.getloadavg(),
                                  'export':path.name}
                        stream.write(json.dumps(sample)+'\n'); stream.flush()
                        if result.returncode: raise RuntimeError('LeanBench execution failed; retained partial collection')
                        rs = json.loads(path.read_text())['results']
                        if len(rs)!=1 or rs[0]['function'] != 'Hex.SignDetBench.InteractingBench.'+case:
                            raise RuntimeError('wrong benchmark result')
                        r = rs[0]
                        if r['kind']!='fixed' or len(r['points'])!=1 or r['points'][0]['status']!='ok' or not r['hashes_agree'] or r['median_nanos'] is None:
                            raise RuntimeError('incomplete fixed observation')
                        h = r['observed_hash']
                        if h is None or h != expected.setdefault(case,h): raise RuntimeError('answer hash mismatch')
                        samples.append({**sample,'nanos':r['median_nanos'],'hash':h})
        summary = {}
        for case in metadata['cases']:
            pairs = [{s['arm']:s['nanos'] for s in samples if s['case']==case and s['trial']==i} for i in range(6)]
            summary[case] = {'baselineMedianNanos':statistics.median(q['A'] for q in pairs),
                             'candidateMedianNanos':statistics.median(q['B'] for q in pairs),
                             'pairRatios':[q['A']/q['B'] for q in pairs],
                             'medianPairRatio':statistics.median(q['A']/q['B'] for q in pairs)}
        (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        metadata['loadAfter']=os.getloadavg()
        (a.output/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
        print(json.dumps(summary))


if __name__ == '__main__': main()
