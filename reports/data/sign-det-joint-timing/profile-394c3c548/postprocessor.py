from pathlib import Path
import collections,hashlib,json,re,shutil
r=Path('/tmp/issue-10377-joint-profile-394c3c548')
old=json.loads((r/'summary.json').read_text());pid=next(x['pid'] for x in old['sidecars'] if x['kind']=='header');regions=old['regions']
counts=collections.Counter();samples=[];outside=0;foreign=0
for line in (r/'perf-ip-pids.txt').read_text().splitlines():
 m=re.fullmatch(r'(\d+)/(\d+)\s+(\d+)\.(\d+):\s+([0-9a-f]+)\s+(.*?)\s+\((.*)\)',line.strip())
 if not m: raise ValueError('unparsed perf event: '+line)
 p,t,sec,frac,ip,sym,dso=m.groups();ns=int(sec)*10**9+int(frac.ljust(9,'0'))
 if not any(a<=ns<=b for a,b in regions): outside+=1;continue
 if int(p)!=pid: foreign+=1;continue
 counts[sym]+=1;samples.append(dict(pid=int(p),tid=int(t),mono_ns=ns,ip=ip,symbol=sym,dso=dso))
assert len(samples)==old['operation_samples']
shutil.copyfile(r/'summary.json',r/'unwind-summary.json')
summary={'operation_samples':len(samples),'outside_operation_samples':outside,'foreign_pid_samples_in_region':foreign,
         'regions':regions,'pid':pid,'thread_ids':sorted({s['tid'] for s in samples}),
         'leaf_counts':dict(counts.most_common()),'samples':samples,
         'scope':'direct sampled instruction pointers within the one cold comparison operation; not allocated bytes or scientific timing',
         'postprocessor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(r/'ip-summary.json').write_text(json.dumps(summary,indent=2)+'\n');(r/'postprocessor.py').write_bytes(Path(__file__).read_bytes())
print('samples',len(samples),'outside',outside,'foreign',foreign)
for symbol,n in counts.most_common(25): print(n,symbol)
