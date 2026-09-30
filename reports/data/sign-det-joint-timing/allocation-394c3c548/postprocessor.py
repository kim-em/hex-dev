from pathlib import Path
import collections, hashlib, json, re
raw=Path('/tmp/issue-10377-joint-allocation-394c3c548')
pattern=re.compile(r'^lp_Hex_Hex_SignDetBench_Joint_runComparison(?:___redArg|___boxed)?$')
variants=collections.Counter(); callback=0; other=0; stacks=0
with (raw/'comparison-allocations.stacks').open() as stream:
 for line in stream:
  frames, count=line.rstrip().rsplit(' ',1); count=int(count); stacks+=1
  matched=[f for f in frames.split(';') if pattern.fullmatch(f)]
  if matched:
   callback+=count
   for f in set(matched): variants[f]+=count
  else: other+=count
histogram_calls=0; requested_bytes=0
for line in (raw/'comparison-histogram.tsv').read_text().splitlines():
 size,count=map(int,line.split());histogram_calls+=count;requested_bytes+=size*count
summary={'schema':'hex-sign-det-joint-allocation-summary-v1','source_revision':json.loads((raw/'metadata.json').read_text())['revision'],
 'function':'Hex.SignDetBench.Joint.runComparison','parameter':31,
 'whole_process_allocation_calls':1039653778,'histogram_allocation_calls':histogram_calls,
 'whole_process_requested_bytes':requested_bytes,'filtered_stack_allocation_calls':callback+other,
 'exact_callback_stack_allocation_calls':callback,'other_filtered_stack_allocation_calls':other,
 'folded_stacks':stacks,'callback_frame_variants':dict(variants),
 'callback_frame_pattern':pattern.pattern,
 'limitations':['Heaptrack summary and histogram totals are whole-process even with --filter-bt-function.',
 'The original l_Hex callback filter matched no reported allocators; the corrected substring also matches helpers used during preparation.',
 'Exact callback frame matching excludes those preparation stacks; incomplete unwinding can omit callback frames, so this is attributable work, not a complete callback allocation counter.',
 'Requested bytes count malloc/realloc requests intercepted by heaptrack, not all Lean object allocations or live memory.',
 'Instrumented runtime and RSS include heaptrack overhead and are not scientific timing observations.']}
assert histogram_calls==summary['whole_process_allocation_calls']
assert callback>0 and other>0
(raw/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(raw/'postprocessor.py').write_bytes(Path(__file__).read_bytes())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as stream:
  for chunk in iter(lambda:stream.read(1024*1024),b''): h.update(chunk)
 return h.hexdigest()
manifest={'raw_directory':str(raw),'source_revision':summary['source_revision'],
 'artifacts':{p.name:sha(p) for p in raw.iterdir() if p.is_file() and p.name!='artifacts.json'}}
(raw/'artifacts.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(summary,indent=2))
