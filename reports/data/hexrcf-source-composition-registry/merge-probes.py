from pathlib import Path
import argparse,hashlib,json,re,subprocess,tempfile
p=argparse.ArgumentParser();p.add_argument('--source');a=p.parse_args()
root=Path.cwd()
show=lambda ref:subprocess.check_output(['git','show',ref+':lakefile.lean'],text=True)
old='73d7ae29113be739bb2c579d9ec86cb7fb12c551'
upstream=subprocess.check_output(['git','rev-parse','87a142bdcd2ef708edfd30002f3c55704e8554f5'],text=True).strip()
base=subprocess.check_output(['git','merge-base',old,upstream],text=True).strip()
ours=show(a.source) if a.source else (root/'lakefile.lean').read_text()
main=show(upstream)
def names(s):
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 return set(re.findall(r'`([A-Za-z0-9_.]+)',s))
def merge(left,ancestor,right):
 with tempfile.TemporaryDirectory(prefix='hex-10358-merge-') as directory:
  paths=[Path(directory)/n for n in ['ours','base','theirs']]
  for path,text in zip(paths,[left,ancestor,right]):path.write_text(text)
  result=subprocess.run(['git','merge-file','--stdout',*[str(x) for x in paths]],text=True,capture_output=True)
  return result.returncode,result.stdout
checks=[]
code,_=merge(show(old),show(base),main)
assert code==1,('actual prior conflict control',code)
checks.append({'name':'prior_actual_conflict','expected':1,'actual':code})
start=main.index('lean_lib HexConformance where')
end=start+1+re.search(r'^lean_lib ',main[start+1:],re.M).start()
part=main[start:end]
needle='`HexGroebner.HitConformance'
assert part.count(needle)==1
first=part.replace(needle,needle+' /- merge probe -/')
pos=part.rindex('.map Glob.one')+len('.map Glob.one')
tail=part[:pos]+' ++\n    #[].map Glob.one'+part[pos:]
for name,changed in [('shared_line_edit',first),('tail_append',tail)]:
 future=main[:start]+changed+main[end:]
 code,output=merge(ours,main,future)
 assert code==0,(name,code)
 assert names(output)==names(ours)|names(future),name
 checks.append({'name':name,'expected':0,'actual':code})
print(json.dumps({'source_sha256':hashlib.sha256(ours.encode()).hexdigest(),'old_head':old,'upstream_commit':upstream,'merge_base':base,'checks':checks},indent=2))
