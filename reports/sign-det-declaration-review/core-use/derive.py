"""Inspect core use with the existing source parser, role index and alias graph."""
from pathlib import Path
import importlib.util,json,sys,hashlib
root=Path(__file__).resolve().parents[3];out=Path(sys.argv[1])
sys.path.insert(0,str(root));p=root/'reports/sign-det-declaration-review/current/normalize.py'
spec=importlib.util.spec_from_file_location('core_use_existing_helpers',p);helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
rows=json.loads((out/'declaration-use.json').read_text());fields=json.loads((out/'structure-fields.json').read_text());imports=json.loads((out/'audit-imports.json').read_text());inputs=json.loads((out/'inputs.json').read_text())
for name,digest in inputs['inputs'].items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
owned=set(inputs['modules']);assert {r['module'] for r in rows}==owned
handwritten=set();names={}
for path in sorted((root/'HexSignDet').rglob('*.lean')):
 module=str(path.relative_to(root).with_suffix('')).replace('/','.')
 for relative,full in helpers.source_names(path).items():
  matches=[r for r in rows if r['module']==module and r['user_name']==full]
  assert len(matches)==1,(module,relative,full,len(matches))
  name=matches[0]['name'];assert name not in handwritten,name
  handwritten.add(name);names[name]={'path':str(path.relative_to(root)),'relative':relative,'public_name':full}
assert len(handwritten)==728,len(handwritten)
index=helpers.SourceIndex();roles={m:dict(index.resolve(m)) for m in imports}
for m,role in roles.items():
 if m in owned:role['category']='SignDet core production'
 elif role['category']=='Sturm production':role['category']='other Hex production'
projections={f['projection'] for f in fields};users,live,modules,aliases=helpers.reference_graph(rows,handwritten,projections,roles)
private={n for n in handwritten if n.startswith('_private.')};paths=[];unreached=[]
from collections import deque
for name in sorted(private):
 q=deque([[name]]);seen={name};found=None
 while q:
  chain=q.popleft()
  if len(chain)>1 and chain[-1] in handwritten-private:found=chain;break
  for client in users.get(chain[-1],[]):
   if client not in seen:seen.add(client);q.append(chain+[client])
 if found:paths.append({'helper':name,'path':found})
 else:unreached.append(name)
public=handwritten-private;without=sorted(public-live)
report={'source_revision':inputs['source_revision'],'imported_modules':len(imports),'production_modules':len(owned),'attributed_constants':len(rows),'handwritten':len(handwritten),'fields':len(projections),'private':len(private),'private_without_handwritten_public_path':unreached,'public_without_external_production_path':[dict(names[n],name=n,clients=users.get(n,[]),client_modules={u:modules[u] for u in users.get(n,[])}) for n in without],'public_without_direct_clients':sorted(n for n in public if not users.get(n)),'axioms':sorted({a for r in rows for a in r['axioms']})}
assert set(report['axioms'])<={'propext','Classical.choice','Quot.sound'},report['axioms']
for name,data in [('summary.json',report),('handwritten.json',names),('helper-paths.json',paths),('downstream-use.json',{'users':users,'modules':modules,'aliases':aliases,'live':sorted(live)}),('module-roles.json',roles)]:
 (out/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
print({k:(len(v) if isinstance(v,list) and k!='axioms' else v) for k,v in report.items()})
# Reuse the companion audit's source-role/import coverage rule for the core selection.
import subprocess
production={}
for file in subprocess.check_output(['git','ls-files','*.lean'],cwd=root,text=True).splitlines():
 path=root/file
 for source in index.project:
  if path.is_relative_to(source):
   name='.'.join(path.relative_to(source).with_suffix('').parts)
   if not name.startswith('Hex'):continue
   role=index.resolve(name)
   if role['path']==file and role['category'] in {'Sturm production','other Hex production','other root-package production'}:production[name]=file
helpers.check_production_imports(production,lambda m:helpers.family_evidence(index,m))
cache={}
def reaches(name,visiting=frozenset()):
 if name.split('.')[0] in {'HexSignDet','HexSignDetTheory'}:return True
 if name in cache:return cache[name]
 if name in visiting:return False
 role=index.resolve(name)
 cache[name]=role['path'] is not None and any(reaches(parent,visiting|{name}) for parent in helpers._parse_imports(root/role['path']))
 return cache[name]
required={name:path for name,path in production.items() if reaches(name)}
missing={name:path for name,path in required.items() if name not in roles}
coverage={'scope':'Tracked Hex production modules with transitive imports to either SignDet root, using the existing SourceIndex and import parser. This is import coverage, not runtime-use or external-client coverage.','production_modules':len(production),'required_modules':len(required),'covered_modules':dict(sorted(required.items())),'missing_modules':missing}
(out/'production-import-coverage.json').write_text(json.dumps(coverage,indent=2,sort_keys=True)+'\n')
assert not missing,missing
print('Production import coverage:',len(required),'required, no missing modules.')
