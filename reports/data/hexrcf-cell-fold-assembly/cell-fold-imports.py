from pathlib import Path
import hashlib,json,subprocess,sys
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358');side=Path('/home/kim/.codex/tasks/hex-10358/boolean-worktree');out=Path('/home/kim/.codex/tasks/hex-10358')
sys.path.insert(0,str(root/'scripts'));from check_dag import parse_imports
prefixes=['','adapters','conformance','Hex','bench','experiments'];seen={};external=set();stack=['HexRCF.CellReplay.Algebraic.Check']
while stack:
 module=stack.pop()
 if module in seen or module in external:continue
 rel=Path(*module.split('.')).with_suffix('.lean')
 candidates=[root/prefix/rel for prefix in prefixes]
 path=next((p for p in candidates if p.is_file()),None)
 if path is None:external.add(module);continue
 name=path.relative_to(root).as_posix();data=path.read_bytes()
 assert data==(side/name).read_bytes(),name
 seen[module]={'path':name,'sha256':hashlib.sha256(data).hexdigest()};stack.extend(parse_imports(path))
forbidden=['HexRCF.RealCoefficients.CellEncode','HexRCF.RealCoefficients.CellCodec','HexRCF.RealCoefficients.SectorEncode','HexRCF.RealCoefficients.CellBuild','HexRCF.RealCoefficients.CellDiscover','HexRCF.RealCoefficients.RootBuild']
assert all(x not in seen for x in forbidden)
record={'root_source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'measurement_context_commit':'5da4aa647ee82620cf23a296f1a0d089bc063eed','target':'HexRCF.CellReplay.Algebraic.Check','local_sources':seen,'external_imports':sorted(external),'excluded_adapter_modules':forbidden}
(out/'cell-fold-imports.json').write_text(json.dumps(record,indent=2)+'\n');print(len(seen),'matched local source modules',len(external),'external import leaves; staged codec/producer modules absent')
