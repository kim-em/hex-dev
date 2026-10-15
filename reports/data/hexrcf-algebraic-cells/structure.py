import json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[3];p=root/'conformance-fixtures/HexRCF'
packet=json.loads((p/'cell-algebraic.json').read_text());scalars=json.loads((p/'cell-algebraic-scalars.json').read_text());graphs=[('roots',packet[0])]
for i,row in enumerate(packet[1]):graphs.append((f'section/{i}',row[4]))
for i,sector in enumerate(packet[2]):
 for j,label in [(1,'left'),(2,'right')]:
  if sector[j] is not None:graphs.append((f'sector/{i}/{label}',sector[j][4]))
 graphs.extend([(f'sector/{i}/point',sector[4]),(f'sector/{i}/row',sector[5][4])])
for i,scalar in enumerate(scalars):graphs.append((f'scalar/{i}',scalar[2]))
rows=[]
for label,g in graphs:
 assert g[0]==1 and len(g)==3
 root_index,entries=g[1:];assert 0<=root_index<len(entries)
 expanded=[]
 for i,(_,children) in enumerate(entries):
  assert len(children) in (0,1)
  if not children:expanded.append(1)
  else:
   pair=children[0];assert len(pair)==2 and all(0<=c<i for c in pair)
   expanded.append(1+sum(expanded[c] for c in pair))
 rows.append(dict(path=label,retained_nodes=len(entries),expanded_visits=expanded[root_index],sha256=hashlib.sha256(json.dumps(g,separators=(',',':')).encode()).hexdigest()))
result=dict(schema='hex-rcf-algebraic-cell-structure-v1',graph_occurrences=len(rows),retained_nodes=sum(r['retained_nodes'] for r in rows),expanded_visits=sum(r['expanded_visits'] for r in rows),distinct_graph_literals=len({r['sha256'] for r in rows}),matrix_graphs=sum(not r['path'].startswith('scalar/') for r in rows),fixtures={f:dict(bytes=(p/f).stat().st_size,sha256=hashlib.sha256((p/f).read_bytes()).hexdigest()) for f in ['cell-algebraic.json','cell-algebraic-scalars.json','cell-algebraic-mutations.json']},graphs=rows,scope='Graph occurrences explicitly consumed as matrix or scalar packets. Nested immutable context-frame literals and internal Sturm/Tarski records are not separate graph occurrences here. Expanded visits unroll repeated binary child references and do not measure validation work or kernel proof size.')
print(json.dumps(result,indent=2))
