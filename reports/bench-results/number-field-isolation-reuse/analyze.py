from pathlib import Path
import json,statistics
ROOT=Path(__file__).parent
for family in ['pairs','numberfield-pairs','exact-ladder-pairs','root-pairs']:
 p=ROOT/family;m=json.loads((p/'metadata.json').read_text());out={'cases':{},'failed_arms':[],'all_completed_arms':len(m['arms'])}
 for case in dict.fromkeys(a['case'] for a in m['arms']):
  raw=[];ratios=[]
  for block in range(4):
   vals={}
   for arm in ['Before','After']:
    a=next(a for a in m['arms'] if (a['case'],a['block'],a['arm'])==(case,block,arm));x=json.loads((p/a['output']).read_text())['results'][0]
    good=a['exit_code']==0 and x['expected_hash_check']['status']=='match' and x['hashes_agree'] and all(z['status']=='ok' for z in x['points'])
    row={'block':block,'arm':arm,'exit_code':a['exit_code'],'status':[z['status'] for z in x['points']],'hash':x['observed_hash'],'median_ms':None if x['median_nanos'] is None else x['median_nanos']/1e6,'inner_repeats':[z['inner_repeats'] for z in x['points']]};raw.append(row)
    if good: vals[arm]=row['median_ms']
    else:out['failed_arms'].append({'case':case,**row})
   if len(vals)==2:ratios.append(vals['Before']/vals['After'])
  out['cases'][case]={'arms':raw,'successful_adjacent_pairs':len(ratios),'median_adjacent_before_after_ratio':statistics.median(ratios) if ratios else None,'ratio_range':[min(ratios),max(ratios)] if ratios else None}
  for arm in ['Before','After']:
   xs=[r['median_ms'] for r in raw if r['arm']==arm and r['median_ms'] is not None];out['cases'][case][arm.lower()+'_median_ms']=statistics.median(xs) if xs else None
 (p/'analysis.json').write_text(json.dumps(out,indent=2)+'\n')
 print(family,[(c,round(v['before_median_ms'] or 0,3),round(v['after_median_ms'] or 0,3),round(v['median_adjacent_before_after_ratio'] or 0,3)) for c,v in out['cases'].items()], 'failures',len(out['failed_arms']))
