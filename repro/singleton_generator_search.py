#!/usr/bin/env python3
"""One arbitrary generator with any one initially known vertex, fixed KT tower."""
from pathlib import Path
import json,sys
import parametric_generator_search as P

def run(out):
    cases=[];wins=[]
    for t in range(6):
        rows=P.edge_rows()+[P.site(t,(1,0)),P.site(t,(0,1))]
        K,C=P.closure(P.null_columns(rows,12),[t]);reps,cts=P.direction_classes(C,K)
        rec={'initial_known':t,'base_known':K,'base_null_columns':C,'classes':cts,'representatives':[]}
        for v,a,b in reps:
            T,D=P.closure(P.impose(C,P.site(v,(a,b))),K)
            e={'generator':[v,a,b]}
            if len(T)==6:e['complete']=True;wins.append([t,v,a,b])
            else:e['barrier']=P.barrier(D,T)
            rec['representatives'].append(e)
        cases.append(rec)
    obj={'schema':'kakeya-singleton-arbitrary-generator-v1','scope':{'initial_known':'any singleton',
         'fixed_edges':[[u,v,list(x)] for u,v,x in P.EDGES], 'label':'all nonzero integer (a,b), a+b != 0'},
         'summary':{'site_families':36,'representatives':sum(len(x['representatives']) for x in cases),
         'score':'8/5','potential_winners':wins},'cases':cases}
    Path(out).write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(obj['summary'],indent=2))
if __name__=='__main__':
    run(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'results/singleton_generator_certificate.json')
