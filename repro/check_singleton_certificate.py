#!/usr/bin/env python3
"""Independent checker; imports integer checker utilities, never the producer."""
from pathlib import Path
import hashlib,json,sys
from check_parametric_certificate import require,rank,dot,site,fixed_rows,matrix_integer,expected_reps,EDGES

def check(path,out):
    path=Path(path);d=json.loads(path.read_text());require(d['schema']=='kakeya-singleton-arbitrary-generator-v1','schema')
    require(d['scope']['fixed_edges']==[[u,v,list(x)] for u,v,x in EDGES],'edge domain')
    require([c['initial_known'] for c in d['cases']]==list(range(6)),'initial-known domain')
    total=duals=0
    for case in d['cases']:
        t=case['initial_known'];K=case['base_known'];C=case['base_null_columns']
        require(K==sorted(set(K)) and {t}<=set(K)<set(range(6)),'base known set')
        rows=fixed_rows();aug=rows+[site(v,a,b) for v in K for a,b in [(1,0),(0,1)]]
        require(matrix_integer(C) and all(dot(r,c)==0 for r in aug for c in C),'nullspace')
        require(rank(C)==len(C) and rank(aug)+len(C)==12,'nullspace completeness')
        expected,cts=expected_reps(C,K);require(cts==case['classes'],'classes')
        given=[tuple(x['generator']) for x in case['representatives']]
        require(len(given)==len(set(given)) and set(given)==expected,'first-escape coverage')
        for rec in case['representatives']:
            v,a,b=rec['generator'];require(a+b!=0,'forbidden generator')
            require('barrier' in rec,'unexcluded representative');br=rec['barrier'];T=br['known']
            require(T==sorted(set(T)) and set(K)<=set(T)<set(range(6)),'barrier')
            unknown=set(range(6))-set(T);require(set(br['dual'])==set(map(str,unknown)),'missing dual')
            for x in unknown:
                h=br['dual'][str(x)];require(len(h)==12 and all(type(a) is int for a in h),'dual integers')
                require(all(dot(r,h)==0 for r in rows+[site(v,a,b)]),'annihilation')
                require(all(h[2*y]==h[2*y+1]==0 for y in T),'known slack')
                require(h[2*x]!=h[2*x+1],'target separation');duals+=1
        total+=len(given)
    require(d['summary']['potential_winners']==[] and d['summary']['representatives']==total,'outcome')
    r={'status':'PASS','initial_known_sets':6,'site_parametric_families':36,'representatives_checked':total,
       'integer_target_duals_checked':duals,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
       'claim':'No completion on the fixed seven-edge tower with one initially known vertex and one arbitrary admissible integer site generator.'}
    Path(out).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    check(sys.argv[1] if len(sys.argv)>1 else root/'results/singleton_generator_certificate.json',
          sys.argv[2] if len(sys.argv)>2 else root/'results/independent_singleton_check.json')
