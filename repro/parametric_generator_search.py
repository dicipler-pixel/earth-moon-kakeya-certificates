#!/usr/bin/env python3
"""Exact one-unrestricted-generator Kakeya exclusion, standard library only.

Scope: the fixed 6-vertex / 7-edge Katz--Tao calibration, two distinct
site/direction placements from the seven-direction pool, and one extra
site row with any nonzero integer label (a,b), a+b != 0. Nonzero target
multiples are allowed. This is not a search over arbitrary towers.

The producer reduces each unbounded projective label family to finitely
many first-escape classes. A separate checker verifies nullspace coverage
and integer closed-set obstruction certificates. Run without -O.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
import json, sys, time

POOL = [(-1,2),(0,1),(1,0),(1,1),(1,2),(2,-1),(2,1)]
# Vertex order (1,1),(1,2),(1,3),(2,1),(2,2),(2,3).
EDGES = [(0,3,(1,0)),(1,4,(1,0)),(2,5,(1,0)),
         (0,1,(0,1)),(1,2,(1,1)),(3,4,(0,1)),(4,5,(0,1))]
NVERT=6; DIM=12

def primitive(x):
    ds=lcm(*(F(a).denominator for a in x)) if x else 1
    y=[int(F(a)*ds) for a in x]
    g=gcd(*y) if y else 0
    if not g: return y
    y=[a//g for a in y]
    if next(a for a in y if a)!=abs(next(a for a in y if a)): y=[-a for a in y]
    return y

def site(v,label,n=NVERT):
    u=[0]*(2*n);u[2*v:2*v+2]=label;return u

def edge_rows(n=NVERT,edges=EDGES):
    out=[]
    for u,v,x in edges:
        r=site(u,x,n);r[2*v]-=x[0];r[2*v+1]-=x[1];out.append(r)
    return out

def null_columns(rows,d):
    a=[[F(v) for v in row] for row in rows if any(row)]
    piv=[];j=0
    for c in range(d):
        k=next((k for k in range(j,len(a)) if a[k][c]),None)
        if k is None:continue
        a[j],a[k]=a[k],a[j]
        p=a[j][c];a[j]=[z/p for z in a[j]]
        for k in range(len(a)):
            if k!=j and a[k][c]:
                p=a[k][c];a[k]=[z-p*w for z,w in zip(a[k],a[j])]
        piv.append(c);j+=1
        if j==len(a):break
    cols=[]
    for c in range(d):
        if c in piv:continue
        v=[F(0)]*d;v[c]=1
        for k,p in enumerate(piv):v[p]=-a[k][c]
        cols.append(primitive(v))
    return cols

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def impose(cols,u):
    w=[dot(u,c) for c in cols]
    p=next((i for i,x in enumerate(w) if x),None)
    if p is None:return [c[:] for c in cols]
    out=[]
    for j in range(len(cols)):
        if j!=p:out.append(primitive([w[p]*a-w[j]*b for a,b in zip(cols[j],cols[p])]))
    return out

def closure(cols,known,n=NVERT):
    cols=[c[:] for c in cols];known=set(known)
    changed=True
    while changed:
        changed=False
        for v in range(n):
            if v not in known and all(c[2*v]==c[2*v+1] for c in cols):
                known.add(v);cols=impose(cols,site(v,(1,0),n));changed=True
    return sorted(known),cols

def direction_classes(cols,known,n=NVERT):
    """First-escape cover: empty, unique ray, or a rank-one image plane."""
    reps=set();counts={'empty':0,'ray':0,'plane':0,'forbidden_or_zero_image':0}
    for v in range(n):
        A=[c[2*v] for c in cols];B=[c[2*v+1] for c in cols]
        for t in range(n):
            if t in known:continue
            r=[c[2*t]-c[2*t+1] for c in cols]
            p=next((j for j,z in enumerate(r) if z),None)
            if p is None:raise ValueError('Input known set is not closed')
            eq=[(r[p]*A[j]-r[j]*A[p],r[p]*B[j]-r[j]*B[p]) for j in range(len(cols))]
            first=next((q for q in eq if q!=(0,0)),None)
            if first is None:
                counts['plane']+=1
                chosen=next((x for x in [(1,0),(0,1),(1,1)]
                    if any(x[0]*a+x[1]*b for a,b in zip(A,B))),None)
                if chosen is None:counts['forbidden_or_zero_image']+=1;continue
                # Every nonzero image lies on r; all such labels define the
                # same added row space modulo the fixed known-coordinate rows.
                reps.add((v,*chosen));continue
            a,b=first
            if any(a*y-b*x for x,y in eq):counts['empty']+=1;continue
            counts['ray']+=1
            x=primitive((-b,a))
            if sum(x)==0 or not any(x[0]*s+x[1]*t for s,t in zip(A,B)):
                counts['forbidden_or_zero_image']+=1;continue
            reps.add((v,*x))
    return sorted(reps),counts

def barrier(cols,known,n=NVERT):
    if len(known)==n:raise ValueError('No proper barrier for a complete object')
    return {'known':known,'dual':{str(v):next(c for c in cols if c[2*v]!=c[2*v+1])
                                for v in range(n) if v not in known}}

def solve_rows(rows,n=NVERT,initial=()):
    rr=rows+[site(v,l,n) for v in initial for l in [(1,0),(0,1)]]
    return closure(null_columns(rr,2*n),initial,n)

def controls():
    kt2=[(1,(1,0)),(3,(1,1)),(0,(1,1)),(2,(0,1))]
    rr=edge_rows()+[site(v,x) for v,x in kt2]
    k,_=solve_rows(rr);assert len(k)==6
    kbad,_=solve_rows(rr[:-1]);assert kbad==[]
    # The enumerator itself, not just its closure engine, must rediscover
    # a complete fourth-generator class from three fixed positive-control rows.
    K,C=solve_rows(rr[:-1]); reps,_=direction_classes(C,K)
    hits=[]
    for v,a,b in reps:
        known,_=closure(impose(C,site(v,(a,b))),K)
        if len(known)==6:hits.append([v,a,b])
    assert hits, 'Positive extension search did not recover any complete class'
    r4=[[1,0,0,0,-1,0,0,0],[0,0,1,0,0,0,-1,0],
        [1,2,-1,-2,0,0,0,0],[0,0,0,0,0,1,0,-1],
        [0,0,1,1,0,0,0,0],[0,0,0,0,0,0,1,1],[0,1,0,0,0,0,0,0]]
    k,_=solve_rows(r4,4);assert len(k)==4
    assert len(solve_rows([[1,1],[1,0]],1)[0])==1
    return {'kt_11_6_complete':True,'kt_minus_generator_closure':kbad,
            'kt_7_4_complete':True,'extension_positive_complete_representatives':hits,
            'one_site_zero_first_gain_then_complete':True}

def run(out):
    start=time.perf_counter(); out=Path(out);out.mkdir(parents=True,exist_ok=True)
    base=edge_rows();options=[(v,x) for v in range(6) for x in POOL]
    records=[];winners=[];nrep=0;tot={'empty':0,'ray':0,'plane':0,'forbidden_or_zero_image':0}
    ctrl=controls()
    for idx,(i,j) in enumerate(combinations(range(len(options)),2)):
        seeds=[options[i],options[j]];rows=base+[site(v,x) for v,x in seeds]
        K,C=solve_rows(rows)
        if len(K)==6:raise RuntimeError('Unexpected complete two-seed object')
        reps,counts=direction_classes(C,K)
        for key in tot:tot[key]+=counts[key]
        case={'placements':[i,j],'base_known':K,'base_null_columns':C,'classes':counts,'representatives':[]}
        for v,a,b in reps:
            T,D=closure(impose(C,site(v,(a,b))),K)
            entry={'generator':[v,a,b]}
            if len(T)==6:
                actual,_=solve_rows(rows+[site(v,(a,b))])
                entry['relaxed_complete']=True;entry['actual_known']=actual
                winners.append({'placements':[i,j],'generator':[v,a,b],'actual_known':actual})
            else:entry['barrier']=barrier(D,T)
            case['representatives'].append(entry)
        records.append(case);nrep+=len(reps)
        if (idx+1)%100==0:print('base pairs',idx+1,'reps',nrep,'potential',len(winners),flush=True)
    summary={'schema':'kakeya-one-free-generator-v1','fixed_vertices':6,'fixed_edges':7,
        'generator_cost':3,'score':'5/3','base_pairs':len(records),
        'site_parametric_families':6*len(records),'representative_checks':nrep,
        'first_escape_class_counts':tot,'potential_winners':winners,'controls':ctrl,
        'meaning':'Quantified one-unrestricted-direction families; not a count of disjoint new configurations.',
        'status':'EXCLUDED' if not winners else 'CANDIDATES_REQUIRE_INDEPENDENT_CHECK'}
    obj={'scope':{'pool':[list(x) for x in POOL], 'edges':[[u,v,list(x)] for u,v,x in EDGES],
        'third_label':'all integer pairs (a,b) != (0,0), a+b != 0; arbitrary site',
        'target_rule':'any nonzero integer multiple (a,-a)'},'summary':summary,'cases':records}
    text=json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n'
    (out/'one_free_generator_certificate.json').write_text(text)
    (out/'one_free_generator_summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary,indent=2));print('elapsed_seconds',time.perf_counter()-start)

if __name__=='__main__':run(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'results')
