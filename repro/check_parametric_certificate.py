#!/usr/bin/env python3
"""Independent integer-only checker for the one-free-direction proof cover.
Does not import the search producer. All rank operations are fraction-free.
The proof in the manuscript explains why this finite cover quantifies over
all admissible integer labels, including labels outside every finite box.
"""
from __future__ import annotations
from itertools import combinations, product
from pathlib import Path
from math import gcd
import copy, hashlib, json, sys, time

POOL=[(-1,2),(0,1),(1,0),(1,1),(1,2),(2,-1),(2,1)]
EDGES=[(0,3,(1,0)),(1,4,(1,0)),(2,5,(1,0)),(0,1,(0,1)),(1,2,(1,1)),(3,4,(0,1)),(4,5,(0,1))]

def require(b,msg):
    if not b:raise ValueError(msg)

def canon(v):
    g=gcd(*v) if v else 0
    if not g:return list(v)
    w=[x//g for x in v]
    return [-x for x in w] if next(x for x in w if x)<0 else w

def rank(rows):
    """Integer cross-multiplication echelon, no producer RREF code."""
    a=[canon(r) for r in rows if any(r)]; out=0
    while a:
        p=min(min(i for i,x in enumerate(r) if x) for r in a)
        j=next(j for j,r in enumerate(a) if r[p]);b=a.pop(j);new=[]
        for r in a:
            if r[p]:r=canon([b[p]*x-r[p]*y for x,y in zip(r,b)])
            if any(r):new.append(r)
        a=new;out+=1
    return out

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def site(v,a,b):
    row=[0]*12;row[2*v]=a;row[2*v+1]=b;return row

def fixed_rows():
    out=[]
    for u,v,(a,b) in EDGES:
        r=site(u,a,b);r[2*v]-=a;r[2*v+1]-=b;out.append(r)
    return out

def matrix_integer(cols):
    return all(len(c)==12 and all(type(x) is int for x in c) for c in cols)

def expected_reps(cols,K):
    candidates=set(); counts={'empty':0,'ray':0,'plane':0,'forbidden_or_zero_image':0}
    for v in range(6):
        A=[c[2*v] for c in cols];B=[c[2*v+1] for c in cols]
        for t in range(6):
            if t in K:continue
            r=[c[2*t]-c[2*t+1] for c in cols]
            require(any(r),'base set is not a closed barrier')
            # Unlike the producer, verify all 2x2 wedge coordinates.
            eq=[(r[i]*A[j]-r[j]*A[i],r[i]*B[j]-r[j]*B[i])
                for i in range(len(cols)) for j in range(i+1,len(cols))]
            rk=rank(eq)
            if rk==2:counts['empty']+=1;continue
            if rk==1:
                counts['ray']+=1
                u,w=next(x for x in eq if any(x));a,b=canon([-w,u])
                if a+b==0 or not any(a*x+b*y for x,y in zip(A,B)):
                    counts['forbidden_or_zero_image']+=1;continue
                candidates.add((v,a,b))
            else:
                counts['plane']+=1
                chosen=next(((a,b) for a,b in [(1,0),(0,1),(1,1)]
                            if any(a*x+b*y for x,y in zip(A,B))),None)
                if chosen is None:counts['forbidden_or_zero_image']+=1;continue
                candidates.add((v,*chosen))
    return candidates,counts

def check_case(case,placements):
    i,j=case['placements'];require(0<=i<j<42,'wrong pair index')
    rows=fixed_rows()+[site(v,*x) for v,x in [placements[i],placements[j]]]
    K=case['base_known'];require(K==sorted(set(K)) and set(K)<set(range(6)),'bad base-known set')
    aug=rows+[site(v,a,b) for v in K for a,b in [(1,0),(0,1)]]
    C=case['base_null_columns'];require(matrix_integer(C),'noninteger/null-basis shape')
    require(all(dot(r,c)==0 for r in aug for c in C),'nullspace relation fails')
    require(rank(C)==len(C) and rank(aug)+len(C)==12,'incomplete nullspace basis')
    expected,counts=expected_reps(C,K)
    require(counts==case['classes'],'classification counts differ')
    reps=case['representatives'];given=[tuple(x['generator']) for x in reps]
    require(len(given)==len(set(given)) and set(given)==expected,'first-escape cover missing/extra classes')
    duals=0
    for rec in reps:
        v,a,b=rec['generator'];require(a+b!=0,'forbidden label')
        require('barrier' in rec,'complete representative is not excluded')
        brr=rec['barrier'];T=brr['known'];require(T==sorted(set(T)) and set(K)<=set(T)<set(range(6)),'bad barrier set')
        unknown=set(range(6))-set(T)
        require(set(brr['dual'])==set(map(str,unknown)),'missing target obstruction')
        rr=rows+[site(v,a,b)]
        for t in unknown:
            h=brr['dual'][str(t)]
            require(len(h)==12 and all(type(x) is int for x in h),'dual is not integral')
            require(all(dot(r,h)==0 for r in rr),'dual fails row annihilation')
            require(all(h[2*s]==h[2*s+1]==0 for s in T),'dual fails known-site support')
            require(h[2*t]-h[2*t+1]!=0,'dual does not distinguish target')
            duals+=1
    return len(reps),duals,counts

def direct_closure(rows,n):
    # Independent feasibility criterion: adding tau must not increase row rank,
    # with full free-coordinate slack at known sites.
    K=set();changed=True;d=2*n
    while changed:
        changed=False
        slack=[]
        for v in K:
            for j in [2*v,2*v+1]:
                e=[0]*d;e[j]=1;slack.append(e)
        base=rows+slack;r=rank(base)
        for v in range(n):
            if v not in K:
                tau=[0]*d;tau[2*v]=1;tau[2*v+1]=-1
                if rank(base+[tau])==r:K.add(v);changed=True
    return sorted(K)

def verify_input_anchor(path):
    d=json.loads(path.read_text());p=d['problem'];require(p['dims']==[2,3],'wrong tower')
    vs=list(product(range(1,3),range(1,4)));idx={x:i for i,x in enumerate(vs)};edges=[]
    for lev,entries in enumerate(p['levels']):
        for entry in entries:
            pref=entry['prefix'];x=entry['label']
            for tail in product(*[range(1,b+1) for b in p['dims'][lev+1:]]):
                u=tuple(pref)+tail;vp=pref[:-1]+[pref[-1]+1];v=tuple(vp)+tail
                if any(x):edges.append((idx[u],idx[v],tuple(x)))
    require(edges==EDGES,'producer domain disagrees with recovered tower')
    rows=fixed_rows()+[site(idx[tuple(g['vertex'])],*g['label']) for g in p['generators']]
    require(direct_closure(rows,6)==list(range(6)),'known positive calibration fails')
    return rows

def check(path,out):
    t0=time.perf_counter();path=Path(path);d=json.loads(path.read_text())
    require(d['scope']['pool']==[list(x) for x in POOL],'wrong pool')
    require(d['scope']['edges']==[[u,v,list(x)] for u,v,x in EDGES],'wrong edge domain')
    cases=d['cases'];required=list(combinations(range(42),2))
    require([tuple(c['placements']) for c in cases]==required,'base pair domain is not exactly covered')
    placements=[(v,x) for v in range(6) for x in POOL]
    reps=duals=0;tot={'empty':0,'ray':0,'plane':0,'forbidden_or_zero_image':0}
    for c in cases:
        n,m,ct=check_case(c,placements);reps+=n;duals+=m
        for k in tot:tot[k]+=ct[k]
    summary=d['summary'];require(summary['representative_checks']==reps,'wrong representative total')
    require(summary['base_pairs']==861 and summary['site_parametric_families']==5166,'wrong family totals')
    require(summary['first_escape_class_counts']==tot and summary['potential_winners']==[],'wrong outcome')
    anchor=Path(__file__).resolve().parent/'inputs/kt_11_6.json'
    full=verify_input_anchor(anchor)
    require(direct_closure(full[:-1],6)==[],'known negative control fails')
    # Both declared positive extension representatives must really complete.
    for v,a,b in summary['controls']['extension_positive_complete_representatives']:
        require(direct_closure(full[:-1]+[site(v,a,b)],6)==list(range(6)),'false positive extension control')
    corruptions=[]
    for typ in ['drop_class','erase_dual','corrupt_nullspace']:
        bad=copy.deepcopy(next(c for c in cases if c['representatives']))
        if typ=='drop_class':bad['representatives'].pop()
        elif typ=='erase_dual':
            dual=bad['representatives'][0]['barrier']['dual'];key=next(iter(dual));dual[key]=[0]*12
        else:bad['base_null_columns'][0][0]+=1
        try:check_case(bad,placements)
        except ValueError:corruptions.append(typ)
        else:raise ValueError('Corruption control accepted: '+typ)
    report={'status':'PASS','base_pairs_checked':len(cases),'site_parametric_families':5166,
        'representative_barriers_checked':reps,'integer_target_duals_checked':duals,
        'first_escape_class_counts':tot,'corruptions_rejected':corruptions,
        'source_anchor_sha256':hashlib.sha256(anchor.read_bytes()).hexdigest(),
        'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'claim':'No completing object in the stated one-unrestricted-generator family.',
        'not_claimed':['official Epoch verification','Lean compilation','new exponent','all six-vertex labelings']}
    out=Path(out);out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2));print('elapsed_seconds',time.perf_counter()-t0)

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    check(sys.argv[1] if len(sys.argv)>1 else root/'results/one_free_generator_certificate.json',
          sys.argv[2] if len(sys.argv)>2 else root/'results/independent_parametric_check.json')
