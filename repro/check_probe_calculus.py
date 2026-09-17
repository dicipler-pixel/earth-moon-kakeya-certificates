#!/usr/bin/env python3
"""Exact finite checks for probe residues, kernel updates and source-aware Schur reduction.
Standard library only. No network, file downloads, floating point or Lean claim.
"""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json, random, sys


def need(b,why):
    if not b: raise ValueError(why)
def tr(A): return list(map(list,zip(*A)))
def mm(A,B): return [[sum((x*y for x,y in zip(r,c)),F(0)) for c in tr(B)] for r in A]
def plus(A,B): return [[x+y for x,y in zip(r,s)] for r,s in zip(A,B)]
def minus(A,B): return [[x-y for x,y in zip(r,s)] for r,s in zip(A,B)]
def scale(a,A): return [[a*x for x in r] for r in A]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def outer(v,w): return [[x*y for y in w] for x in v]
def mv(A,v): return [sum((x*y for x,y in zip(r,v)),F(0)) for r in A]
def dot(u,v): return sum((x*y for x,y in zip(u,v)),F(0))
def det(A):
    n=len(A);a=[list(map(F,r)) for r in A];d=F(1)
    for j in range(n):
        k=next((k for k in range(j,n) if a[k][j]),None)
        if k is None:return F(0)
        if k!=j:a[j],a[k]=a[k],a[j];d=-d
        p=a[j][j];d*=p
        for k in range(j+1,n):
            c=a[k][j]/p
            for l in range(j+1,n):a[k][l]-=c*a[j][l]
    return d

def inv(A):
    n=len(A);a=[list(map(F,r))+s for r,s in zip(A,eye(n))]
    for j in range(n):
        k=next((k for k in range(j,n) if a[k][j]),None)
        if k is None:raise ValueError('singular inverse')
        a[j],a[k]=a[k],a[j];p=a[j][j];a[j]=[x/p for x in a[j]]
        for k in range(n):
            if k!=j:
                p=a[k][j];a[k]=[x-p*y for x,y in zip(a[k],a[j])]
    return [r[n:] for r in a]

def kernel(A,n):
    a=[list(map(F,r)) for r in A];piv=[];j=0
    for c in range(n):
        k=next((k for k in range(j,len(a)) if a[k][c]),None)
        if k is None:continue
        a[j],a[k]=a[k],a[j];p=a[j][c];a[j]=[x/p for x in a[j]]
        for k in range(len(a)):
            if k!=j:
                p=a[k][c];a[k]=[x-p*y for x,y in zip(a[k],a[j])]
        piv.append(c);j+=1
        if j==len(a):break
    cols=[]
    for c in range(n):
        if c in piv:continue
        x=[F(0)]*n;x[c]=1
        for j,p in enumerate(piv):x[p]=-a[j][c]
        cols.append(x)
    return cols

def projector(A,n):
    cols=kernel(A,n)
    if not cols:return scale(F(0),eye(n)),0
    C=tr(cols);return mm(mm(C,inv(mm(tr(C),C))),tr(C)),len(cols)
def polynomial(values):
    n=len(values);V=[[F(i)**j for j in range(n)] for i in range(n)]
    return mv(inv(V),values)
def fsq(A):return sum((x*x for r in A for x in r),F(0))
def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,list):return [encode(y) for y in x]
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    return x


def run():
    rng=random.Random(20260917);nprobe=nupdates=nweight=0;records=[]
    for d in range(2,7):
        for m in range(1,d+2):
            for repeat in range(2):
                A=[[F(rng.randrange(-2,3)) for _ in range(d)] for _ in range(m)]
                L=mm(tr(A),A);P,k=projector(A,d)
                tau=[F(rng.randrange(-2,3)) for _ in range(d)]
                if not any(tau):tau[0]=1
                rho=dot(tau,mv(P,tau));need(rho>=0,'negative projector response')
                # Values determine these polynomials exactly. The displayed
                # theorem proves the polynomial and leading-coefficient claims.
                ps=[];qs=[]
                for e in range(d+1):
                    M=plus(L,scale(F(e),eye(d)));p=det(M)
                    ps.append(p);qs.append(det(plus(M,outer(tau,tau)))-p)
                    if e:
                        need(qs[-1]==p*dot(tau,mv(inv(M),tau)),'probe determinant identity')
                pc=polynomial(ps);qc=polynomial(qs)
                need(next(i for i,x in enumerate(pc) if x)==k,'determinant nullity order')
                if k:
                    need(qc[k-1]==pc[k]*rho,'wrong numerator residue')
                    need(all(x==0 for x in qc[:k-1]),'unexpected lower numerator coefficient')
                W=[F(rng.randrange(1,5)) for _ in range(m)]
                LW=mm(tr(A),[[w*x for x in row] for row,w in zip(A,W)])
                PW,kw=projector(LW,d)
                need(PW==P and kw==k,'positive weights changed exact kernel');nweight+=1
                u=[F(rng.randrange(-2,3)) for _ in range(d)];w=mv(P,u);ww=dot(w,w)
                Pn,kn=projector(A+[u],d)
                predicted=P if not ww else minus(P,scale(1/ww,outer(w,w)))
                need(Pn==predicted,'rank-one kernel update')
                gain=rho-dot(tau,mv(Pn,tau))
                need(gain==(dot(tau,w)**2/ww if ww else 0),'target gain')
                need(fsq(minus(P,Pn))==k-kn,'projector distance not rank loss')
                records.append({'dimension':d,'rows':m,'nullity':k,'rho':rho,'gain':gain,
                                'det_leading':pc[k], 'probe_leading':qc[k-1] if k else None})
                nupdates+=1;nprobe+=1
    # A zero immediate gain can be indispensable to a later exact completion.
    t=[F(1),F(-1)];P0=eye(2);P1,_=projector([[1,1]],2);P2,_=projector([[1,1],[1,0]],2)
    need(dot(t,mv(P0,t))==dot(t,mv(P1,t))==2 and dot(t,mv(P2,t))==0,'zero-gain control')
    # Two-source elimination: retain matrix, two reduced sources, determinant
    # multiplier and the already-eliminated scalar bilinear response.
    A=[[F(rng.randrange(-2,3)) for _ in range(6)] for _ in range(6)]
    M=plus(mm(tr(A),A),eye(6));b=[F(x) for x in [1,-1,2,3,1,-2]];c=[F(x) for x in [-2,1,3,1,2,1]]
    full=dot(c,mv(inv(M),b));outcomes=[]
    for order in permutations(range(4)):
        labels=list(range(6));S=[r[:] for r in M];bb=b[:];cc=c[:];w=F(1);a=F(0)
        for v in order:
            i=labels.index(v);I=[j for j in range(len(labels)) if j!=i];p=S[i][i]
            need(p>0,'SPD pivot not positive');a+=cc[i]*bb[i]/p;w*=p
            nb=[bb[j]-S[j][i]*bb[i]/p for j in I]
            nc=[cc[j]-S[j][i]*cc[i]/p for j in I]
            S=[[S[j][k]-S[j][i]*S[i][k]/p for k in I] for j in I for _ in [0]]
            labels=[labels[j] for j in I];bb,cc=nb,nc
        need(a+dot(cc,mv(inv(S),bb))==full,'lost source response')
        need(w*det(S)==det(M),'lost determinant weight')
        outcomes.append([S,bb,cc,w,a])
    need(all(x==outcomes[0] for x in outcomes),'elimination order is not coherent')
    # A subsequent boundary load is tested against the same retained registers.
    S,bb,cc,w,a=outcomes[0];loads=[]
    for z in [F(0),F(1,3),F(1),F(5)]:
        MM=[r[:] for r in M];MM[5][5]+=z;SS=[r[:] for r in S];SS[1][1]+=z
        need(a+dot(cc,mv(inv(SS),bb))==dot(c,mv(inv(MM),b)),'loaded response')
        need(w*det(SS)==det(MM),'loaded determinant');loads.append(z)
    # Same Schur response is not the same determinant-valued context.
    X=[[F(2),F(1)],[F(1),F(2)]];Y=[[F(8),F(2)],[F(2),F(2)]]
    need(X[1][1]-X[1][0]**2/X[0][0]==Y[1][1]-Y[1][0]**2/Y[0][0]==F(3,2),'control response')
    need(det(X)==3 and det(Y)==12,'determinant control')
    return encode({'status':'PASS','probe_polynomial_systems':nprobe,'positive_weight_kernel_tests':nweight,
       'rank_one_updates':nupdates,'coherent_elimination_orders':len(outcomes),'post_elimination_loads':loads,
       'zero_immediate_gain_control':{'initial_residual':2,'after_first':2,'after_second':0},
       'same_response_different_determinant_control':[3,12], 'records':records,
       'scope':'Exact finite checks of the accompanying written identities; not analytic convergence, Lean, or an amplitude equivalence.'})

if __name__=='__main__':
    report=run();out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'results/probe_calculus_checks.json'
    out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='records'},indent=2))
