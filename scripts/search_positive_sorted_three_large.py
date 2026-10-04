"""Untrusted exact-certificate search; the generated Lean identity is the proof.
The rational certificate is recovered and checked before it is emitted.
"""
import sympy as s, itertools, numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
from fractions import Fraction
from pathlib import Path
V=s.symbols('B C D E F');B,C,D,E,F=V
z=(s.Integer(3),B+4,C+D+9,D+9,E+4,F+6)
names=('m1','i1','m2','i2','m3','i3')
def step(z,g):
 a,b,c,d,e,f=z
 return dict(m1=(a,a*b-d,a*c-e,b,c,f),i1=(a,d,e,a*d-b,a*e-c,f),m2=(a*d-b,a,c,d,d*e-f,e),i2=(b,b*d-a,c,d,f,d*f-e),m3=(a,f*b-c,b,f*d-e,d,f),i3=(a,c,f*c-b,e,f*e-d,f))[g]
def exps(n,maxd):
 if n==0:yield();return
 for k in range(maxd+1):
  for tail in exps(n-1,maxd-k):yield(k,)+tail

def pd(p):return s.Poly(s.expand(p),*V).as_dict()
def shift(p,m):return{tuple(a+b for a,b in zip(k,m)):v for k,v in p.items()}
def degree(p):return max(map(sum,p),default=0)
a,b,c,d,e,f=z
q1=a*c*d*f-a*b*d-a*c*e-b*c*f-d*e*f+sum(t*t for t in z)-8
q2=a*f-b*e+c*d
marker=32+2*(a*b*d+a*c*e+b*c*f+d*e*f)-4*sum(t*t for t in z)
guards=[];seen=set()
for n in range(1,4):
 for w in itertools.product(names,repeat=n):
  zz=z
  for g in w:zz=step(zz,g)
  p=pd(sum(zz)-sum(z))
  key=tuple(sorted(p.items()))
  if p and key not in seen:
   seen.add(key);guards.append(('word:'+','.join(w),p))
guards+=[('triangle:'+t,pd(-7-(u*u+v*v+w*w-u*v*w))) for t,u,v,w in [('abd',a,b,d),('ace',a,c,e),('bcf',b,c,f),('def',d,e,f)]]
guards.append(('marker',pd(marker-1)))
for n in [6]:
 rows=list(exps(5,n));ix={m:i for i,m in enumerate(rows)}
 for q in[4,-4]:
  cols=[];labels=[];cost=[];bounds=[]
  for m in rows:
   cols.append({m:s.Integer(1)});labels.append(('mono',m));cost.append(1);bounds.append((0,None))
  for name,p in guards:
   if degree(p)>n:continue
   for m in exps(5,n-degree(p)):
    cols.append(shift(p,m));labels.append((name,m));cost.append(1);bounds.append((0,None))
  for name,p in [('q1',pd(q1)),('q2',pd(q2-q))]:
   for m in exps(5,n-degree(p)):
    cols.append(shift(p,m));labels.append((name,m));cost.append(0);bounds.append((None,None))
  rr=[];cc=[];data=[]
  for j,p in enumerate(cols):
   for m,v in p.items():rr.append(ix[m]);cc.append(j);data.append(float(v))
  mat=csc_matrix((data,(rr,cc)),shape=(len(rows),len(cols)));rhs=np.zeros(len(rows));rhs[ix[(0,)*5]]=-1
  import flint,json
  for attempt in range(25):
   out=linprog(cost,A_eq=mat,b_eq=rhs,bounds=bounds,method='highs-ds', options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
   print(n,q,attempt,len(cols),out.message,flush=True)
   if not out.success:break
   supp=[j for j,v in enumerate(out.x)if v!=0]
   aug=flint.fmpq_mat([[int(cols[j].get(m,0))for j in supp]+[-int(m==(0,)*5)]for m in rows])
   rrk,rank=aug.rref();exact={};consistent=True
   for i in range(rank):
    first=next((j for j in range(len(supp)+1)if rrk[i,j]),None)
    if first==len(supp):consistent=False;break
    exact[supp[first]]=Fraction(str(rrk[i,len(supp)]))
   if not consistent:
    print('inconsistent support',flush=True);break
   bad=[j for j,v in exact.items()if bounds[j][0] is not None and v<0]
   print('support',len(supp),'rank',rank,'negative',len(bad),flush=True)
   if not bad:
    residual={m:Fraction(int(m==(0,)*5))for m in rows}
    for j,x in exact.items():
     for m,v in cols[j].items():residual[m]+=x*int(v)
    assert not any(residual.values())
    entries=[(labels[j],str(v))for j,v in exact.items()if v]
    certificate_dir=Path(__file__).resolve().parent/'certificates'
    certificate_dir.mkdir(exist_ok=True)
    branch='plus' if q==4 else 'minus'
    (certificate_dir/f'positive_sorted_three_large_{branch}.json').write_text(json.dumps(entries,indent=2))
    print('EXACT POSITIVE',q,len(entries),flush=True);break
   for j in bad:bounds[j]=(0,0)
