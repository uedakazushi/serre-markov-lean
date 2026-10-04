"""Emit exact kernel proofs from rational nonnegative polynomial certificates."""
from pathlib import Path
from fractions import Fraction
from math import lcm
from collections import defaultdict
import json
import sympy as s
vars=s.symbols('B C D E F');B,C,D,E,F=vars
z=(s.Integer(3),B+4,C+D+9,D+9,E+4,F+6)
a,b,c,d,e,f=z
q1=a*c*d*f-a*b*d-a*c*e-b*c*f-d*e*f+sum(t*t for t in z)-8
q2=a*f-b*e+c*d
names=('m1','i1','m2','i2','m3','i3')
def step(z,g):
 a,b,c,d,e,f=z
 return dict(m1=(a,a*b-d,a*c-e,b,c,f),i1=(a,d,e,a*d-b,a*e-c,f),m2=(a*d-b,a,c,d,d*e-f,e),i2=(b,b*d-a,c,d,f,d*f-e),m3=(a,f*b-c,b,f*d-e,d,f),i3=(a,c,f*c-b,e,f*e-d,f))[g]
def mon(m):return s.prod(v**i for v,i in zip(vars,m))
def guard(n,q):
 if n=='mono':return s.Integer(1)
 if n=='q1':return q1
 if n=='q2':return q2-q
 if n.startswith('word:'):
  zz=z
  for g in n[5:].split(','):zz=step(zz,g)
  return s.expand(sum(zz)-sum(z))
 if n=='triangle:abd':return -7-(a*a+b*b+d*d-a*b*d)
 if n=='triangle:ace':return -7-(a*a+c*c+e*e-a*c*e)
 raise ValueError(n)
def leanmono(m):
 a=[str(v)if i==1 else f'{v}^{i}'for v,i in zip(vars,m)if i]
 return '*'.join(a)or'1'
def leanpoly(items):
 out=[]
 for m,n in items:
  if not n:continue
  if m==(0,)*5:term=str(abs(n))
  else:term=f'{abs(n)}*{leanmono(m)}'
  out.append(('-'if n<0 else '+')+term)
 return ''.join(out).lstrip('+')or'0'
def nonnegproof(items):
 proofs=[]
 for m,n in items:
  assert n>=0
  p=f'(Int.natCast_nonneg {n})'
  for v,i in zip(vars,m):
   if i:
    pp=f'h{v}' if i==1 else f'(pow_nonneg h{v} {i})'
    p=f'(mul_nonneg {p} {pp})'
  proofs.append(p)
 p=proofs[0]
 for q in proofs[1:]:p=f'(add_nonneg {p} {q})'
 return p
lines=['''import SerreMarkov.PositiveTriangleLower
import SerreMarkov.PositiveShortWord
import SerreMarkov.PositiveThreeTriangles

/-! # The sorted first-edge-three large positive chamber

Exact nonnegative degree-six identities exclude `d≥9` when `a=3`, `d≤c`,
and `f≥6`. The hypotheses are actual solution/chamber and three-letter
no-drop statements. No bound on the original height is supplied.
-/
namespace SerreMarkov.PositiveSortedThreeLarge
open PositiveChamber PositiveShortWord NegativeDescent
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
''']
for sign,q in [('plus',4),('minus',-4)]:
 entries=json.loads(Path(f'scripts/certificates/positive_sorted_three_large_{sign}.json').read_text())
 exact=[((n,tuple(m)),Fraction(v))for(n,m),v in entries]
 assert all(v>=0 for(n,m),v in exact if n not in('q1','q2'))
 D=lcm(*(v.denominator for _,v in exact))
 groups=defaultdict(list);expr=s.Integer(D)
 for(n,m),v in exact:
  coeff=int(v*D);groups[n].append((m,coeff));expr+=coeff*mon(m)*guard(n,q)
 assert s.Poly(s.expand(expr),*vars).is_zero
 ln=f'⟨3,B+4,C+D+9,D+9,E+4,F+6⟩'
 lines.append(f'''private theorem certificate_{sign} (B C D E F : ℤ)
    (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber {ln}) (ht : ShortTerminal {ln} 3)
    (hq : q2 {ln}={q}) : False := by
  have H := (shortTerminal_iff_polynomial _ hz 3).mp ht
''')
 pos=[];defs=[];idx=0
 for name,items in groups.items():
  if name in('q1','q2'):continue
  poly=leanpoly(items); nnp=nonnegproof(items)
  if name=='mono':
   lines.append(f'  let P{idx} : ℤ := {poly}\n  have hP{idx} : 0≤P{idx} := by\n    dsimp only [P{idx}]\n    clear * - B C D E F hB hC hD hE hF\n    exact {nnp}\n')
   pos.append(f'P{idx}');defs.append(f'P{idx}');idx+=1;continue
  lines.append(f'  let M{idx} : ℤ := {poly}\n  have hM{idx} : 0≤M{idx} := by\n    dsimp only [M{idx}]\n    clear * - B C D E F hB hC hD hE hF\n    exact {nnp}\n')
  if name.startswith('word:'):
   word='['+','.join('.'+i for i in name[5:].split(','))+']'
   lines.append(f'  let G{idx} : ℤ := heightPolynomial {ln} {word}\n  have hG{idx} : 0≤G{idx} := H {word} (by decide)\n')
  else:
   tri=name[9:];coords={'abd':('a','b','d'),'ace':('a','c','e')}[tri]
   xx=[{'a':'3','b':'(B+4)','c':'(C+D+9)','d':'(D+9)','e':'(E+4)'}[i]for i in coords]
   lines.append(f'  let G{idx} : ℤ := -7-PositiveChamber.triangleDefect '+' '.join(xx)+f'\n  have hG{idx} : 0≤G{idx} := by\n    have h := PositiveTriangleLower.chamber_{tri}_defect_bound _ hz\n    dsimp only [G{idx}]\n    linarith only [h]\n')
  lines.append(f'  have hP{idx} : 0≤M{idx}*G{idx} := mul_nonneg hM{idx} hG{idx}\n')
  pos.append(f'M{idx}*G{idx}');defs.extend((f'M{idx}',f'G{idx}'));idx+=1
 hp_proof='hP0'
 for j in range(1,idx):hp_proof=f'add_nonneg ({hp_proof}) hP{j}'
 lines.append(f'  let P : ℤ := '+ '+'.join(pos)+'\n  have hp : 0≤P := by\n    dsimp only [P]\n    exact '+hp_proof+'\n')
 μ=leanpoly(groups['q1']);ν=leanpoly(groups['q2'])
 lines.append(f'''  have hid : {D}+P+({μ})*(q1 {ln}-8)+({ν})*(q2 {ln}-{q if q>0 else '('+str(q)+')'})=0 := by
    dsimp only [P,{','.join(defs)},heightPolynomial,coordinateSum,applyWord,step,
      mu1,mu2,mu3,inv1,inv2,inv3,q1,q2,PositiveChamber.triangleDefect]
    clear * - B C D E F
    ring
  rw [hz.1.1,hq] at hid
  norm_num only [sub_self,mul_zero,add_zero] at hid
  have hpositive : 0 < {D}+P := add_pos_of_pos_of_nonneg (by decide) hp
  exact (ne_of_gt hpositive) hid
''')
lines.append("""/-- The sorted first-edge-three chamber cannot be terminal when the two
other indicated outer coefficients are both beyond the finite endpoint slices. -/
theorem a_three_sorted_large_impossible (z : Six) (hz : Chamber z) (ha : z.a=3)
    (hcd : z.d≤z.c) (hd : 9≤z.d) (hf : 6≤z.f)
    (ht : ShortTerminal z 3) : False := by
  obtain ⟨hb,hc,hdd,he⟩ := PositiveThreeTriangles.a_three_incident_bounds z hz ha
  let B := z.b-4
  let C := z.c-z.d
  let D := z.d-9
  let E := z.e-4
  let F := z.f-6
  have heq : z=⟨3,B+4,C+D+9,D+9,E+4,F+6⟩ := by
    ext <;> dsimp [B,C,D,E,F] <;> simp [ha] <;> omega
  have hw : Chamber ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩ := heq ▸ hz
  have htw : ShortTerminal ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩ 3 := heq ▸ ht
  have hB : 0≤B := by dsimp [B]; omega
  have hC : 0≤C := by dsimp [C]; omega
  have hD : 0≤D := by dsimp [D]; omega
  have hE : 0≤E := by dsimp [E]; omega
  have hF : 0≤F := by dsimp [F]; omega
  have hq : q2 ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩=4 ∨
      q2 ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩= -4 := by
    have hh := hw.1.2
    have hprod : (q2 ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩-4)*
        (q2 ⟨3,B+4,C+D+9,D+9,E+4,F+6⟩+4)=0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp hprod with h | h <;> [left;right] <;> omega
  rcases hq with hq | hq
  · exact certificate_plus B C D E F hB hC hD hE hF hw htw hq
  · exact certificate_minus B C D E F hB hC hD hE hF hw htw hq

/-- Only the already finite endpoint branches remain when the first edge is
three and the next two outer edges are sorted. -/
theorem a_three_sorted_small_boundary (z : Six) (hz : Chamber z) (ha : z.a=3)
    (hcd : z.d≤z.c) (ht : ShortTerminal z 3) : z.d≤8 ∨ z.f≤5 := by
  by_contra hn
  apply a_three_sorted_large_impossible z hz ha hcd (by omega) (by omega) ht

end SerreMarkov.PositiveSortedThreeLarge
""")
Path('SerreMarkov/PositiveSortedThreeLarge.lean').write_text('\n'.join(lines))
