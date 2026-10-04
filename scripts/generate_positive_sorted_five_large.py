"""Generate kernel proofs from independently verified exact rational identities."""
from pathlib import Path
from fractions import Fraction
from math import lcm
from collections import defaultdict
import json
import sympy as s

root=Path(__file__).resolve().parents[1]
var=s.symbols('B C D E F');B,C,D,E,F=var
z=(s.Integer(5),B+3,C+D+6,D+6,E+3,F+6)
names=('m1','i1','m2','i2','m3','i3')
def step(z,g):
 a,b,c,d,e,f=z
 return dict(m1=(a,a*b-d,a*c-e,b,c,f),i1=(a,d,e,a*d-b,a*e-c,f),m2=(a*d-b,a,c,d,d*e-f,e),i2=(b,b*d-a,c,d,f,d*f-e),m3=(a,f*b-c,b,f*d-e,d,f),i3=(a,c,f*c-b,e,f*e-d,f))[g]
def image(word):
 zz=z
 for g in word:zz=step(zz,g)
 return zz
def guard(name,q):
 a,b,c,d,e,f=z
 if name=='q1':return a*c*d*f-a*b*d-a*c*e-b*c*f-d*e*f+sum(t*t for t in z)-8
 if name=='q2':return a*f-b*e+c*d-q
 if name=='mono':return s.Integer(1)
 if name=='marker':return 32+2*(a*b*d+a*c*e+b*c*f+d*e*f)-4*sum(t*t for t in z)-1
 bits=name.split(':')
 word=bits[1].split(',')if bits[1]else[]
 zz=image(word)
 if bits[0]=='word':return sum(zz)-sum(z)
 if bits[0]=='coord':return zz[int(bits[2])]-3
 if bits[0]=='triangle':
  coords=dict(zip('abcdef',zz));u,v,w=(coords[c]for c in bits[2])
  return u*v*w-u*u-v*v-w*w-7
 raise ValueError(name)
def mon(m):return s.prod(v**i for v,i in zip(var,m))
def lm(m):return '*'.join(str(v)if i==1 else f'{v}^{i}'for v,i in zip(var,m)if i)or'1'
def numeral(n):return f'(Int.ofNat {n})'if n>=0 else f'(-(Int.ofNat {-n}))'
def lp(items):
 return '+'.join(numeral(n)if not any(m)else f'{numeral(n)}*{lm(m)}'for m,n in items if n)or'(0:ℤ)'
def addproof(proofs):
 out=proofs[0]
 for term in proofs[1:]:out=f'(add_nonneg {out} {term})'
 return out
def multiplierproof(items):
 proofs=[]
 for m,n in items:
  if not n:continue
  assert n>=0
  out=f'(Int.natCast_nonneg {n})'
  for v,i in zip(var,m):
   if i:out=f'(mul_nonneg {out} '+(f'h{v}'if i==1 else f'(pow_nonneg h{v} {i})')+')'
  proofs.append(out)
 return addproof(proofs)
def lw(word):return '['+','.join('.'+g for g in word)+']'

for tag,q in [('Minus',-4),('Plus',4)]:
 source=root/'scripts'/'certificates'/f'positive_sorted_five_large_{tag.lower()}.json'
 entries=[((name,tuple(m)),Fraction(v))for(name,m),v in json.loads(source.read_text())]
 assert all(v>=0 for(name,m),v in entries if name not in('q1','q2'))
 denominator=lcm(*(v.denominator for _,v in entries));groups=defaultdict(list)
 residual=s.Integer(denominator)
 for(name,m),v in entries:
  coefficient=int(v*denominator);groups[name].append((m,coefficient))
  residual+=coefficient*mon(m)*guard(name,q)
 assert s.Poly(s.expand(residual),*var).is_zero
 lines=[f'''import SerreMarkov.PositiveTriangleLower
import SerreMarkov.PositiveShortWord

/-! Exact degree-seven certificate for the sorted first-edge-five large chamber.
The certificate is an identity over the integers, using actual braid-word
chamber preservation and three-letter height inequalities. -/
namespace SerreMarkov.PositiveSortedFiveLarge{tag}
open PositiveChamber PositiveShortWord NegativeDescent
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem certificate (B C D E F : ℤ)
    (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩)
    (ht : ShortTerminal ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ 3)
    (hq : q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ = {q}) : False := by
  let z : Six := ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩
  change Chamber z at hz
  change ShortTerminal z 3 at ht
  change q2 z={q} at hq
  have H := (shortTerminal_iff_polynomial z hz 3).mp ht
  let k : ℤ := {numeral(denominator)}
  have hk : 0<k := by dsimp only [k]; decide
''']
 words={}
 for name in groups:
  if name.startswith(('coord:','triangle:')):
   bits=name.split(':');word=tuple(bits[1].split(','))if bits[1]else()
   if word not in words:
    i=len(words);words[word]=i
    lines.append(f'''  let W{i} : Six := applyWord z {lw(word)}
  have hW{i} : Chamber W{i} := by
    exact applyWord_preserves_chamber z hz {lw(word)} (by simp [IsBraid])
''')
 pos=[];pProof=[];clearNames=['H','ht','hB','hC','hD','hE','hF']+[f'hW{i}'for i in words.values()]
 definitions=['z','k']+[f'W{i}'for i in words.values()]
 for i,(name,items)in enumerate((name,items)for name,items in groups.items()if name not in('q1','q2')):
  lines.append(f'  let M{i} : ℤ := {lp(items)}\n  have hM{i} : 0≤M{i} := by dsimp only [M{i}]; exact {multiplierproof(items)}\n')
  clearNames.append(f'hM{i}')
  definitions.append(f'M{i}')
  if name=='mono':
   pos.append(f'M{i}');pProof.append(f'hM{i}');continue
  if name.startswith('word:'):
   word=tuple(name[5:].split(','))
   lines.append(f'  let G{i} : ℤ := heightPolynomial z {lw(word)}\n  have hG{i} : 0≤G{i} := H {lw(word)} (by decide)\n')
  elif name.startswith('coord:'):
   bits=name.split(':');word=tuple(bits[1].split(','))if bits[1]else();j=words[word]
   coord='abcdef'[int(bits[2])]
   access='hW'+str(j)+'.2.2'+['.1','.2.1','.2.2.1','.2.2.2.1','.2.2.2.2.1','.2.2.2.2.2'][int(bits[2])]
   lines.append(f'  let G{i} : ℤ := W{j}.{coord}-3\n  have hG{i} : 0≤G{i} := by\n    have h := {access}\n    dsimp only [G{i}]\n    exact sub_nonneg.mpr h\n')
  elif name.startswith('triangle:'):
   bits=name.split(':');word=tuple(bits[1].split(','))if bits[1]else();j=words[word];tri=bits[2]
   u,v,w=tri
   lines.append(f'''  let G{i} : ℤ := -7-triangleDefect W{j}.{u} W{j}.{v} W{j}.{w}
  have hG{i} : 0≤G{i} := by
    have h := PositiveTriangleLower.chamber_{tri}_defect_bound W{j} hW{j}
    dsimp only [G{i}]
    exact sub_nonneg.mpr h
''')
  elif name=='marker':
   lines.append(f'  let G{i} : ℤ := IntrinsicSigns.thirdMinorSum z-1\n  have hG{i} : 0≤G{i} := by have h := hz.2.1; dsimp only [G{i}]; omega\n')
  else:raise ValueError(name)
  lines.append(f'  have hP{i} : 0≤M{i}*G{i} := mul_nonneg hM{i} hG{i}\n')
  pos.append(f'M{i}*G{i}');pProof.append(f'hP{i}');definitions.append(f'G{i}')
  clearNames.extend((f'hG{i}',f'hP{i}'))
 lines.append('  let P : ℤ := '+'+'.join(pos)+f'\n  have hp : 0≤P := by dsimp only [P]; exact {addproof(pProof)}\n')
 lines.append('  clear '+' '.join(clearNames)+'\n')
 mu=lp(groups['q1']);nu=lp(groups['q2'])
 lines.append(f'''  have hid : k+P+({mu})*(q1 z-8)+({nu})*(q2 z-({q}))=0 := by
    dsimp only [P,{','.join(definitions)},heightPolynomial,coordinateSum,applyWord,step,
      mu1,mu2,mu3,inv1,inv2,inv3,q1,q2,triangleDefect,IntrinsicSigns.thirdMinorSum]
    clear * - B C D E F
    ring
  rw [hz.1.1,hq] at hid
  norm_num only [sub_self,mul_zero,add_zero] at hid
  have hpositive : 0<k+P := add_pos_of_pos_of_nonneg hk hp
  exact (ne_of_gt hpositive) hid

end SerreMarkov.PositiveSortedFiveLarge{tag}
''')
 (root/'SerreMarkov'/f'PositiveSortedFiveLarge{tag}.lean').write_text('\n'.join(lines))
 print(tag,'terms',len(entries),'groups',len(groups),'constant digits',len(str(denominator)),flush=True)

(root/'SerreMarkov'/'PositiveSortedFiveLarge.lean').write_text('''import SerreMarkov.PositiveSortedFiveLargeMinus
import SerreMarkov.PositiveSortedFiveLargePlus

/-! The strict sorted first-edge-five region has no positive terminal solution. -/
namespace SerreMarkov.PositiveSortedFiveLarge
open PositiveChamber PositiveShortWord NegativeDescent

theorem a_five_sorted_large_impossible (z : Six) (hz : Chamber z) (ha : z.a=5)
    (hcd : z.d≤z.c) (hd : 6≤z.d) (hf : 6≤z.f)
    (ht : ShortTerminal z 3) : False := by
  let B := z.b-3
  let C := z.c-z.d
  let D := z.d-6
  let E := z.e-3
  let F := z.f-6
  have heq : z=⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ := by
    ext <;> dsimp [B,C,D,E,F] <;> simp [ha] <;> omega
  have hw : Chamber ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ := heq ▸ hz
  have htw : ShortTerminal ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩ 3 := heq ▸ ht
  have hB : 0≤B := by dsimp [B]; linarith [hz.2.2.2.1]
  have hC : 0≤C := by dsimp [C]; omega
  have hD : 0≤D := by dsimp [D]; omega
  have hE : 0≤E := by dsimp [E]; linarith [hz.2.2.2.2.2.2.1]
  have hF : 0≤F := by dsimp [F]; omega
  have hq : q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩=4 ∨
      q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩= -4 := by
    have hh := hw.1.2
    have hprod : (q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩-4)*
        (q2 ⟨5,B+3,C+D+6,D+6,E+3,F+6⟩+4)=0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp hprod with h | h <;> [left;right] <;> omega
  rcases hq with hq | hq
  · exact PositiveSortedFiveLargePlus.certificate B C D E F hB hC hD hE hF hw htw hq
  · exact PositiveSortedFiveLargeMinus.certificate B C D E F hB hC hD hE hF hw htw hq

end SerreMarkov.PositiveSortedFiveLarge
''')
