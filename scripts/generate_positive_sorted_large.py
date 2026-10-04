"""Regenerate the four checked Lean modules from the bundled exact JSON data.

Run this script from any directory. It uses only the Python standard library and
the three positive_sorted_large_*.json files in scripts/certificates. Missing or
invalid certificate files are reported before any Lean output is written.
"""
from pathlib import Path
from fractions import Fraction
import json

ROOT=Path(__file__).resolve().parents[1]
CERTDIR=ROOT/'scripts'/'certificates'
VARS=('A','B','C','D','E','F');ZERO=(0,)*6
def decode(p):return {tuple(m):Fraction(co) for m,co in p}
def required_json(name):
 path=CERTDIR/name
 try:
  return json.loads(path.read_text())
 except FileNotFoundError:
  raise SystemExit(f'Required certificate JSON is missing: {path}') from None
 except json.JSONDecodeError as err:
  raise SystemExit(f'Invalid certificate JSON in {path}: {err}') from None

saved=required_json('positive_sorted_large_guard_metadata.json')
certificates={label:required_json('positive_sorted_large_'+label.lower()+'.json')
 for label in ('Minus','Plus')}
metadata=dict(base={n:decode(p) for n,p in saved['base'].items()},
 factors=saved['factors'],needed=set(saved['needed']),metadata=saved['metadata'])
needed=sorted(metadata['needed']);ids={name:i for i,name in enumerate(needed)}
ln='⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩'
args='A B C D E F'
params='(A B C D E F : ℤ)'
hyps='(hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)'
names=['m1','i1','m2','i2','m3','i3']
def word(w):return '['+','.join('.'+names[i] for i in w)+']'
def mono(m):return '*'.join(x if e==1 else f'{x}^{e}' for x,e in zip(VARS,m) if e) or '1'
def leanpoly(p):
 out=[]
 for m,co in sorted(p.items(),reverse=True):
  assert co.denominator==1 if isinstance(co,Fraction) else True
  co=int(co)
  if not co:continue
  term=str(abs(co)) if m==ZERO else f'{abs(co)}*{mono(m)}'
  out.append(('-' if co<0 else '+')+term)
 return ''.join(out).lstrip('+') or '0'
def nonnegative_poly(p):
 proofs=[]
 for m,co in sorted(p.items(),reverse=True):
  co=int(co)
  if not co:continue
  assert co>0
  proof=f'(Int.natCast_nonneg {co})'
  for name,e in zip(VARS,m):
   if not e:continue
   factor=f'h{name}' if e==1 else f'(pow_nonneg h{name} {e})'
   proof=f'(mul_nonneg {proof} {factor})'
  proofs.append(proof)
 if not proofs:return '(le_refl (0:ℤ))'
 ans=proofs[0]
 for proof in proofs[1:]:ans=f'(add_nonneg {ans} {proof})'
 return ans
def add_proofs(proofs):
 ans=proofs[0]
 for p in proofs[1:]:ans=f'(add_nonneg {ans} {p})'
 return ans
def mul_proofs(proofs):
 ans=proofs[0]
 for p in proofs[1:]:ans=f'(mul_nonneg {ans} {p})'
 return ans

# Base guards are modest polynomial identities, compiled before the two large
# final coefficient identities. Their semantic proofs use actual braid words.
prefix='''import SerreMarkov.PositiveSortedTerminal
import SerreMarkov.PositiveTriangleLower

/-! Nonnegative guards for the ordered large-edge terminal certificate. -/
namespace SerreMarkov.PositiveSortedLarge
open PositiveChamber PositiveShortWord PositiveSortedTerminal NegativeDescent
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem braid_word_chamber (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) : Chamber (applyWord z word) := by
  exact applyWord_preserves_chamber z hz word
    (fun g hg => braidMoves_isBraid (hw g hg))

theorem word_height_nonnegative (z : Six) (hz : Chamber z) (ht : AllTerminal z)
    (word : List Generator) (hw : ∀ g∈word, g∈braidMoves) :
    0≤heightPolynomial z word := by
  apply (shortTerminal_iff_polynomial z hz word.length).mp (ht word.length)
  exact (mem_braidWords_iff _ _).mpr ⟨le_refl _,hw⟩

theorem word_coordinates (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) : Coordinates (applyWord z word) :=
  (braid_word_chamber z hz word hw).2.2

theorem word_triangle_bounds (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) :
    triangleDefect (applyWord z word).a (applyWord z word).b (applyWord z word).d≤ -7 ∧
    triangleDefect (applyWord z word).a (applyWord z word).c (applyWord z word).e≤ -7 ∧
    triangleDefect (applyWord z word).b (applyWord z word).c (applyWord z word).f≤ -7 ∧
    triangleDefect (applyWord z word).d (applyWord z word).e (applyWord z word).f≤ -7 :=
  PositiveTriangleLower.chamber_all_triangle_bounds _ (braid_word_chamber z hz word hw)

theorem marker_nonnegative (z : Six) (hz : Chamber z) :
    0≤IntrinsicSigns.thirdMinorSum z-2 := by
  have h := hz.2.1
  dsimp [IntrinsicSigns.thirdMinorSum] at h ⊢
  omega

theorem normalized_nonnegative (n G R : ℤ) (hn : 0<n) (hR : 0≤R)
    (heq : R=n*G) : 0≤G := by
  have h : 0≤n*G := heq ▸ hR
  exact (mul_nonneg_iff_of_pos_left hn).mp h

'''
guards=[prefix,'set_option linter.unusedVariables false\n']
unfold='applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3'
for name in needed:
 i=ids[name];p=metadata['base'][name];info=metadata['metadata'][name]
 assert info['normalizer']==1
 guards.append(f'\ndef guard{i} {params} : ℤ := {leanpoly(p)}\n')
 guards.append(f'theorem guard{i}_nonnegative {params}\n    {hyps}\n    (hz : Chamber {ln}) (ht : AllTerminal {ln}) :\n    0≤guard{i} {args} := by\n')
 kind=info['kind'];w=word(info.get('word',()))
 if kind in ('var','newvar'):
  guards.append(f'  dsimp only [guard{i}]\n  positivity\n')
 else:
  if kind=='height':
   raw=f'heightPolynomial {ln} {w}'
   guards.append(f'  have hr : 0≤{raw} := word_height_nonnegative _ hz ht {w} (by decide +kernel)\n')
   more='heightPolynomial,coordinateSum,'+unfold
  elif kind=='coord':
   field='abcdef'[info['index']];raw=f'(applyWord {ln} {w}).{field}-3'
   proj='.2'*info['index']+'.1' if info['index']<5 else '.2'*5
   guards.append(f'  have hc := word_coordinates _ hz {w} (by decide +kernel)\n  have hr : 0≤{raw} := by linarith only [hc{proj}]\n')
   more=unfold
  elif kind=='tri':
   coords=[('a','b','d'),('a','c','e'),('b','c','f'),('d','e','f')][info['index']]
   raw='-7-triangleDefect '+' '.join(f'(applyWord {ln} {w}).{field}' for field in coords)
   proj='.2'*info['index']+'.1' if info['index']<3 else '.2'*3
   guards.append(f'  have hc := word_triangle_bounds _ hz {w} (by decide +kernel)\n  have hr : 0≤{raw} := by linarith only [hc{proj}]\n')
   more='triangleDefect,'+unfold
  elif kind=='marker':
   raw=f'IntrinsicSigns.thirdMinorSum {ln}-2'
   guards.append(f'  have hr : 0≤{raw} := marker_nonnegative _ hz\n')
   more='IntrinsicSigns.thirdMinorSum'
  else:raise ValueError(kind)
  guards.append(f'  have heq : guard{i} {args}={raw} := by\n    dsimp only [guard{i},{more}]\n    ring\n  rw [heq]\n  exact hr\n')
guards.append('\nend SerreMarkov.PositiveSortedLarge\n')
guardfile=ROOT/'SerreMarkov'/'PositiveSortedLargeGuards.lean'
if not guardfile.exists() or guardfile.read_text()!=''.join(guards):
 guardfile.write_text(''.join(guards))

for label,sign in [('Minus',-4),('Plus',4)]:
 certificate=certificates[label];den=int(certificate['scale'])
 groups={n:decode(p) for n,p in certificate['guards'].items()}
 mu=decode(certificate['mu']);nu=decode(certificate['nu'])
 lines=['import SerreMarkov.PositiveSortedLargeGuards\n\nnamespace SerreMarkov.PositiveSortedLarge\n',
  'open PositiveChamber PositiveShortWord PositiveSortedTerminal NegativeDescent\n',
  'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\n',
  f'\ntheorem certificate_{label.lower()} {params}\n    {hyps}\n    (hz : Chamber {ln}) (ht : AllTerminal {ln})\n    (hq : q2 {ln}={sign if sign>0 else "(-4)"}) : False := by\n']
 baseused=sorted({b for n in groups for b in metadata['factors'][n]})
 for base in baseused:
  i=ids[base]
  lines.append(f'  have hG{i} := guard{i}_nonnegative {args} hA hB hC hD hE hF hz ht\n')
 terms=[];defs=[]
 for j,(name,p) in enumerate(groups.items()):
  lines.append(f'  let M{j} : ℤ := {leanpoly(p)}\n  have hM{j} : 0≤M{j} := {nonnegative_poly(p)}\n')
  gs='*'.join(f'(guard{ids[b]} {args})' for b in metadata['factors'][name])
  gp=mul_proofs([f'hG{ids[b]}' for b in metadata['factors'][name]])
  lines.append(f'  let T{j} : ℤ := M{j}*({gs})\n  have hT{j} : 0≤T{j} := mul_nonneg hM{j} {gp}\n')
  terms.append(f'T{j}');defs.extend((f'T{j}',f'M{j}'))
 lines.append('  let P : ℤ := '+'+'.join(terms)+'\n  have hp : 0≤P := '+add_proofs([f'hT{j}' for j in range(len(terms))])+'\n')
 qsign='4' if sign>0 else '(-4)'
 lines.append(f'  have hid : {den}+P-({leanpoly(mu)})*(q1 {ln}-8)-({leanpoly(nu)})*(q2 {ln}-{qsign})=0 := by\n')
 lines.append('    dsimp only [P,'+','.join(defs)+','+','.join(f'guard{ids[b]}' for b in baseused)+',q1,q2]\n    clear * - A B C D E F\n    ring\n')
 lines.append(f'  have hzero : {den}+P=0 := by\n    simpa only [hz.1.1,hq,sub_self,mul_zero,sub_zero] using hid\n')
 lines.append(f'  have hpos : 0<{den}+P := add_pos_of_pos_of_nonneg (by norm_num) hp\n  exact (ne_of_gt hpos) hzero\n\nend SerreMarkov.PositiveSortedLarge\n')
 (ROOT/'SerreMarkov'/('PositiveSortedLarge'+label+'.lean')).write_text(''.join(lines))
 print(label,'groups',len(groups),'base',len(baseused),'mu',len(mu),'nu',len(nu),'scale digits',len(str(den)),flush=True)

main='''import SerreMarkov.PositiveSortedLargeMinus
import SerreMarkov.PositiveSortedLargePlus

/-! The first outer edge of every sorted terminal positive chamber is at most
five. This is proved from actual finite-word guards by exact integer identities.
-/
namespace SerreMarkov.PositiveSortedLarge
open PositiveChamber PositiveShortWord PositiveSortedTerminal

theorem sorted_first_ge_six_impossible (z : Six) (hz : Chamber z)
    (hs : SortedOuter z) (ht : AllTerminal z) (ha : 6≤z.a) : False := by
  let A := z.a-6
  let B := z.b-3
  let C := z.c-z.d
  let D := z.d-z.a
  let E := z.e-3
  let F := z.f-z.a
  have heq : z=⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := by
    ext <;> dsimp [A,B,C,D,E,F] <;> ring
  have hA : 0≤A := by dsimp [A]; omega
  have hB : 0≤B := by dsimp [B]; have h:=hz.2.2.2.1; omega
  have hC : 0≤C := by dsimp [C]; have h:=hs.2.2.2; omega
  have hD : 0≤D := by dsimp [D]; have h:=hs.2.1; omega
  have hE : 0≤E := by dsimp [E]; have h:=hz.2.2.2.2.2.2.1; omega
  have hF : 0≤F := by dsimp [F]; have h:=hs.2.2.1; omega
  have hw : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := heq ▸ hz
  have htw : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ := heq ▸ ht
  have hq : q2 ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩=4 ∨
      q2 ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hw.1.2)
  rcases hq with hq|hq
  · exact certificate_plus A B C D E F hA hB hC hD hE hF hw htw hq
  · exact certificate_minus A B C D E F hA hB hC hD hE hF hw htw hq

theorem sorted_first_edge_le_five (z : Six) (hz : Chamber z)
    (hs : SortedOuter z) (ht : AllTerminal z) : z.a≤5 := by
  by_contra hn
  exact sorted_first_ge_six_impossible z hz hs ht (by omega)

end SerreMarkov.PositiveSortedLarge
'''
(ROOT/'SerreMarkov'/'PositiveSortedLarge.lean').write_text(main)
