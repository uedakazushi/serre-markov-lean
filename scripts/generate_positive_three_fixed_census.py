#!/usr/bin/env python3
"""Encode complete fixed d=6,7,8 slices for independent kernel verification."""
from pathlib import Path
import re,json,sys
base=Path(__file__).resolve().parent;root=base.parent/'SerreMarkov'
points={6:'⟨3,7,6,6,7,3⟩',7:'⟨3,7,4,7,8,8⟩',8:'⟨0,0,0,0,0,0⟩'}
for d in map(int,sys.argv[1:] or ('6','7','8')):
 name={6:'Six',7:'Seven',8:'Eight'}[d];word=name.lower();bounds=json.loads((base/f'positive_three_{word}_boxes.json').read_text());bounds={int(b):tuple(v)for b,v in bounds.items()}
 code=(base/'generate_positive_three_five_census.py').read_text()
 code=code.replace('PositiveThreeFive','PositiveThree'+name)
 code=re.sub(r'boxes=\{[^\n]*\}', 'boxes='+repr(bounds),code,count=1)
 code=code.replace('⟨3,5,5,5,10,7⟩',points[d]).replace('⟨3,10,5,5,5,7⟩',points[d])
 code=code.replace('⟨3,b,c,5,','⟨3,b,c,'+str(d)+',').replace('5*(c:ℤ)',str(d)+'*(c:ℤ)')
 code=code.replace('c,5,e,f','c,'+str(d)+',e,f').replace('b≤11','b≤'+str(3*d-4))
 formula=f'''def binaryConic (b c f q : ℤ) : ℤ :=
  (b^2+{d*d}-{3*d}*b)*c^2+(b^2+9-{3*d}*b)*f^2+
    ({6*d}+{3*d}*b^2-{9+d*d}*b-b^3)*c*f+
    (3*b-{2*d})*q*c+({d}*b-6)*q*f+q^2+b^2*(b^2-{3*d}*b+{1+d*d})

'''
 code=re.sub(r'def binaryConic .*?theorem binaryConic_solution',lambda _:formula+'theorem binaryConic_solution',code,flags=re.S,count=1)
 exec(compile(code,str(base/'generate_positive_three_fixed_census.py'),'exec'),{'__file__':str(base/'generate_positive_three_five_census.py')})
 module=root/f'PositiveThree{name}Base.lean';src=module.read_text()
 src=src.replace('3 ≤ z.f ∧ isSolution z)', '3 ≤ z.f ∧ isSolution z ∧ 0 < IntrinsicSigns.thirdMinorSum z)')
 term='(candidate b (10*j+c) f q)'
 src=src.replace(f'∧ isSolution {term} :=',f'∧ isSolution {term} ∧ 0 < IntrinsicSigns.thirdMinorSum {term} :=')
 src=src.replace('hz.2.2.2.2.2.2.2,hz.1⟩','hz.2.2.2.2.2.2.2,hz.1,hz.2.1⟩')
 module.write_text(src)
 core=(root/'PositiveThreeFiveCensusCore.lean').read_text()
 core=core.replace('PositiveThreeFive','PositiveThree'+name).replace('a_three_d_five','a_three_d_'+word)
 core=core.replace('b ≤ 11','b ≤ '+str(3*d-4)).replace('z.b.toNat ≤ 11','z.b.toNat ≤ '+str(3*d-4))
 core=core.replace('z.d=5','z.d='+str(d)).replace('z.c,5,z.e','z.c,'+str(d)+',z.e').replace('5*z.c',str(d)+'*z.c')
 (root/f'PositiveThree{name}CensusCore.lean').write_text(core)
 final=f'''import SerreMarkov.PositiveThree{name}Checks
import SerreMarkov.PositiveThree{name}CensusCore
import SerreMarkov.PositiveBoundedCensus

/-! Universal terminal classification in the fixed slice a=3,d={d}.
Bounds are derived from genuine short words; every candidate is checked by
the Lean kernel. No general upper bound on d is asserted here. -/
namespace SerreMarkov.PositiveThree{name}
open PositiveChamber PositiveShortWord NegativeDescent

'''
 if d in(6,7):
  height={6:32,7:37}[d]
  final+=f'''theorem a_three_d_{word}_terminal_unique (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d={d}) (ht : ShortTerminal z 2) : z={points[d]} := by
  obtain h|h := chamber_census all_blocks_checked z hz ha hd ht
  · exact h
  · exact h

theorem a_three_d_{word}_terminal_height (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d={d}) (ht : ShortTerminal z 2) : l1 z={height} := by
  rw [a_three_d_{word}_terminal_unique z hz ha hd ht]
  decide +kernel

theorem a_three_d_{word}_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d={d}) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  rw [a_three_d_{word}_terminal_unique z hz ha hd ht]
  decide +kernel
'''
 else:
  final+='''theorem a_three_d_eight_terminal_impossible (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=8) (ht : ShortTerminal z 2) : False := by
  obtain h|h := chamber_census all_blocks_checked z hz ha hd ht
  · rw [h] at ha; norm_num [first] at ha
  · rw [h] at ha; norm_num [second] at ha
'''
 final+=f'\nend SerreMarkov.PositiveThree{name}\n'
 (root/f'PositiveThree{name}Census.lean').write_text(final)
 print('generated',d,sum((cb+1)*(fb+1)*2 for cb,fb in bounds.values()),'valid encodings')
