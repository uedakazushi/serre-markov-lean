#!/usr/bin/env python3
"""Generated closed kernel checks for a universal finite slice."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'SerreMarkov'
boxes={4:(101,68),5:(76,51),6:(62,41),7:(51,32),8:(41,25),9:(33,19),10:(25,14),11:(19,10)}
(root/'PositiveThreeFiveBase.lean').write_text('''import SerreMarkov.PositiveThreeFiveBounds

namespace SerreMarkov.PositiveThreeFive
open PositiveChamber PositiveThreeFourBounds PositiveShortWord NegativeDescent

def first : Six := ⟨3,5,5,5,10,7⟩
def second : Six := ⟨3,10,5,5,5,7⟩
def candidate (b c f : ℕ) (q : Bool) : Six :=
  ⟨3,b,c,5,(3*(f:ℤ)+5*(c:ℤ)-(if q then 4 else -4))/(b:ℤ),f⟩

def binaryConic (b c f q : ℤ) : ℤ :=
  (b^2+25-15*b)*c^2+(b^2+9-15*b)*f^2+
    (30+15*b^2-34*b-b^3)*c*f+
    (3*b-10)*q*c+(5*b-6)*q*f+q^2+b^2*(b^2-15*b+26)

theorem binaryConic_solution (b c e f : ℤ) (hz : isSolution ⟨3,b,c,5,e,f⟩) :
    binaryConic b c f (q2 ⟨3,b,c,5,e,f⟩)=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [binaryConic,q2]
  linear_combination b^2*h1

local instance (z : Six) : Decidable (isSolution z) := by unfold isSolution; infer_instance

def guardCheck (z : Six) : Bool :=
  oneStepCheck z && decide (l1 z ≤ l1 (applyWord z [.m2,.m1])) &&
    decide (l1 z ≤ l1 (applyWord z [.i1,.i2]))

def caseCheck (z : Six) : Bool :=
  if decide (3 ≤ z.c ∧ 3 ≤ z.e ∧ 3 ≤ z.f ∧ isSolution z) then
    if guardCheck z then decide (z=first ∨ z=second) else true
  else true

def encodedCheck (b c f : ℕ) (q : Bool) : Bool :=
  if decide (binaryConic b c f (if q then 4 else -4)=0) then
    caseCheck (candidate b c f q) else true

def blockCheck (b j : ℕ) : Bool :=
  (List.range 10).all (fun c => (List.range (fBound b+1)).all (fun f =>
    [false,true].all (fun q => encodedCheck b (10*j+c) f q)))

theorem blockCheck_correct (b j : ℕ) (h : blockCheck b j=true)
    (c f : ℕ) (hc : c<10) (hf : f<fBound b+1) (q : Bool)
    (hz : Chamber (candidate b (10*j+c) f q))
    (hone : guardCheck (candidate b (10*j+c) f q)=true)
    (hconic : binaryConic b (10*j+c) f (if q then 4 else -4)=0) :
    candidate b (10*j+c) f q=first ∨ candidate b (10*j+c) f q=second := by
  have h1 := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  have h2 := List.all_eq_true.mp h1 f (List.mem_range.mpr hf)
  have h3 := List.all_eq_true.mp h2 q (by cases q <;> simp)
  have hcase : caseCheck (candidate b (10*j+c) f q)=true := by simpa [encodedCheck,hconic] using h3
  have hp : 3 ≤ (candidate b (10*j+c) f q).c ∧
      3 ≤ (candidate b (10*j+c) f q).e ∧
      3 ≤ (candidate b (10*j+c) f q).f ∧ isSolution (candidate b (10*j+c) f q) :=
    ⟨hz.2.2.2.2.1,hz.2.2.2.2.2.2.1,hz.2.2.2.2.2.2.2,hz.1⟩
  simpa [caseCheck,hp,hone] using hcase

theorem shortTerminal_guardCheck (z : Six) (ht : ShortTerminal z 2) : guardCheck z=true := by
  have hone : oneStepCheck z=true := by
    apply List.all_eq_true.mpr
    intro g hg
    apply decide_eq_true
    have hm : [g] ∈ braidWords 2 :=
      (mem_braidWords_iff 2 [g]).mpr ⟨by simp,by simpa using hg⟩
    simpa only [applyWord] using ht [g] hm
  have hM := ht [.m2,.m1] (by decide +kernel)
  have hI := ht [.i1,.i2] (by decide +kernel)
  simp [guardCheck,hone,hM,hI]

end SerreMarkov.PositiveThreeFive
''')
for b,(cb,fb)in boxes.items():
 checks='\n'.join(f'theorem checked_{b}_{j} : blockCheck {b} {j}=true := by decide +kernel'for j in range(cb//10+1))
 (root/f'PositiveThreeFivePart{b-4:02}.lean').write_text(f'''import SerreMarkov.PositiveThreeFiveBase
namespace SerreMarkov.PositiveThreeFive
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
{checks}
end SerreMarkov.PositiveThreeFive
''')
checks='\n'.join(f'import SerreMarkov.PositiveThreeFivePart{b-4:02}'for b in boxes)
checks+='''
namespace SerreMarkov.PositiveThreeFive
theorem all_blocks_checked (b j : ℕ) (hb : 4≤b) (hb' : b≤11)
    (hj : 10*j≤cBound b) : blockCheck b j=true := by
  interval_cases b
'''
for b,(cb,fb)in boxes.items():
 checks+=f'  · norm_num [cBound] at hj\n    have hjMax : j ≤ {cb//10} := by omega\n    interval_cases j\n'
 checks+=''.join(f'    · exact checked_{b}_{j}\n'for j in range(cb//10+1))
checks+='end SerreMarkov.PositiveThreeFive\n'
(root/'PositiveThreeFiveChecks.lean').write_text(checks)
