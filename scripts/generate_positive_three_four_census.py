#!/usr/bin/env python3
"""Generate kernel checks; the Python process supplies no trusted evidence."""
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'SerreMarkov'
(root/'PositiveThreeFourBase.lean').write_text('''import SerreMarkov.PositiveThreeFourBounds
import SerreMarkov.PositiveShortWord

/-! Exhaustive candidate encoding for the slice a=3,d=4. -/
namespace SerreMarkov.PositiveThreeFour
open PositiveChamber PositiveThreeFourBounds NegativeDescent

def first : Six := ⟨3,8,7,4,7,8⟩
def extra : Six := ⟨3,8,18,4,29,52⟩

def candidate (b c f : ℕ) (q : Bool) : Six :=
  ⟨3,b,c,4,(3*(f:ℤ)+4*(c:ℤ)-(if q then 4 else -4))/(b:ℤ),f⟩

def binaryConic (b c f q : ℤ) : ℤ :=
  (b^2+16-12*b)*c^2+(b^2+9-12*b)*f^2+
    (24+12*b^2-25*b-b^3)*c*f+
    (3*b-8)*q*c+(4*b-6)*q*f+q^2+b^2*(b^2-12*b+17)

theorem binaryConic_solution (b c e f : ℤ) (hz : isSolution ⟨3,b,c,4,e,f⟩) :
    binaryConic b c f (q2 ⟨3,b,c,4,e,f⟩)=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [binaryConic,q2]
  linear_combination b^2*h1

local instance (z : Six) : Decidable (isSolution z) := by unfold isSolution; infer_instance

def caseCheck (z : Six) : Bool :=
  if decide (3 ≤ z.c ∧ 3 ≤ z.e ∧ 3 ≤ z.f ∧ isSolution z) then
    if oneStepCheck z then decide (z=first ∨ z=extra) else true
  else true

def encodedCheck (b c f : ℕ) (q : Bool) : Bool :=
  if decide (binaryConic b c f (if q then 4 else -4)=0) then
    caseCheck (candidate b c f q) else true

def blockCheck (b k j : ℕ) : Bool :=
  (List.range 15).all (fun c => (List.range 46).all (fun f =>
    [false,true].all (fun q => encodedCheck b (15*j+c) (46*k+f) q)))

theorem blockCheck_correct (b k j : ℕ) (h : blockCheck b k j=true)
    (c f : ℕ) (hc : c<15) (hf : f<46) (q : Bool)
    (hz : Chamber (candidate b (15*j+c) (46*k+f) q))
    (hone : oneStepCheck (candidate b (15*j+c) (46*k+f) q)=true)
    (hconic : binaryConic b (15*j+c) (46*k+f) (if q then 4 else -4)=0) :
    candidate b (15*j+c) (46*k+f) q=first ∨ candidate b (15*j+c) (46*k+f) q=extra := by
  have h1 := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  have h2 := List.all_eq_true.mp h1 f (List.mem_range.mpr hf)
  have h3 := List.all_eq_true.mp h2 q (by cases q <;> simp)
  have hcase : caseCheck (candidate b (15*j+c) (46*k+f) q)=true := by simpa [encodedCheck,hconic] using h3
  have hp : 3 ≤ (candidate b (15*j+c) (46*k+f) q).c ∧
      3 ≤ (candidate b (15*j+c) (46*k+f) q).e ∧
      3 ≤ (candidate b (15*j+c) (46*k+f) q).f ∧ isSolution (candidate b (15*j+c) (46*k+f) q) :=
    ⟨hz.2.2.2.2.1,hz.2.2.2.2.2.2.1,hz.2.2.2.2.2.2.2,hz.1⟩
  simpa [caseCheck,hp,hone] using hcase

end SerreMarkov.PositiveThreeFour
''')
for b in range(4,9):
 for k in range(4):
  n=(b-4)*4+k
  checks_for_block='\n'.join(f'theorem checked_{b}_{k}_{j} : blockCheck {b} {k} {j}=true := by decide +kernel' for j in range(11))
  (root/f'PositiveThreeFourPart{n:02}.lean').write_text(f'''import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

{checks_for_block}
end SerreMarkov.PositiveThreeFour
''')
checks='\n'.join(f'import SerreMarkov.PositiveThreeFourPart{i:02}' for i in range(20))
checks+='''
namespace SerreMarkov.PositiveThreeFour

theorem all_blocks_checked (b k j : ℕ) (hb : 4≤b) (hb' : b≤8) (hk : k<4) (hj : j<11) :
    blockCheck b k j=true := by
  interval_cases b <;> interval_cases k <;> interval_cases j
'''
checks+='\n'.join(f'  · exact checked_{b}_{k}_{j}'for b in range(4,9)for k in range(4)for j in range(11))
checks+='\nend SerreMarkov.PositiveThreeFour\n'
(root/'PositiveThreeFourChecks.lean').write_text(checks)
