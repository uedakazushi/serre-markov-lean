import SerreMarkov.PositiveThreeSixBounds

namespace SerreMarkov.PositiveThreeSix
open PositiveChamber PositiveThreeFourBounds PositiveShortWord NegativeDescent

def first : Six := ⟨3,7,6,6,7,3⟩
def second : Six := ⟨3,7,6,6,7,3⟩
def candidate (b c f : ℕ) (q : Bool) : Six :=
  ⟨3,b,c,6,(3*(f:ℤ)+6*(c:ℤ)-(if q then 4 else -4))/(b:ℤ),f⟩

def binaryConic (b c f q : ℤ) : ℤ :=
  (b^2+36-18*b)*c^2+(b^2+9-18*b)*f^2+
    (36+18*b^2-45*b-b^3)*c*f+
    (3*b-12)*q*c+(6*b-6)*q*f+q^2+b^2*(b^2-18*b+37)

theorem binaryConic_solution (b c e f : ℤ) (hz : isSolution ⟨3,b,c,6,e,f⟩) :
    binaryConic b c f (q2 ⟨3,b,c,6,e,f⟩)=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [binaryConic,q2]
  linear_combination b^2*h1

local instance (z : Six) : Decidable (isSolution z) := by unfold isSolution; infer_instance

def guardCheck (z : Six) : Bool :=
  oneStepCheck z && decide (l1 z ≤ l1 (applyWord z [.m2,.m1])) &&
    decide (l1 z ≤ l1 (applyWord z [.i1,.i2]))

def caseCheck (z : Six) : Bool :=
  if decide (3 ≤ z.c ∧ 3 ≤ z.e ∧ 3 ≤ z.f ∧ isSolution z ∧ 0 < IntrinsicSigns.thirdMinorSum z) then
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
      3 ≤ (candidate b (10*j+c) f q).f ∧ isSolution (candidate b (10*j+c) f q) ∧ 0 < IntrinsicSigns.thirdMinorSum (candidate b (10*j+c) f q) :=
    ⟨hz.2.2.2.2.1,hz.2.2.2.2.2.2.1,hz.2.2.2.2.2.2.2,hz.1,hz.2.1⟩
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

end SerreMarkov.PositiveThreeSix
