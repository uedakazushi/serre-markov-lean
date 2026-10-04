import SerreMarkov.PositiveEndpointBounds
import SerreMarkov.PositiveBoundedBase

/-! Exact candidate encoding for small opposite endpoints, with no presumed
bound on any original solution. The endpoint sum caps are proved separately. -/

namespace SerreMarkov.PositiveSmallEndpointCensus

open PositiveChamber PositiveShortWord PositiveEndpointBounds PositiveBounded

def cap (a f : ℕ) : ℕ := (endpointSumBound (a+3) (f+3)).toNat

def candidate (a f b : ℕ) (xs : List ℕ) (q : ℤ) : Six :=
  let c : ℤ := xs.getD 0 0+3
  let d : ℤ := xs.getD 1 0+3
  ⟨a+3,b+3,c,d,((a+3)*(f+3)+c*d-q)/(b+3),f+3⟩

local instance (z : Six) : Decidable (BalanceInequalities z) := by
  unfold BalanceInequalities
  infer_instance

/-- A finite Boolean certificate checks the desired total bound only when
all of the actual solution and two-letter terminal inequalities hold. -/
def caseCheck (C : ℕ) (z : Six) : Bool :=
  if decide (3 ≤ z.e ∧ z.b+z.c+z.d+z.e ≤ C ∧ BalanceInequalities z ∧
      q1 z=8 ∧ q2 z^2=16 ∧ 0 < IntrinsicSigns.thirdMinorSum z) then
    decide (z.a+z.b+z.c+z.d+z.e+z.f ≤ 37)
  else true

def blockCandidates (a f b : ℕ) : List Six :=
  (boundedTuples 2 (cap a f-12-b)).flatMap
    (fun xs => [candidate a f b xs 4,candidate a f b xs (-4)])

def blockCheck (a f b : ℕ) : Bool :=
  (blockCandidates a f b).all (caseCheck (cap a f))

theorem caseCheck_correct (C : ℕ) (z : Six) (h : caseCheck C z=true)
    (hz : Chamber z) (hcap : z.b+z.c+z.d+z.e ≤ C)
    (hbal : BalanceInequalities z) : z.a+z.b+z.c+z.d+z.e+z.f ≤ 37 := by
  have hp : 3 ≤ z.e ∧ z.b+z.c+z.d+z.e ≤ C ∧ BalanceInequalities z ∧
      q1 z=8 ∧ q2 z^2=16 ∧ 0 < IntrinsicSigns.thirdMinorSum z :=
    ⟨hz.2.2.2.2.2.2.1,hcap,hbal,hz.1.1,hz.1.2,hz.2.1⟩
  have hh : decide (z.a+z.b+z.c+z.d+z.e+z.f ≤ 37)=true := by
    simpa only [caseCheck,decide_eq_true hp,ite_true] using h
  exact of_decide_eq_true hh

theorem cap_cast (a f : ℕ) : (cap a f : ℤ)=endpointSumBound (a+3) (f+3) := by
  apply Int.toNat_of_nonneg
  unfold endpointSumBound
  split_ifs <;> norm_num

theorem cap_le_sixty_three (a f : ℕ) : cap a f ≤ 63 := by
  unfold cap endpointSumBound
  split_ifs <;> norm_num

end SerreMarkov.PositiveSmallEndpointCensus
