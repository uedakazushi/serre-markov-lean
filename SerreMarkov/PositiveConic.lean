import SerreMarkov.PositiveShortWord
import SerreMarkov.PositiveTriangleLower

/-! # A universal two-slack conic for positive terminal solutions

This exact polynomial certificate has positive quadratic coefficients in the
positive chamber and nonnegative slacks at actual two-step terminal points.
These statements alone do not assert a finite bound.
-/

namespace SerreMarkov.PositiveConic
open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 4000000

def adjacentDifference (z : Six) : ℤ := z.a*z.d-z.b

def triangleSize (z : Six) : ℤ :=
  z.b*adjacentDifference z-z.a^2-z.d^2

def firstSlack (z : Six) : ℤ := z.b*heightPolynomial z [.m2,.m1]
def secondSlack (z : Six) : ℤ := z.b*heightPolynomial z [.i1,.i2]

def firstOffset (z : Six) : ℤ :=
  z.b*adjacentDifference z*(z.a+1)-z.b^2-2*z.b*z.d

def secondOffset (z : Six) : ℤ :=
  z.b*adjacentDifference z*(z.d+1)-z.b^2-2*z.a*z.b

def conic (z : Six) : ℤ :=
  (z.d^2+triangleSize z)*(firstSlack z-firstOffset z)^2+
  (adjacentDifference z*triangleSize z+2*z.a*z.d)*
    (firstSlack z-firstOffset z)*(secondSlack z-secondOffset z)+
  (z.a^2+triangleSize z)*(secondSlack z-secondOffset z)^2-
  z.b^2*(adjacentDifference z)^2*(triangleSize z+4)^2

/-- The two actual word heights are linear in the last three coordinates
when the first triangle is held fixed. -/
theorem firstSlack_formula (z : Six) :
    firstSlack z=z.b*((z.a*z.d-z.b)*(z.a+z.c+1)-z.b-z.d*(z.e+2)) := by
  dsimp [firstSlack,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2]
  ring

theorem secondSlack_formula (z : Six) :
    secondSlack z=z.b*((z.a*z.d-z.b)*(z.d+z.f+1)-z.b-z.a*(z.e+2)) := by
  dsimp [secondSlack,heightPolynomial,coordinateSum,applyWord,step,inv1,inv2]
  ring

/-- This identity holds before either solution equation is imposed. -/
theorem conic_certificate (z : Six) :
    conic z=z.b^2*(adjacentDifference z)^2*
      (triangleSize z*(q1 z-8)+q2 z^2-16) := by
  rw [conic,firstSlack_formula,secondSlack_formula]
  dsimp [firstOffset,secondOffset,adjacentDifference,triangleSize,q1,q2]
  ring

theorem solution_conic (z : Six) (hz : isSolution z) : conic z=0 := by
  rw [conic_certificate,hz.1,hz.2]
  ring

/-- Every quadratic coefficient on the positive slack quadrant is positive. -/
theorem chamber_coefficient_bounds (z : Six) (hz : Chamber z) :
    3≤adjacentDifference z ∧ 7≤triangleSize z ∧
    0<z.d^2+triangleSize z ∧
    0<adjacentDifference z*triangleSize z+2*z.a*z.d ∧
    0<z.a^2+triangleSize z := by
  have hA : 3≤adjacentDifference z := by
    have hw := step_preserves_chamber .i1 True.intro z hz
    exact hw.2.2.2.2.2.1
  have hT := PositiveTriangleLower.chamber_abd_defect_bound z hz
  have hT' : 7≤triangleSize z := by
    dsimp [triangleSize,adjacentDifference,triangleDefect] at hT ⊢
    nlinarith only [hT]
  have ha : 0≤z.a := by have hh:=hz.2.2.1; omega
  have hd : 0≤z.d := by have hh:=hz.2.2.2.2.2.1; omega
  have hpos : 0<adjacentDifference z*triangleSize z := mul_pos (by omega) (by omega)
  have hprod := mul_nonneg ha hd
  exact ⟨hA,hT',by nlinarith [sq_nonneg z.d],by nlinarith,by nlinarith [sq_nonneg z.a]⟩

/-- The nonnegative slacks are genuine two-letter height comparisons. -/
theorem terminal_slacks_nonnegative (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 2) : 0≤firstSlack z ∧ 0≤secondSlack z := by
  have hp := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hb : 0≤z.b := by have hh:=hz.2.2.2.1; omega
  exact ⟨mul_nonneg hb (hp [.m2,.m1] (by decide +kernel)),
    mul_nonneg hb (hp [.i1,.i2] (by decide +kernel))⟩

end SerreMarkov.PositiveConic
