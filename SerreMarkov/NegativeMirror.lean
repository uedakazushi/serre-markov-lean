import SerreMarkov.IntrinsicFrame
import Mathlib.Tactic.LinearCombination

/-!
# The algebra behind negative mirrors

A rank-zero exceptional vector forces `A=-1`. This conclusion is conditional
on existence of that vector. The real mirror equations and height bound below
are polynomial consequences of two norm equations. They do not assert that
all mirrors arise from integral roots, chamber freeness, or existence of a
vertical mirror.
-/

namespace SerreMarkov.NegativeMirror

open IntrinsicFrame

/-- A rank-zero exceptional vector forces the unimodular degree case. -/
theorem rank_zero_exceptional_forces_A_neg_one {z : Six} (R : Frame z) (e : IntVec4)
    (he : chiVec z e e = 1) (hr : chiVec z e R.flag.p = 0) :
    A R = -1 ∧ (chiVec z e R.flag.l = 1 ∨ chiVec z e R.flag.l = -1) := by
  have h := frame_symmetric_rank_kernel R e e hr hr
  rw [symmetric_pairing, he] at h
  have hu : (-A R) * (chiVec z e R.flag.l)^2 = 1 := by nlinarith [h]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hu with ⟨hA, hd⟩ | ⟨hA, hd⟩
  · refine ⟨by linarith, ?_⟩
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simpa using hd
  · have hn := sq_nonneg (chiVec z e R.flag.l)
    linarith

/-- The quadratic norm in adapted coordinates. -/
def normQ (α B D k r d z : ℝ) : ℝ := α*r^2+B*r*d+D*d^2-k*r*z

/-- Its symmetric polar pairing, with no factor of one-half. -/
def polarH (α B D k r d z R E Z : ℝ) : ℝ :=
  2*α*r*R+B*(r*E+R*d)+2*D*d*E-k*(r*Z+R*z)

/-- The mirror identity depends only on the two displayed norm equations. -/
theorem mirror_polynomial_certificate (α B D k r d z R E Z : ℝ)
    (hx : normQ α B D k r d z = -1) (he : normQ α B D k R E Z = 1) :
    r*R*polarH α B D k r d z R E Z = r^2-R^2-D*(r*E-R*d)^2 := by
  unfold normQ polarH at *
  linear_combination R^2*hx + r^2*he

/-- Squaring the upper-half-plane height removes the square root. -/
theorem mirror_height_squared (D r : ℝ) (hD : 0 < D) :
    (1/(Real.sqrt D*r))^2 = 1/(D*r^2) := by
  rw [div_pow, mul_pow, Real.sq_sqrt hD.le]
  norm_num

private theorem circle_difference (D r d R E : ℝ) (hD : 0 < D)
    (hr : r ≠ 0) (hR : R ≠ 0) :
    (d/r-E/R)^2+(1/(Real.sqrt D*r))^2-1/(D*R^2) =
      (D*(r*E-R*d)^2+R^2-r^2)/(D*r^2*R^2) := by
  rw [mirror_height_squared D r hD]
  field_simp [hD.ne', hr, hR]
  ring

/-- A nonvertical mirror is exactly its explicitly specified Euclidean circle. -/
theorem mirror_zero_iff_circle (α B D k r d z R E Z : ℝ)
    (hx : normQ α B D k r d z = -1) (he : normQ α B D k R E Z = 1)
    (hr : 0 < r) (hR : R ≠ 0) (hD : 0 < D) :
    polarH α B D k r d z R E Z = 0 ↔
      (d/r-E/R)^2+(1/(Real.sqrt D*r))^2 = 1/(D*R^2) := by
  have hc : ((d/r-E/R)^2+(1/(Real.sqrt D*r))^2 = 1/(D*R^2)) ↔
      D*(r*E-R*d)^2+R^2-r^2 = 0 := by
    rw [← sub_eq_zero, circle_difference D r d R E hD hr.ne' hR, div_eq_zero_iff]
    simp [hD.ne', hr.ne', hR]
  rw [hc]
  have hp := mirror_polynomial_certificate α B D k r d z R E Z hx he
  constructor
  · intro h
    rw [h, mul_zero] at hp
    linarith
  · intro h
    have hh : (r*R)*polarH α B D k r d z R E Z = 0 := by
      rw [hp]
      linarith
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hr.ne' hR)

/-- Integral nonzero root rank bounds the square of the circle height. -/
theorem integral_mirror_height_squared_le (α B D k r d z : ℝ) (R : ℤ) (E Z : ℝ)
    (hx : normQ α B D k r d z = -1) (he : normQ α B D k (R:ℝ) E Z = 1)
    (hm : polarH α B D k r d z (R:ℝ) E Z = 0)
    (hr : 0 < r) (hR : R ≠ 0) (hD : 0 < D) :
    (1/(Real.sqrt D*r))^2 ≤ 1/D := by
  have hR2 : (1:ℤ) ≤ R^2 := by
    have hn := sq_nonneg R
    have hne := pow_ne_zero 2 hR
    omega
  have hR2r : (1:ℝ) ≤ (R:ℝ)^2 := by exact_mod_cast hR2
  have hp := mirror_polynomial_certificate α B D k r d z (R:ℝ) E Z hx he
  rw [hm, mul_zero] at hp
  have hd := mul_nonneg hD.le (sq_nonneg (r*E-(R:ℝ)*d))
  have hr2 : (1:ℝ) ≤ r^2 := by nlinarith only [hp, hd, hR2r]
  rw [mirror_height_squared D r hD]
  apply (div_le_div_iff₀ (mul_pos hD (sq_pos_of_pos hr)) hD).mpr
  have hmul := mul_nonneg hD.le (sub_nonneg.mpr hr2)
  nlinarith only [hmul]

end SerreMarkov.NegativeMirror
