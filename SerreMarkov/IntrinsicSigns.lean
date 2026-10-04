import SerreMarkov.IntrinsicFrame
import SerreMarkov.DegenerateAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SerreMarkov.IntrinsicSigns

open Matrix IntrinsicFrame
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

/-- The sum of the four principal three-by-three symmetric minors. -/
def thirdMinorSum (z : Six) : ℤ :=
  32 + 2*(z.a*z.b*z.d + z.a*z.c*z.e + z.b*z.c*z.f + z.d*z.e*z.f) -
    4*(z.a^2+z.b^2+z.c^2+z.d^2+z.e^2+z.f^2)

theorem trace_adjugate_symmetric (z : Six) :
    (symmetricForm z).adjugate.trace = thirdMinorSum z := by
  rw [← symmetricCofactors_eq_adjugate]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four, symmetricCofactors, thirdMinorSum]
  ring

/-- In an adapted frame only the point cofactor survives. -/
theorem adapted_symmetric_adjugate (α β γ a k : ℤ) :
    (AdaptedIntrinsic.euler α β γ a k + (AdaptedIntrinsic.euler α β γ a k)ᵀ).adjugate =
      oneEntryMatrix 3 3 (2*a*k^2) := by
  have hE : AdaptedIntrinsic.euler α β γ a k + (AdaptedIntrinsic.euler α β γ a k)ᵀ =
      !![2*α,β+γ,-k,0; β+γ,-2*a,0,0; -k,0,0,0; 0,0,0,0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [AdaptedIntrinsic.euler] <;> ring
  rw [hE]
  apply Matrix.ext
  intro i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^0 * ((-2*a)*(0)*(0) - (-2*a)*(0)*(0) - (0)*(0)*(0) + (0)*(0)*(0) + (0)*(0)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^1 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (-k)*(0)*(0) + (-k)*(0)*(0) + (0)*(0)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^2 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (-k)*(-2*a)*(0) + (-k)*(0)*(0) + (0)*(-2*a)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^3 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (-k)*(-2*a)*(0) + (-k)*(0)*(0) + (0)*(-2*a)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^1 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (0)*(-k)*(0) + (0)*(0)*(0) + (0)*(-k)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^2 * ((2*α)*(0)*(0) - (2*α)*(0)*(0) - (-k)*(-k)*(0) + (-k)*(0)*(0) + (0)*(-k)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^3 * ((2*α)*(0)*(0) - (2*α)*(0)*(0) - (-k)*(β+γ)*(0) + (-k)*(0)*(0) + (0)*(β+γ)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^4 * ((2*α)*(0)*(0) - (2*α)*(0)*(0) - (-k)*(β+γ)*(0) + (-k)*(0)*(-k) + (0)*(β+γ)*(0) - (0)*(0)*(-k)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^2 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (-2*a)*(-k)*(0) + (-2*a)*(0)*(0) + (0)*(-k)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^3 * ((2*α)*(0)*(0) - (2*α)*(0)*(0) - (β+γ)*(-k)*(0) + (β+γ)*(0)*(0) + (0)*(-k)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^4 * ((2*α)*(-2*a)*(0) - (2*α)*(0)*(0) - (β+γ)*(β+γ)*(0) + (β+γ)*(0)*(0) + (0)*(β+γ)*(0) - (0)*(-2*a)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^5 * ((2*α)*(-2*a)*(0) - (2*α)*(0)*(0) - (β+γ)*(β+γ)*(0) + (β+γ)*(0)*(-k) + (0)*(β+γ)*(0) - (0)*(-2*a)*(-k)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^3 * ((β+γ)*(0)*(0) - (β+γ)*(0)*(0) - (-2*a)*(-k)*(0) + (-2*a)*(0)*(0) + (0)*(-k)*(0) - (0)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^4 * ((2*α)*(0)*(0) - (2*α)*(0)*(0) - (β+γ)*(-k)*(0) + (β+γ)*(0)*(0) + (-k)*(-k)*(0) - (-k)*(0)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^5 * ((2*α)*(-2*a)*(0) - (2*α)*(0)*(0) - (β+γ)*(β+γ)*(0) + (β+γ)*(0)*(0) + (-k)*(β+γ)*(0) - (-k)*(-2*a)*(0)) = 0
    ring
  · rw [Matrix.det_fin_three]
    change (-1 : ℤ)^6 * ((2*α)*(-2*a)*(0) - (2*α)*(0)*(0) - (β+γ)*(β+γ)*(0) + (β+γ)*(0)*(-k) + (-k)*(β+γ)*(0) - (-k)*(-2*a)*(-k)) = 2*a*k^2
    ring

/-- Adjugates transform contravariantly under an integral unit congruence. -/
theorem adjugate_congruence (H B : Mat4) (hB : B.det=1 ∨ B.det=-1) :
    B * (Bᵀ*H*B).adjugate * Bᵀ = H.adjugate := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, ← Matrix.adjugate_transpose]
  calc
    _ = (B*B.adjugate)*H.adjugate*(B*B.adjugate)ᵀ := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = (B.det • (1 : Mat4))*H.adjugate*(B.det • (1 : Mat4))ᵀ := by
      rw [Matrix.mul_adjugate]
    _ = H.adjugate := by
      rcases hB with h | h <;> rw [h] <;> simp

/-- The intrinsic symmetric adjugate is the signed point tensor. -/
theorem frame_symmetric_adjugate {z : Six} (R : Frame z) :
    (symmetricForm z).adjugate = (2*A R*R.flag.k^2) •
      Matrix.vecMulVec R.flag.p R.flag.p := by
  have h := adjugate_congruence (symmetricForm z) (columns R) (frame_determinant R)
  rw [frame_symmetric_gram, adapted_symmetric_adjugate] at h
  rw [← h]
  apply Matrix.ext
  intro i j
  simp [columns, oneEntryMatrix, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.smul_apply, Matrix.vecMulVec_apply]
  ring

/-- The third symmetric minor sum has the sign of the intrinsic integer `A`. -/
theorem frame_trace_adjugate {z : Six} (R : Frame z) :
    (symmetricForm z).adjugate.trace =
      2*A R*R.flag.k^2 * ∑ i : Fin 4, (R.flag.p i)^2 := by
  rw [frame_symmetric_adjugate R]
  simp [Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Finset.mul_sum, pow_two]

theorem frame_point_ne_zero {z : Six} (R : Frame z) : R.flag.p ≠ 0 := by
  intro hp
  have h := R.u_rank
  rw [hp] at h
  simp [chiVec] at h

theorem frame_point_sum_squares_pos {z : Six} (R : Frame z) :
    0 < ∑ i : Fin 4, (R.flag.p i)^2 := by
  have hi : ∃ i : Fin 4, R.flag.p i ≠ 0 := by
    by_contra h
    push_neg at h
    apply frame_point_ne_zero R
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg (R.flag.p j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

private theorem frame_trace_factor_pos {z : Six} (R : Frame z) :
    0 < 2*R.flag.k^2*(∑ i : Fin 4, (R.flag.p i)^2) := by
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos R.flag.k_pos))
    (frame_point_sum_squares_pos R)

theorem frame_thirdMinorSum_pos_iff {z : Six} (R : Frame z) :
    0 < thirdMinorSum z ↔ 0 < A R := by
  rw [← trace_adjugate_symmetric, frame_trace_adjugate]
  have heq : 2*A R*R.flag.k^2 * (∑ i : Fin 4, (R.flag.p i)^2) =
      A R * (2*R.flag.k^2*(∑ i : Fin 4, (R.flag.p i)^2)) := by ring
  rw [heq]
  exact mul_pos_iff_of_pos_right (frame_trace_factor_pos R)

theorem frame_thirdMinorSum_neg_iff {z : Six} (R : Frame z) :
    thirdMinorSum z < 0 ↔ A R < 0 := by
  rw [← trace_adjugate_symmetric, frame_trace_adjugate]
  have heq : 2*A R*R.flag.k^2 * (∑ i : Fin 4, (R.flag.p i)^2) =
      A R * (2*R.flag.k^2*(∑ i : Fin 4, (R.flag.p i)^2)) := by ring
  rw [heq]
  constructor
  · intro h
    by_contra hn
    have hnonneg := mul_nonneg (le_of_not_gt hn) (frame_trace_factor_pos R).le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos h (frame_trace_factor_pos R)

theorem frame_thirdMinorSum_zero_iff {z : Six} (R : Frame z) :
    thirdMinorSum z = 0 ↔ A R = 0 := by
  rw [← trace_adjugate_symmetric, frame_trace_adjugate]
  have heq : 2*A R*R.flag.k^2 * (∑ i : Fin 4, (R.flag.p i)^2) =
      A R * (2*R.flag.k^2*(∑ i : Fin 4, (R.flag.p i)^2)) := by ring
  rw [heq, mul_eq_zero]
  simp [(frame_trace_factor_pos R).ne']

theorem frame_A_sign_independent {z : Six} (R Q : Frame z) :
    (0 < A R ↔ 0 < A Q) ∧ (A R < 0 ↔ A Q < 0) := by
  exact ⟨(frame_thirdMinorSum_pos_iff R).symm.trans (frame_thirdMinorSum_pos_iff Q),
    (frame_thirdMinorSum_neg_iff R).symm.trans (frame_thirdMinorSum_neg_iff Q)⟩

theorem solution_regular_thirdMinorSum_ne_zero (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) : thirdMinorSum z ≠ 0 := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  exact fun h => frame_A_ne_zero R hreg ((frame_thirdMinorSum_zero_iff R).mp h)

end SerreMarkov.IntrinsicSigns
