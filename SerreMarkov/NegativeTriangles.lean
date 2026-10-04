import SerreMarkov.IntrinsicType
import SerreMarkov.MarkovDescent

/-! # Triangle inequalities on the negative side

Every principal three-dimensional symmetric minor is nonpositive. The resulting
Cayley inequalities imply strict Vieta descent inside each positive triangle;
this module does not assume a global local-descent or orbit-classification result.
-/

namespace SerreMarkov.NegativeTriangles

open Matrix IntrinsicSigns IntrinsicFrame
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- The Cayley defect of a triangle of Euler pairings. -/
def cayleyDefect (u v w : ℤ) : ℤ := u^2+v^2+w^2-u*v*w

/-- Negative solutions have nonpositive diagonal symmetric cofactors. -/
theorem negative_adjugate_diag_nonpos (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) (i : Fin 4) :
    (symmetricForm z).adjugate i i ≤ 0 := by
  have hreg : shiftedSerre z^3 ≠ 0 := by
    intro hzero
    have hs := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hzero
    linarith
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  have hA : A R < 0 := (frame_thirdMinorSum_neg_iff R).mp hneg
  rw [frame_symmetric_adjugate R]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have hc : 2*A R*R.flag.k^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg R.flag.k)
  simpa only [pow_two] using
    mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg (R.flag.p i))

/-- Equivalently, each of the four principal three-by-three minors is nonpositive. -/
theorem negative_principal_three_minor_nonpos (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) (i : Fin 4) :
    ((symmetricForm z).submatrix i.succAbove i.succAbove).det ≤ 0 := by
  have h := negative_adjugate_diag_nonpos z hz hneg i
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have hs : (-1 : ℤ)^(i.val+i.val) = 1 := by
    rw [← Nat.two_mul, pow_mul]
    norm_num
  simpa only [hs, one_mul] using h

/-- The four triangle defects are all at least four on the negative side. -/
theorem negative_triangle_inequalities (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) :
    4 ≤ cayleyDefect z.a z.b z.d ∧
    4 ≤ cayleyDefect z.a z.c z.e ∧
    4 ≤ cayleyDefect z.b z.c z.f ∧
    4 ≤ cayleyDefect z.d z.e z.f := by
  have h0 := negative_adjugate_diag_nonpos z hz hneg 0
  have h1 := negative_adjugate_diag_nonpos z hz hneg 1
  have h2 := negative_adjugate_diag_nonpos z hz hneg 2
  have h3 := negative_adjugate_diag_nonpos z hz hneg 3
  rw [← symmetricCofactors_eq_adjugate] at h0 h1 h2 h3
  change -2*z.d^2+2*z.d*z.e*z.f-2*z.e^2-2*z.f^2+8 ≤ 0 at h0
  change -2*z.b^2+2*z.b*z.c*z.f-2*z.c^2-2*z.f^2+8 ≤ 0 at h1
  change -2*z.a^2+2*z.a*z.c*z.e-2*z.c^2-2*z.e^2+8 ≤ 0 at h2
  change -2*z.a^2+2*z.a*z.b*z.d-2*z.b^2-2*z.d^2+8 ≤ 0 at h3
  unfold cayleyDefect
  constructor
  · nlinarith [h3]
  constructor
  · nlinarith [h2]
  constructor
  · nlinarith [h1]
  · nlinarith [h0]

/-- The sorted Cayley inequality already forces the largest edge above half
of the product of the other two edges. Equality to four is unnecessary. -/
theorem cayley_sorted_product_lt_twice (u v w : ℤ)
    (hu : 3 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : u*v < 2*w := by
  unfold cayleyDefect at hc
  by_contra hn
  have hn' : 2*w ≤ u*v := le_of_not_gt hn
  have hsquares : u^2 ≤ v^2 := by
    nlinarith [mul_nonneg (by omega : 0 ≤ v-u) (by omega : 0 ≤ v+u)]
  have hlarge : 0 ≤ (u-3)*v^2 := mul_nonneg (by omega) (sq_nonneg v)
  have hfactor : (w-v)*(w+v-u*v) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) (by nlinarith)
  nlinarith [hsquares, hlarge, hfactor]

/-- Strict descent of a largest edge for every sorted positive Cayley triangle. -/
theorem cayley_sorted_abs_descent (u v w : ℤ)
    (hu : 3 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hc : 4 ≤ cayleyDefect u v w) : |u*v-w| < w := by
  have hupper := cayley_sorted_product_lt_twice u v w hu huv hvw hc
  have hproduct : 0 < u*v := mul_pos (by omega) (by omega)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Either ordering of the two smaller edges gives the same strict descent. -/
theorem cayley_positive_abs_descent (u v w : ℤ)
    (hu : 3 ≤ u) (hv : 3 ≤ v) (hw : 3 ≤ w)
    (hmax : u ≤ w ∧ v ≤ w) (hc : 4 ≤ cayleyDefect u v w) :
    |u*v-w| < w := by
  rcases le_total u v with huv | hvu
  · exact cayley_sorted_abs_descent u v w hu huv hmax.2 hc
  · have hc' : 4 ≤ cayleyDefect v u w := by simpa [cayleyDefect, mul_comm, add_comm] using hc
    simpa only [mul_comm v u] using
      cayley_sorted_abs_descent v u w hv hvu hmax.1 hc'


/-- Passing to absolute values preserves the triangle defect when its product
is nonnegative. -/
theorem cayleyDefect_abs_of_product_nonneg (u v w : ℤ) (hprod : 0 ≤ u*v*w) :
    cayleyDefect |u| |v| |w| = cayleyDefect u v w := by
  simp only [cayleyDefect, sq_abs, ← abs_mul, abs_of_nonneg hprod]

/-- The strict largest-edge reduction is unchanged by triangle sign switches. -/
theorem cayley_signed_abs_descent (u v w : ℤ)
    (hu : 3 ≤ |u|) (hv : 3 ≤ |v|) (hw : 3 ≤ |w|)
    (hmax : |u| ≤ |w| ∧ |v| ≤ |w|) (hprod : 0 < u*v*w)
    (hc : 4 ≤ cayleyDefect u v w) : |u*v-w| < |w| := by
  have hcabs : 4 ≤ cayleyDefect |u| |v| |w| := by
    rw [cayleyDefect_abs_of_product_nonneg u v w hprod.le]
    exact hc
  have h := cayley_positive_abs_descent |u| |v| |w| hu hv hw hmax hcabs
  by_cases hwpos : 0 < w
  · have huvpos : 0 < u*v := by
      by_contra hn
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hwpos.le
      linarith
    simpa only [← abs_mul, abs_of_pos huvpos, abs_of_pos hwpos] using h
  · have hwneg : w < 0 := by
      have hn : w ≤ 0 := le_of_not_gt hwpos
      rw [abs_of_nonpos hn] at hw
      omega
    have huvneg : u*v < 0 := by
      by_contra hn
      have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hn) hwneg.le
      linarith
    rw [← abs_mul, abs_of_neg huvneg, abs_of_neg hwneg] at h
    have heq : -(u*v)- -w = -(u*v-w) := by ring
    rw [heq, abs_neg] at h
    simpa only [abs_of_neg hwneg] using h

/-- A natural-height form of the same strict reduction. -/
theorem cayley_signed_natAbs_descent (u v w : ℤ)
    (hu : 3 ≤ |u|) (hv : 3 ≤ |v|) (hw : 3 ≤ |w|)
    (hmax : |u| ≤ |w| ∧ |v| ≤ |w|) (hprod : 0 < u*v*w)
    (hc : 4 ≤ cayleyDefect u v w) : (u*v-w).natAbs < w.natAbs := by
  have h := cayley_signed_abs_descent u v w hu hv hw hmax hprod hc
  rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at h
  exact_mod_cast h

end SerreMarkov.NegativeTriangles
