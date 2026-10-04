import SerreMarkov.Matrix
import SerreMarkov.Arithmetic
import Mathlib.LinearAlgebra.Matrix.Block

namespace SerreMarkov

open Matrix

/-- Adapted Euler pairing for the family with total parameter `m`. -/
def adaptedGram (m y : ℤ) : Mat4 :=
  !![1 + m*y, y, 0, 1;
     m, 1, 1, 0;
     -m, -1, 0, 0;
     -1, 0, 0, 0]

/-- Integral change of basis to the adapted pairing. -/
def adaptedBasis (y : ℤ) : Mat4 :=
  !![-y, -1, 1, 0;
     1, 0, 0, -1;
     0, 0, 0, 1;
     0, 0, 1, 0]

def adaptedBasisInverse (y : ℤ) : Mat4 :=
  !![0, 1, 1, 0;
     -1, -y, -y, 1;
     0, 0, 0, 1;
     0, 0, 1, 0]

theorem adaptedBasis_mul_inverse (y : ℤ) :
    adaptedBasis y * adaptedBasisInverse y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedBasis, adaptedBasisInverse, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem adaptedBasisInverse_det (y : ℤ) : (adaptedBasisInverse y).det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [adaptedBasisInverse, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_four, Fin.succAbove, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem adaptedBasis_det (y : ℤ) : (adaptedBasis y).det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [adaptedBasis, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_four, Fin.succAbove, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem adaptedBasis_congruence (m y : ℤ) :
    (adaptedBasis y)ᵀ * gram (family (m-y) y) * adaptedBasis y =
      adaptedGram m y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedBasis, adaptedGram, gram, family, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- An integral certificate when the two divisibility witnesses are supplied.
`g` witnesses `(y-y'-2*t)/m`, while `k` witnesses `t*(t-y)/m`. -/
def adaptedIsometry (m t g k : ℤ) : Mat4 :=
  !![1, 0, 0, 0;
     -t, 1, 0, 0;
     t + m*g + k, g, 1, 0;
     0, k + g*t, t, 1]

theorem adaptedIsometry_congruence (m y t g k : ℤ)
    (hk : t * (t-y) = m*k) :
    (adaptedIsometry m t g k)ᵀ * adaptedGram m y * adaptedIsometry m t g k =
      adaptedGram m (y - 2*t - m*g) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedIsometry, adaptedGram, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    nlinarith [hk]

/-- The certificate preserves an integral basis. -/
theorem adaptedIsometry_det (m t g k : ℤ) :
    (adaptedIsometry m t g k).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [adaptedIsometry, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_four, Fin.succAbove, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

/-- Constructive sufficiency of the simultaneous congruences for the adapted
Euler lattices. Necessity of this criterion is not assumed here. -/
theorem adapted_isometry_of_divisibility (m y y' : ℤ)
    (h : ∃ t : ℤ, m ∣ y - y' - 2*t ∧ m ∣ t*(t-y)) :
    ∃ T : Mat4, T.det = 1 ∧ Tᵀ * adaptedGram m y * T = adaptedGram m y' := by
  rcases h with ⟨t, ⟨g, hg⟩, ⟨k, hk⟩⟩
  have htarget : y' = y - 2*t - m*g := by linarith
  refine ⟨adaptedIsometry m t g k, adaptedIsometry_det m t g k, ?_⟩
  rw [htarget]
  exact adaptedIsometry_congruence m y t g k hk

/-- The same sufficient congruence criterion for the original Euler matrices,
with an explicitly constructed integral, determinant-one isometry. -/
theorem family_isometry_of_divisibility (m y y' : ℤ)
    (h : ∃ t : ℤ, m ∣ y - y' - 2*t ∧ m ∣ t*(t-y)) :
    ∃ B : Mat4, B.det = 1 ∧
      Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y') := by
  obtain ⟨T, hdet, hcong⟩ := adapted_isometry_of_divisibility m y y' h
  let B := adaptedBasis y * T * adaptedBasisInverse y'
  refine ⟨B, ?_, ?_⟩
  · simp [B, Matrix.det_mul, adaptedBasis_det, adaptedBasisInverse_det, hdet]
  · calc
      Bᵀ * gram (family (m-y) y) * B =
          (adaptedBasisInverse y')ᵀ *
            (Tᵀ * ((adaptedBasis y)ᵀ * gram (family (m-y) y) * adaptedBasis y) * T) *
            adaptedBasisInverse y' := by
        simp only [B, Matrix.transpose_mul]
        noncomm_ring
      _ = (adaptedBasisInverse y')ᵀ * adaptedGram m y' * adaptedBasisInverse y' := by
        rw [adaptedBasis_congruence, hcong]
      _ = gram (family (m-y') y') := by
        rw [← adaptedBasis_congruence m y']
        calc
          (adaptedBasisInverse y')ᵀ * ((adaptedBasis y')ᵀ *
              gram (family (m-y') y') * adaptedBasis y') * adaptedBasisInverse y' =
              (adaptedBasis y' * adaptedBasisInverse y')ᵀ *
              gram (family (m-y') y') * (adaptedBasis y' * adaptedBasisInverse y') := by
            rw [Matrix.transpose_mul]
            noncomm_ring
          _ = gram (family (m-y') y') := by
            rw [adaptedBasis_mul_inverse]
            simp

theorem family_isometry_of_odd_square (m : ℕ) (hm : Odd m) (y y' : ℤ)
    (hs : (y' : ZMod m)^2 = (y : ZMod m)^2) :
    ∃ B : Mat4, B.det = 1 ∧
      Bᵀ * gram (family ((m : ℤ)-y) y) * B =
        gram (family ((m : ℤ)-y') y') := by
  exact family_isometry_of_divisibility m y y'
    (integer_congruences_of_odd_square m hm y y' hs)

end SerreMarkov
