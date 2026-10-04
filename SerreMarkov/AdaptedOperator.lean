import SerreMarkov.Isometry
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SerreMarkov

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply

/-- The shifted Serre operator in the adapted integral basis. -/
def adaptedN (m y : ℤ) : Mat4 :=
  !![0, 0, 0, 0;
     m, 0, 0, 0;
     y, 2, 0, 0;
     m*y + 2, m+y, -m, 0]

def adaptedCube (m : ℤ) : Mat4 :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     -2*m^2, 0, 0, 0]

theorem adaptedGram_det (m y : ℤ) : (adaptedGram m y).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [adaptedGram, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_four, Fin.succAbove]

theorem adaptedGram_mul_N (m y : ℤ) :
    adaptedGram m y * adaptedN m y = adaptedGram m y + (adaptedGram m y)ᵀ := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedGram, adaptedN, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem adaptedN_cube (m y : ℤ) : adaptedN m y ^ 3 = adaptedCube m := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedN, adaptedCube, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- Isometries intertwine the shifted Serre operators, with no chosen inverse. -/
theorem adaptedN_intertwine_totals (m m' y y' : ℤ) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * adaptedGram m y * B = adaptedGram m' y') :
    B * adaptedN m' y' = adaptedN m y * B := by
  have hu : IsUnit (Bᵀ * adaptedGram m y) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_mul, Matrix.det_transpose, adaptedGram_det, mul_one]
    rcases hdet with h | h <;> rw [h] <;> simp
  apply hu.mul_left_cancel
  calc
    (Bᵀ * adaptedGram m y) * (B * adaptedN m' y') =
        (Bᵀ * adaptedGram m y * B) * adaptedN m' y' := by simp [Matrix.mul_assoc]
    _ = adaptedGram m' y' * adaptedN m' y' := by rw [hcong]
    _ = adaptedGram m' y' + (adaptedGram m' y')ᵀ := adaptedGram_mul_N m' y'
    _ = Bᵀ * (adaptedGram m y + (adaptedGram m y)ᵀ) * B := by
      rw [← hcong]
      simp [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = (Bᵀ * adaptedGram m y) * (adaptedN m y * B) := by
      rw [← adaptedGram_mul_N]
      simp [Matrix.mul_assoc]

theorem adaptedN_intertwine (m y y' : ℤ) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * adaptedGram m y * B = adaptedGram m y') :
    B * adaptedN m y' = adaptedN m y * B :=
  adaptedN_intertwine_totals m m y y' B hdet hcong

/-- Transport an integral family isometry to the adapted bases. -/
theorem family_isometry_to_adapted (m m' y y' : ℤ) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m'-y') y')) :
    ∃ T : Mat4, (T.det = 1 ∨ T.det = -1) ∧
      Tᵀ * adaptedGram m y * T = adaptedGram m' y' := by
  let T := adaptedBasisInverse y * B * adaptedBasis y'
  have hTdet : T.det = B.det := by
    simp [T, Matrix.det_mul, adaptedBasisInverse_det, adaptedBasis_det]
  have hTcong : Tᵀ * adaptedGram m y * T = adaptedGram m' y' := by
    calc
      Tᵀ * adaptedGram m y * T =
        (adaptedBasis y')ᵀ * Bᵀ *
          ((adaptedBasisInverse y)ᵀ * adaptedGram m y * adaptedBasisInverse y) *
          B * adaptedBasis y' := by
        simp only [T, Matrix.transpose_mul]
        noncomm_ring
      _ = (adaptedBasis y')ᵀ * Bᵀ * gram (family (m-y) y) * B * adaptedBasis y' := by
        rw [← adaptedBasis_congruence m y]
        have hmid : (adaptedBasisInverse y)ᵀ *
            ((adaptedBasis y)ᵀ * gram (family (m-y) y) * adaptedBasis y) *
            adaptedBasisInverse y = gram (family (m-y) y) := by
          calc
            _ = (adaptedBasis y * adaptedBasisInverse y)ᵀ *
                gram (family (m-y) y) * (adaptedBasis y * adaptedBasisInverse y) := by
                  rw [Matrix.transpose_mul]
                  noncomm_ring
            _ = gram (family (m-y) y) := by rw [adaptedBasis_mul_inverse]; simp
        rw [hmid]
      _ = adaptedGram m' y' := by
        calc
          _ = (adaptedBasis y')ᵀ *
              (Bᵀ * gram (family (m-y) y) * B) * adaptedBasis y' := by noncomm_ring
          _ = adaptedGram m' y' := by rw [hcong, adaptedBasis_congruence]
  exact ⟨T, hTdet ▸ hdet, hTcong⟩

end SerreMarkov
