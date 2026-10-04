import SerreMarkov.Matrix

namespace SerreMarkov.AdaptedIntrinsic

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- General Euler form in the integral coordinates `(u,v,l,p)` of Section 5. -/
def euler (α β γ A κ : ℤ) : Mat4 :=
  !![α, β, 0, 1; γ, -A, 1, 0; -κ, -1, 0, 0; -1, 0, 0, 0]

def inverse (α β γ A κ : ℤ) : Mat4 :=
  !![0, 0, 0, -1; 0, 0, -1, κ; 0, 1, -A, A*κ+γ; 1, 0, β, α-β*κ]

def shifted (α β γ A κ : ℤ) : Mat4 :=
  !![0, 0, 0, 0; κ, 0, 0, 0; A*κ+β+γ, -2*A, 0, 0;
     2*α-β*κ, β+γ, -κ, 0]

theorem euler_inverse (α β γ A κ : ℤ) : euler α β γ A κ * inverse α β γ A κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euler, inverse, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem inverse_euler (α β γ A κ : ℤ) : inverse α β γ A κ * euler α β γ A κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euler, inverse, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem euler_det (α β γ A κ : ℤ) : (euler α β γ A κ).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [euler, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_four, Fin.succAbove]

theorem shifted_formula (α β γ A κ : ℤ) :
    inverse α β γ A κ * (euler α β γ A κ)ᵀ + 1 = shifted α β γ A κ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euler, inverse, shifted, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem shifted_cube (α β γ A κ : ℤ) :
    shifted α β γ A κ ^ 3 =
      !![0,0,0,0; 0,0,0,0; 0,0,0,0; 2*A*κ^2,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem shifted_fourth (α β γ A κ : ℤ) : shifted α β γ A κ ^ 4 = 0 := by
  change shifted α β γ A κ ^ (3+1) = 0
  rw [pow_succ, shifted_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted, Matrix.mul_apply, Fin.sum_univ_four]

theorem shifted_cube_zero_iff (α β γ A κ : ℤ) :
    shifted α β γ A κ ^ 3 = 0 ↔ A = 0 ∨ κ = 0 := by
  rw [shifted_cube]
  constructor
  · intro h
    have hh := congrFun (congrFun h 3) 0
    simpa using hh
  · intro h
    rcases h with h | h <;> subst_vars <;> ext i j <;>
      fin_cases i <;> fin_cases j <;> simp

/-- On the rank kernel the symmetric form has the single degree term. -/
theorem symmetric_on_rank_kernel (α β γ A κ : ℤ) (x y : Fin 4 → ℤ)
    (hx : x 0 = 0) (hy : y 0 = 0) :
    x ⬝ᵥ ((euler α β γ A κ + (euler α β γ A κ)ᵀ) *ᵥ y) =
      -2*A*x 1*y 1 := by
  simp [euler, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hx, hy]
  ring

end SerreMarkov.AdaptedIntrinsic
