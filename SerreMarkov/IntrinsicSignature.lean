import SerreMarkov.IntrinsicSigns

/-!
# Explicit rational and real diagonal congruences

This file supplies actual unit matrices taking the symmetric Serre form to
`diag(2,-2,-2A,0)`, and counts the positive, negative and zero entries of
that exhibited diagonal. It does not define the inertia of an arbitrary
matrix by choosing a diagonalization or assume a uniqueness theorem.
-/

namespace SerreMarkov.IntrinsicSignature

open Matrix IntrinsicFrame
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
set_option maxHeartbeats 3000000

/-- The adapted symmetric Euler matrix over the rationals. -/
def rationalSymmetric (α β γ a k : ℤ) : RatMat4 :=
  !![2*(α:ℚ),(β:ℚ)+(γ:ℚ),-(k:ℚ),0;
     (β:ℚ)+(γ:ℚ),-2*(a:ℚ),0,0;
     -(k:ℚ),0,0,0;
     0,0,0,0]

/-- Columns are `u+(α-1)l/k`, `u+(α+1)l/k`, `v+(β+γ)l/k`, `p`. -/
def diagonalChange (α β γ k : ℤ) : RatMat4 :=
  !![1,1,0,0;
     0,0,1,0;
     ((α:ℚ)-1)/(k:ℚ),((α:ℚ)+1)/(k:ℚ),((β:ℚ)+(γ:ℚ))/(k:ℚ),0;
     0,0,0,1]

def rationalDiagonal (a : ℤ) : RatMat4 :=
  Matrix.diagonal ![(2:ℚ),-2,-2*(a:ℚ),0]

theorem diagonalChange_det (α β γ k : ℤ) :
    (diagonalChange α β γ k).det = -2/(k:ℚ) := by
  rw [Matrix.det_succ_row_zero]
  simp [diagonalChange, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_four, Fin.succAbove]
  ring

theorem diagonalChange_isUnit (α β γ k : ℤ) (hk : k ≠ 0) :
    IsUnit (diagonalChange α β γ k) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [diagonalChange_det, isUnit_iff_ne_zero]
  exact div_ne_zero (by norm_num) (by exact_mod_cast hk)

/-- The promised diagonal congruence, verified entry by entry. -/
theorem adapted_diagonal_congruence (α β γ a k : ℤ) (hk : k ≠ 0) :
    (diagonalChange α β γ k)ᵀ * rationalSymmetric α β γ a k *
      diagonalChange α β γ k = rationalDiagonal a := by
  have hkq : (k:ℚ) ≠ 0 := by exact_mod_cast hk
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalChange, rationalSymmetric, rationalDiagonal, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal_apply] <;> field_simp [hkq] <;> ring

theorem cast_adapted_symmetric (α β γ a k : ℤ) :
    integerToRatMatrix (AdaptedIntrinsic.euler α β γ a k +
      (AdaptedIntrinsic.euler α β γ a k)ᵀ) = rationalSymmetric α β γ a k := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [integerToRatMatrix, AdaptedIntrinsic.euler, rationalSymmetric] <;> ring

theorem integerToRatMatrix_transpose (M : Mat4) :
    integerToRatMatrix Mᵀ = (integerToRatMatrix M)ᵀ := rfl

/-- The change of coordinates from the original exceptional basis. -/
def rationalFrameChange {z : Six} (R : Frame z) : RatMat4 :=
  integerToRatMatrix (columns R) * diagonalChange (alpha R) (beta R) (gamma R) R.flag.k

theorem rationalFrameChange_isUnit {z : Six} (R : Frame z) :
    IsUnit (rationalFrameChange R) := by
  exact ((frame_isUnit R).map integerToRatMatrix).mul
    (diagonalChange_isUnit _ _ _ _ R.flag.k_pos.ne')

theorem rationalFrameChange_det {z : Six} (R : Frame z) :
    (rationalFrameChange R).det = ((columns R).det:ℚ) * (-2/(R.flag.k:ℚ)) := by
  rw [rationalFrameChange, Matrix.det_mul, diagonalChange_det]
  congr 1
  exact ((Int.castRingHom ℚ).map_det (columns R)).symm

/-- The original symmetric Gram matrix has the exhibited rational diagonal form. -/
theorem rational_frame_diagonal_congruence {z : Six} (R : Frame z) :
    (rationalFrameChange R)ᵀ * integerToRatMatrix (symmetricForm z) *
      rationalFrameChange R = rationalDiagonal (A R) := by
  have hframe : (integerToRatMatrix (columns R))ᵀ *
      integerToRatMatrix (symmetricForm z) * integerToRatMatrix (columns R) =
      rationalSymmetric (alpha R) (beta R) (gamma R) (A R) R.flag.k := by
    calc
      _ = integerToRatMatrix ((columns R)ᵀ * symmetricForm z * columns R) := by
        simp [map_mul, integerToRatMatrix_transpose]
      _ = _ := by rw [frame_symmetric_gram, cast_adapted_symmetric]
  calc
    _ = (diagonalChange (alpha R) (beta R) (gamma R) R.flag.k)ᵀ *
        ((integerToRatMatrix (columns R))ᵀ * integerToRatMatrix (symmetricForm z) *
          integerToRatMatrix (columns R)) *
        diagonalChange (alpha R) (beta R) (gamma R) R.flag.k := by
      rw [rationalFrameChange, Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hframe]; exact adapted_diagonal_congruence _ _ _ _ _ R.flag.k_pos.ne'

abbrev RealMat4 := Matrix (Fin 4) (Fin 4) ℝ

noncomputable def rationalToRealMatrix : RatMat4 →+* RealMat4 := (algebraMap ℚ ℝ).mapMatrix

def realDiagonal (a : ℤ) : RealMat4 :=
  Matrix.diagonal ![(2:ℝ),-2,-2*(a:ℝ),0]

noncomputable def realFrameChange {z : Six} (R : Frame z) : RealMat4 :=
  rationalToRealMatrix (rationalFrameChange R)

theorem realFrameChange_isUnit {z : Six} (R : Frame z) : IsUnit (realFrameChange R) :=
  (rationalFrameChange_isUnit R).map rationalToRealMatrix

theorem cast_rational_diagonal (a : ℤ) :
    rationalToRealMatrix (rationalDiagonal a) = realDiagonal a := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalToRealMatrix, rationalDiagonal, realDiagonal, Matrix.diagonal_apply]

/-- The same unit congruence over the reals; no inertia axiom is used. -/
theorem real_frame_diagonal_congruence {z : Six} (R : Frame z) :
    (realFrameChange R)ᵀ * rationalToRealMatrix (integerToRatMatrix (symmetricForm z)) *
      realFrameChange R = realDiagonal (A R) := by
  have h := congrArg rationalToRealMatrix (rational_frame_diagonal_congruence R)
  rw [map_mul, map_mul, cast_rational_diagonal] at h
  exact h

/-- Count signs only on the exhibited diagonal entries. -/
noncomputable def positiveDiagonalCount (D : RealMat4) : ℕ :=
  ∑ i : Fin 4, if 0 < D i i then 1 else 0

noncomputable def negativeDiagonalCount (D : RealMat4) : ℕ :=
  ∑ i : Fin 4, if D i i < 0 then 1 else 0

noncomputable def zeroDiagonalCount (D : RealMat4) : ℕ :=
  ∑ i : Fin 4, if D i i = 0 then 1 else 0

theorem positive_A_diagonal_counts (a : ℤ) (ha : 0 < a) :
    positiveDiagonalCount (realDiagonal a) = 1 ∧
      negativeDiagonalCount (realDiagonal a) = 2 ∧
      zeroDiagonalCount (realDiagonal a) = 1 := by
  have har : 0 < (a:ℝ) := by exact_mod_cast ha
  have hn : -2*(a:ℝ) < 0 := mul_neg_of_neg_of_pos (by norm_num) har
  unfold positiveDiagonalCount negativeDiagonalCount zeroDiagonalCount realDiagonal
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  norm_num [hn, hn.not_gt, hn.ne, ha, ha.le, ha.ne']

theorem negative_A_diagonal_counts (a : ℤ) (ha : a < 0) :
    positiveDiagonalCount (realDiagonal a) = 2 ∧
      negativeDiagonalCount (realDiagonal a) = 1 ∧
      zeroDiagonalCount (realDiagonal a) = 1 := by
  have har : (a:ℝ) < 0 := by exact_mod_cast ha
  have hp : 0 < -2*(a:ℝ) := mul_pos_of_neg_of_neg (by norm_num) har
  unfold positiveDiagonalCount negativeDiagonalCount zeroDiagonalCount realDiagonal
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  have hm : 2*(a:ℝ) < 0 := mul_neg_of_pos_of_neg (by norm_num) har
  norm_num [hp, hp.not_gt, hp.ne', ha, ha.le, ha.ne, hm]

theorem zero_A_diagonal_counts :
    positiveDiagonalCount (realDiagonal 0) = 1 ∧
      negativeDiagonalCount (realDiagonal 0) = 1 ∧
      zeroDiagonalCount (realDiagonal 0) = 2 := by
  unfold positiveDiagonalCount negativeDiagonalCount zeroDiagonalCount realDiagonal
  rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
  norm_num

/-- For this explicit diagonal, the pair `(1,2)` occurs exactly when `A>0`. -/
theorem diagonal_counts_one_two_iff (a : ℤ) :
    (positiveDiagonalCount (realDiagonal a) = 1 ∧
      negativeDiagonalCount (realDiagonal a) = 2) ↔ 0 < a := by
  constructor
  · intro h
    rcases lt_trichotomy 0 a with ha | ha | ha
    · exact ha
    · subst a
      have hh := zero_A_diagonal_counts
      omega
    · have hh := negative_A_diagonal_counts a ha
      omega
  · intro ha
    exact ⟨(positive_A_diagonal_counts a ha).1, (positive_A_diagonal_counts a ha).2.1⟩

/-- For this explicit diagonal, the pair `(2,1)` occurs exactly when `A<0`. -/
theorem diagonal_counts_two_one_iff (a : ℤ) :
    (positiveDiagonalCount (realDiagonal a) = 2 ∧
      negativeDiagonalCount (realDiagonal a) = 1) ↔ a < 0 := by
  constructor
  · intro h
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exact ha
    · subst a
      have hh := zero_A_diagonal_counts
      omega
    · have hh := positive_A_diagonal_counts a ha
      omega
  · intro ha
    exact ⟨(negative_A_diagonal_counts a ha).1, (negative_A_diagonal_counts a ha).2.1⟩

/-- A positive intrinsic frame gives an explicit real unit congruence with
one positive, two negative and one radical diagonal entry. -/
theorem positive_frame_certificate {z : Six} (R : Frame z) (hA : 0 < A R) :
    ∃ C : RealMat4, IsUnit C ∧
      Cᵀ * rationalToRealMatrix (integerToRatMatrix (symmetricForm z)) * C = realDiagonal (A R) ∧
      positiveDiagonalCount (realDiagonal (A R)) = 1 ∧
      negativeDiagonalCount (realDiagonal (A R)) = 2 ∧
      zeroDiagonalCount (realDiagonal (A R)) = 1 := by
  exact ⟨realFrameChange R, realFrameChange_isUnit R, real_frame_diagonal_congruence R,
    positive_A_diagonal_counts (A R) hA⟩

/-- A negative intrinsic frame gives two positive, one negative and one
radical diagonal entry by an explicit real unit congruence. -/
theorem negative_frame_certificate {z : Six} (R : Frame z) (hA : A R < 0) :
    ∃ C : RealMat4, IsUnit C ∧
      Cᵀ * rationalToRealMatrix (integerToRatMatrix (symmetricForm z)) * C = realDiagonal (A R) ∧
      positiveDiagonalCount (realDiagonal (A R)) = 2 ∧
      negativeDiagonalCount (realDiagonal (A R)) = 1 ∧
      zeroDiagonalCount (realDiagonal (A R)) = 1 := by
  exact ⟨realFrameChange R, realFrameChange_isUnit R, real_frame_diagonal_congruence R,
    negative_A_diagonal_counts (A R) hA⟩

end SerreMarkov.IntrinsicSignature
