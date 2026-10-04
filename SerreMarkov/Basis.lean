import SerreMarkov.Matrix

/-!
# Integral basis changes realizing mutations

The scalar formulas are connected here with actual unimodular changes of the
exceptional basis. In particular, every `Reachable` pair has isometric Euler
lattices, with an explicitly constructed integral congruence matrix.
-/

namespace SerreMarkov

open Matrix

def basisMu1 (z : Six) : Mat4 :=
  !![z.a, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

def basisInv1 (z : Six) : Mat4 :=
  !![0, -1, 0, 0;
     1, z.a, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

def basisMu2 (z : Six) : Mat4 :=
  !![1, 0, 0, 0;
     0, z.d, 1, 0;
     0, -1, 0, 0;
     0, 0, 0, 1]

def basisInv2 (z : Six) : Mat4 :=
  !![1, 0, 0, 0;
     0, 0, -1, 0;
     0, 1, z.d, 0;
     0, 0, 0, 1]

def basisMu3 (z : Six) : Mat4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, z.f, 1;
     0, 0, -1, 0]

def basisInv3 (z : Six) : Mat4 :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, z.f]

def basisEps1 : Mat4 := !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def basisEps2 : Mat4 := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def basisEps3 : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]
def basisEps4 : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

theorem basisMu1_congruence (z : Six) :
    (basisMu1 z)ᵀ * gram z * basisMu1 z = gram (mu1 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMu1, gram, mu1, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
theorem basisInv1_congruence (z : Six) :
    (basisInv1 z)ᵀ * gram z * basisInv1 z = gram (inv1 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisInv1, gram, inv1, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
theorem basisMu2_congruence (z : Six) :
    (basisMu2 z)ᵀ * gram z * basisMu2 z = gram (mu2 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMu2, gram, mu2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
theorem basisInv2_congruence (z : Six) :
    (basisInv2 z)ᵀ * gram z * basisInv2 z = gram (inv2 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisInv2, gram, inv2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
theorem basisMu3_congruence (z : Six) :
    (basisMu3 z)ᵀ * gram z * basisMu3 z = gram (mu3 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMu3, gram, mu3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
theorem basisInv3_congruence (z : Six) :
    (basisInv3 z)ᵀ * gram z * basisInv3 z = gram (inv3 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisInv3, gram, inv3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem basisEps1_congruence (z : Six) :
    basisEps1ᵀ * gram z * basisEps1 = gram (eps1 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisEps1, gram, eps1, Matrix.mul_apply, Fin.sum_univ_succ]
theorem basisEps2_congruence (z : Six) :
    basisEps2ᵀ * gram z * basisEps2 = gram (eps2 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisEps2, gram, eps2, Matrix.mul_apply, Fin.sum_univ_succ]
theorem basisEps3_congruence (z : Six) :
    basisEps3ᵀ * gram z * basisEps3 = gram (eps3 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisEps3, gram, eps3, Matrix.mul_apply, Fin.sum_univ_succ]
theorem basisEps4_congruence (z : Six) :
    basisEps4ᵀ * gram z * basisEps4 = gram (eps4 z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisEps4, gram, eps4, Matrix.mul_apply, Fin.sum_univ_succ]

theorem basisMu1_det (z : Six) : (basisMu1 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisMu1, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
  decide
theorem basisInv1_det (z : Six) : (basisInv1 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisInv1, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
  decide
theorem basisMu2_det (z : Six) : (basisMu2 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisMu2, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisInv2_det (z : Six) : (basisInv2 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisInv2, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisMu3_det (z : Six) : (basisMu3 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisMu3, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisInv3_det (z : Six) : (basisInv3 z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisInv3, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisEps1_det : basisEps1.det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisEps1, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisEps2_det : basisEps2.det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisEps2, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisEps3_det : basisEps3.det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisEps3, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
theorem basisEps4_det : basisEps4.det = -1 := by
  rw [Matrix.det_succ_row_zero]
  simp [basisEps4, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]

def basisStep : Generator → Six → Mat4
  | .m1 => basisMu1
  | .m2 => basisMu2
  | .m3 => basisMu3
  | .i1 => basisInv1
  | .i2 => basisInv2
  | .i3 => basisInv3
  | .s1 => fun _ => basisEps1
  | .s2 => fun _ => basisEps2
  | .s3 => fun _ => basisEps3
  | .s4 => fun _ => basisEps4

theorem basisStep_congruence (g : Generator) (z : Six) :
    (basisStep g z)ᵀ * gram z * basisStep g z = gram (step g z) := by
  cases g <;> simp [basisStep, step, basisMu1_congruence, basisMu2_congruence,
    basisMu3_congruence, basisInv1_congruence, basisInv2_congruence,
    basisInv3_congruence, basisEps1_congruence, basisEps2_congruence,
    basisEps3_congruence, basisEps4_congruence]

theorem basisStep_det_sq (g : Generator) (z : Six) : (basisStep g z).det ^ 2 = 1 := by
  cases g <;> simp [basisStep, basisMu1_det, basisMu2_det, basisMu3_det,
    basisInv1_det, basisInv2_det, basisInv3_det, basisEps1_det, basisEps2_det,
    basisEps3_det, basisEps4_det]

def basisWord (z : Six) : List Generator → Mat4
  | [] => 1
  | g :: gs => basisStep g z * basisWord (step g z) gs

theorem basisWord_congruence (z : Six) (word : List Generator) :
    (basisWord z word)ᵀ * gram z * basisWord z word = gram (applyWord z word) := by
  induction word generalizing z with
  | nil => simp [basisWord, applyWord]
  | cons g gs ih =>
      simp only [basisWord, applyWord, Matrix.transpose_mul]
      calc
        (basisWord (step g z) gs)ᵀ * (basisStep g z)ᵀ * gram z *
          (basisStep g z * basisWord (step g z) gs) =
          (basisWord (step g z) gs)ᵀ * ((basisStep g z)ᵀ * gram z * basisStep g z) *
            basisWord (step g z) gs := by noncomm_ring
        _ = gram (applyWord (step g z) gs) := by
          rw [basisStep_congruence]
          exact ih (step g z)

theorem basisWord_det_sq (z : Six) (word : List Generator) : (basisWord z word).det ^ 2 = 1 := by
  induction word generalizing z with
  | nil => simp [basisWord]
  | cons g gs ih =>
      simp only [basisWord, Matrix.det_mul, mul_pow, basisStep_det_sq, ih, one_mul]

theorem reachable_integral_congruence {z z' : Six} (h : Reachable z z') :
    ∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧ Bᵀ * gram z * B = gram z' := by
  rcases h with ⟨word, hw⟩
  refine ⟨basisWord z word, ?_, ?_⟩
  · have hs := basisWord_det_sq z word
    have hf : ((basisWord z word).det - 1) * ((basisWord z word).det + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  · rw [← hw]
    exact basisWord_congruence z word

end SerreMarkov
