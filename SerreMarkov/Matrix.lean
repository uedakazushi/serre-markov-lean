import SerreMarkov.Mutations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Matrix identities for rank-four Serre lattices

The inverse is an explicit integral polynomial matrix, so the definitions do not
use a matrix inverse over a field or a nonconstructive choice.  Every identity
below is proved in Lean's kernel using finite sums and ring arithmetic.
-/

namespace SerreMarkov

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Matrix
open scoped Polynomial

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℤ

/-- The Euler Gram matrix in the exceptional basis. -/
def gram (z : Six) : Mat4 :=
  !![1, z.a, z.b, z.c;
     0, 1, z.d, z.e;
     0, 0, 1, z.f;
     0, 0, 0, 1]

/-- Its integral inverse. -/
def gramInverse (z : Six) : Mat4 :=
  !![1, -z.a, z.a * z.d - z.b, -z.a * z.d * z.f + z.a * z.e + z.b * z.f - z.c;
     0, 1, -z.d, z.d * z.f - z.e;
     0, 0, 1, -z.f;
     0, 0, 0, 1]

theorem gram_mul_inverse (z : Six) : gram z * gramInverse z = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, gramInverse, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem inverse_mul_gram (z : Six) : gramInverse z * gram z = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, gramInverse, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gram_det (z : Six) : (gram z).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [gram, Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]

/-- The convention `χ(y,x) = χ(x,Sy)` gives `S = M⁻¹Mᵀ`. -/
def serre (z : Six) : Mat4 := gramInverse z * (gram z)ᵀ

/-- The shifted Serre operator. -/
def shiftedSerre (z : Six) : Mat4 := serre z + 1

def symmetricForm (z : Six) : Mat4 := gram z + (gram z)ᵀ

def alternatingForm (z : Six) : Mat4 := gram z - (gram z)ᵀ

theorem gram_mul_serre (z : Six) : gram z * serre z = (gram z)ᵀ := by
  rw [serre, ← Matrix.mul_assoc, gram_mul_inverse, Matrix.one_mul]

theorem symmetricForm_eq (z : Six) :
    symmetricForm z = gram z * shiftedSerre z := by
  simp only [symmetricForm, shiftedSerre, Matrix.mul_add, gram_mul_serre, Matrix.mul_one]
  exact add_comm _ _

theorem alternatingForm_eq (z : Six) :
    alternatingForm z = gram z * (2 • (1 : Mat4) - shiftedSerre z) := by
  simp [alternatingForm, shiftedSerre, Matrix.mul_sub, Matrix.mul_add,
    gram_mul_serre, two_smul]

theorem alternatingForm_det (z : Six) : (alternatingForm z).det = q2 z ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [alternatingForm, gram, q2, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_four, Fin.succAbove]
  ring

theorem alternatingForm_det_of_solution (z : Six) (h : isSolution z) :
    (alternatingForm z).det = 16 := by
  rw [alternatingForm_det]
  exact h.2

/-- The Serre operator preserves the Euler pairing. -/
theorem serre_isometry (z : Six) : (serre z)ᵀ * gram z * serre z = gram z := by
  calc
    (serre z)ᵀ * gram z * serre z = (serre z)ᵀ * (gram z)ᵀ := by
      rw [Matrix.mul_assoc, gram_mul_serre]
    _ = (gram z * serre z)ᵀ := by rw [Matrix.transpose_mul]
    _ = gram z := by rw [gram_mul_serre, Matrix.transpose_transpose]

/-- An integral change of exceptional basis conjugates the Serre operator. -/
theorem serre_conjugate_of_gram_congruence (z w : Six) (B Binv : Mat4)
    (hcong : gram w = Bᵀ * gram z * B) (hB : B * Binv = 1) :
    serre w = Binv * serre z * B := by
  have htrans : (gram w)ᵀ = Bᵀ * (gram z)ᵀ * B := by
    rw [hcong]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hpair : gram w * (Binv * serre z * B) = (gram w)ᵀ := by
    rw [htrans, hcong]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B Binv, hB, Matrix.one_mul]
    rw [← Matrix.mul_assoc (gram z) (serre z), gram_mul_serre]
  calc
    serre w = gramInverse w * (gram w * serre w) := by
      rw [← Matrix.mul_assoc, inverse_mul_gram, Matrix.one_mul]
    _ = gramInverse w * (gram w * (Binv * serre z * B)) := by
      rw [gram_mul_serre, hpair]
    _ = Binv * serre z * B := by
      rw [← Matrix.mul_assoc, inverse_mul_gram, Matrix.one_mul]

open Polynomial in
/-- The pencil `tM-Mᵀ`, which has much smaller entries than `tI-S`. -/
noncomputable def eulerPencil (z : Six) : Matrix (Fin 4) (Fin 4) ℤ[X] :=
  !![X - 1, C z.a * X, C z.b * X, C z.c * X;
     -C z.a, X - 1, C z.d * X, C z.e * X;
     -C z.b, -C z.d, X - 1, C z.f * X;
     -C z.c, -C z.e, -C z.f, X - 1]

theorem gram_mul_charmatrix (z : Six) :
    (gram z).map Polynomial.C * (serre z).charmatrix = eulerPencil z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, gramInverse, serre, eulerPencil, Matrix.charmatrix,
      Matrix.mul_apply, Fin.sum_univ_four, map_add, map_sub, map_mul, map_neg] <;> ring

open Polynomial in
theorem eulerPencil_det (z : Six) :
    (eulerPencil z).det = X ^ 4 + C (q1 z - 4) * X ^ 3 +
      C (q2 z ^ 2 - 2 * q1 z + 6) * X ^ 2 + C (q1 z - 4) * X + 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [eulerPencil, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_four,
    Fin.succAbove, q1, q2, map_add, map_sub, map_mul, map_neg, map_pow]
  ring

open Polynomial in
/-- The characteristic polynomial in Proposition 2.1 of the manuscript. -/
theorem serre_charpoly (z : Six) :
    (serre z).charpoly = X ^ 4 + C (q1 z - 4) * X ^ 3 +
      C (q2 z ^ 2 - 2 * q1 z + 6) * X ^ 2 + C (q1 z - 4) * X + 1 := by
  have h := congrArg Matrix.det (gram_mul_charmatrix z)
  have hd : ((gram z).map Polynomial.C).det = 1 := by
    simpa [RingHom.mapMatrix_apply, gram_det] using (Polynomial.C.map_det (gram z)).symm
  rw [Matrix.det_mul, hd, one_mul] at h
  exact h.trans (eulerPencil_det z)

open Polynomial in
theorem shiftedSerre_charpoly (z : Six) :
    (shiftedSerre z).charpoly = X ^ 4 + C (q1 z - 8) * X ^ 3 +
      C (q2 z ^ 2 - 5 * q1 z + 24) * X ^ 2 +
      C (8 * q1 z - 2 * q2 z ^ 2 - 32) * X + C (q2 z ^ 2 - 4 * q1 z + 16) := by
  have heq : shiftedSerre z = serre z - Matrix.scalar (Fin 4) (-1 : ℤ) := by
    simp only [shiftedSerre, map_neg, map_one, sub_neg_eq_add]
  rw [heq, Matrix.charpoly_sub_scalar, serre_charpoly]
  simp [map_add, map_sub, map_mul, map_neg, map_pow]
  ring

/-- The Diophantine equations are exactly fourth-order nilpotence. -/
theorem solution_iff_fourth_power_zero (z : Six) :
    isSolution z ↔ shiftedSerre z ^ 4 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc : (shiftedSerre z).charpoly = Polynomial.X ^ 4 := by
      rw [shiftedSerre_charpoly, h1, h2]
      norm_num
    have h := Matrix.aeval_self_charpoly (shiftedSerre z)
    rw [hc] at h
    simpa using h
  · intro h
    have hn : IsNilpotent (shiftedSerre z) := ⟨4, h⟩
    have hp := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hn).eq_zero
    have hc : (shiftedSerre z).charpoly = Polynomial.X ^ 4 := by
      simpa using sub_eq_zero.mp hp
    rw [shiftedSerre_charpoly] at hc
    have h3 := congrArg (fun p : ℤ[X] => p.coeff 3) hc
    have h0 := congrArg (fun p : ℤ[X] => p.coeff 0) hc
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at h3 h0
    norm_num at h3 h0
    exact ⟨by linarith, by linarith⟩

/-- Reflection in the `i`-th exceptional basis vector for the symmetric form. -/
def basisReflection (z : Six) (i : Fin 4) : Mat4 :=
  fun j k => (1 : Mat4) j k - if j = i then symmetricForm z k i else 0

theorem basisReflection_involution (z : Six) (i : Fin 4) :
    basisReflection z i * basisReflection z i = 1 := by
  apply Matrix.ext
  intro j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem basisReflection_isometry (z : Six) (i : Fin 4) :
    (basisReflection z i)ᵀ * symmetricForm z * basisReflection z i = symmetricForm z := by
  apply Matrix.ext
  intro j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem reflection_product (z : Six) :
    basisReflection z 0 * basisReflection z 1 *
      basisReflection z 2 * basisReflection z 3 = -serre z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [basisReflection, symmetricForm, gram, gramInverse, serre,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The rank-one matrix `p ⊗ r`, with `p=(0,-1,1,0)`, `r=(0,1,1,0)`. -/
def familyRankOne : Mat4 :=
  !![0, 0, 0, 0;
     0, -1, -1, 0;
     0, 1, 1, 0;
     0, 0, 0, 0]

/-- A reduced polynomial expression for the shifted operator on the family. -/
theorem family_shiftedSerre (x y : ℤ) :
    shiftedSerre (family x y) =
      !![-2, -x - 2 * y, -x - 2 * y, 2;
         x + 2 * y, y ^ 2 - 2, y ^ 2 - 2, -y;
         -x - 2 * y, 2 - y ^ 2, 2 - y ^ 2, y;
         -2, -y, -y, 2] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftedSerre, serre, gram, gramInverse, family,
      Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem family_cube (x y : ℤ) :
    shiftedSerre (family x y) ^ 3 = (-2 * (x + y) ^ 2) • familyRankOne := by
  rw [family_shiftedSerre]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [familyRankOne, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem family_fourth_power (x y : ℤ) : shiftedSerre (family x y) ^ 4 = 0 := by
  exact (solution_iff_fourth_power_zero (family x y)).mp (family_isSolution x y)

theorem family_degenerate_square (x : ℤ) : shiftedSerre (family x (-x)) ^ 2 = 0 := by
  rw [family_shiftedSerre]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem family_cube_eq_zero_iff (x y : ℤ) :
    shiftedSerre (family x y) ^ 3 = 0 ↔ x + y = 0 := by
  rw [family_cube]
  constructor
  · intro h
    have hentry := congrArg (fun A : Mat4 => A 1 1) h
    simp [familyRankOne] at hentry
    have hsq : (x + y) ^ 2 = 0 := by nlinarith [hentry]
    exact pow_eq_zero hsq
  · intro h
    simp [h]

end SerreMarkov
