import SerreMarkov.Matrix
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SerreMarkov

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- Divisibility of every entry, including the zero entries. -/
def AllEntriesDvd (d : ℤ) (M : Mat4) : Prop := ∀ i j, d ∣ M i j

theorem allEntriesDvd_add {d : ℤ} {M K : Mat4}
    (hM : AllEntriesDvd d M) (hK : AllEntriesDvd d K) : AllEntriesDvd d (M+K) := by
  intro i j
  exact (hM i j).add (hK i j)

theorem allEntriesDvd_mul_left {d : ℤ} {M : Mat4} (hM : AllEntriesDvd d M)
    (B : Mat4) : AllEntriesDvd d (B*M) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_right (hM k j) _)

theorem allEntriesDvd_mul_right {d : ℤ} {M : Mat4} (hM : AllEntriesDvd d M)
    (B : Mat4) : AllEntriesDvd d (M*B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (hM i k) _)

/-- Integral basis changes preserve the entry-divisibility ideal. -/
theorem allEntriesDvd_conjugate_iff (d : ℤ) (M B Binv : Mat4)
    (_hBB : B*Binv = 1) (hBB' : Binv*B = 1) :
    AllEntriesDvd d (B*M*Binv) ↔ AllEntriesDvd d M := by
  constructor
  · intro h
    have hh := allEntriesDvd_mul_right (allEntriesDvd_mul_left h Binv) B
    have heq : Binv*(B*M*Binv)*B = M := by
      calc
        _ = (Binv*B)*M*(Binv*B) := by noncomm_ring
        _ = M := by rw [hBB']; simp
    exact heq ▸ hh
  · intro h
    exact allEntriesDvd_mul_right (allEntriesDvd_mul_left h B) Binv

theorem allEntriesDvd_unit_conjugate_iff (d : ℤ) (M B : Mat4) (hB : IsUnit B) :
    AllEntriesDvd d (B*M*B⁻¹) ↔ AllEntriesDvd d M := by
  have hd := (Matrix.isUnit_iff_isUnit_det B).mp hB
  exact allEntriesDvd_conjugate_iff d M B B⁻¹
    (Matrix.mul_nonsing_inv B hd) (Matrix.nonsing_inv_mul B hd)

/-- The nonnegative generator of the ideal of all sixteen integral entries. -/
def matrixContent (M : Mat4) : ℕ :=
  Finset.univ.gcd (fun ij : Fin 4 × Fin 4 => (M ij.1 ij.2).natAbs)

theorem dvd_matrixContent_iff (d : ℕ) (M : Mat4) :
    d ∣ matrixContent M ↔ AllEntriesDvd (d : ℤ) M := by
  rw [matrixContent, Finset.dvd_gcd_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h i j
    exact Int.natCast_dvd.mpr (h (i,j))
  · intro h ij
    exact Int.natCast_dvd.mp (h ij.1 ij.2)

theorem matrixContent_conjugate (M B Binv : Mat4)
    (hBB : B*Binv = 1) (hBB' : Binv*B = 1) :
    matrixContent (B*M*Binv) = matrixContent M := by
  apply Nat.dvd_antisymm
  · rw [dvd_matrixContent_iff]
    exact (allEntriesDvd_conjugate_iff _ M B Binv hBB hBB').mp
      ((dvd_matrixContent_iff _ _).mp dvd_rfl)
  · rw [dvd_matrixContent_iff]
    exact (allEntriesDvd_conjugate_iff _ M B Binv hBB hBB').mpr
      ((dvd_matrixContent_iff _ _).mp dvd_rfl)

theorem matrixContent_unit_conjugate (M B : Mat4) (hB : IsUnit B) :
    matrixContent (B*M*B⁻¹) = matrixContent M := by
  have hd := (Matrix.isUnit_iff_isUnit_det B).mp hB
  exact matrixContent_conjugate M B B⁻¹
    (Matrix.mul_nonsing_inv B hd) (Matrix.nonsing_inv_mul B hd)

theorem matrixContent_conjugate_of_det (M B : Mat4) (hB : B.det = 1 ∨ B.det = -1) :
    matrixContent (B*M*B⁻¹) = matrixContent M := by
  apply matrixContent_unit_conjugate M B
  apply (Matrix.isUnit_iff_isUnit_det B).mpr
  exact Int.isUnit_iff.mpr hB

def oneEntryMatrix (i j : Fin 4) (c : ℤ) : Mat4 :=
  fun k l => if k = i ∧ l = j then c else 0

theorem allEntriesDvd_oneEntryMatrix (d c : ℤ) (i j : Fin 4) :
    AllEntriesDvd d (oneEntryMatrix i j c) ↔ d ∣ c := by
  constructor
  · intro h
    simpa [oneEntryMatrix] using h i j
  · intro h k l
    dsimp [oneEntryMatrix]
    split_ifs <;> simp [h]

theorem matrixContent_oneEntryMatrix (i j : Fin 4) (c : ℤ) :
    matrixContent (oneEntryMatrix i j c) = c.natAbs := by
  apply Nat.dvd_antisymm
  · have h := (dvd_matrixContent_iff _ (oneEntryMatrix i j c)).mp dvd_rfl
    exact Int.natCast_dvd.mp ((allEntriesDvd_oneEntryMatrix _ _ i j).mp h)
  · rw [dvd_matrixContent_iff, allEntriesDvd_oneEntryMatrix]
    exact Int.natCast_dvd.mpr dvd_rfl

/-- The cube of the shifted operator in an intrinsic adapted frame. -/
def intrinsicCube (A k : ℤ) : Mat4 :=
  !![0,0,0,0; 0,0,0,0; 0,0,0,0; 2*A*k^2,0,0,0]

theorem intrinsicCube_eq_oneEntryMatrix (A k : ℤ) :
    intrinsicCube A k = oneEntryMatrix 3 0 (2*A*k^2) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [intrinsicCube, oneEntryMatrix]

theorem allEntriesDvd_intrinsicCube (d A k : ℤ) :
    AllEntriesDvd d (intrinsicCube A k) ↔ d ∣ 2*A*k^2 := by
  rw [intrinsicCube_eq_oneEntryMatrix, allEntriesDvd_oneEntryMatrix]

theorem matrixContent_intrinsicCube (A k : ℤ) :
    matrixContent (intrinsicCube A k) = 2*A.natAbs*k.natAbs^2 := by
  rw [intrinsicCube_eq_oneEntryMatrix, matrixContent_oneEntryMatrix]
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem matrixContent_intrinsicCube_int (A k : ℤ) :
    (matrixContent (intrinsicCube A k) : ℤ) = 2 * |A| * k^2 := by
  rw [intrinsicCube_eq_oneEntryMatrix, matrixContent_oneEntryMatrix]
  simp [Int.natCast_natAbs, abs_mul, abs_pow]

theorem matrixContent_eq_zero_iff (M : Mat4) : matrixContent M = 0 ↔ M = 0 := by
  rw [matrixContent, Finset.gcd_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, Int.natAbs_eq_zero]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    exact h (i,j)
  · intro h ij
    simp [h]

theorem matrixContent_pos (M : Mat4) (h : M ≠ 0) : 0 < matrixContent M := by
  exact Nat.pos_of_ne_zero (fun hh => h ((matrixContent_eq_zero_iff M).mp hh))

end SerreMarkov
