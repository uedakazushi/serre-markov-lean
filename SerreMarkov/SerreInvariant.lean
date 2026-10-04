import SerreMarkov.LatticeQuotient

/-! # Integral invariance of shifted Serre powers -/

namespace SerreMarkov

open Matrix

theorem shiftedSerre_unit_conjugate {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) :
    shiftedSerre w = (↑B⁻¹ : Mat4) * shiftedSerre z * (B : Mat4) := by
  have hs := serre_conjugate_of_gram_congruence z w (B : Mat4)
    (↑B⁻¹ : Mat4) h.symm (by simp)
  simp only [shiftedSerre, hs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  simp

theorem shiftedSerre_unit_conjugate_pow {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (n : ℕ) :
    shiftedSerre w ^ n = (↑B⁻¹ : Mat4) * shiftedSerre z ^ n * (B : Mat4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, shiftedSerre_unit_conjugate B h, pow_succ]
    calc
      ((↑B⁻¹ : Mat4) * shiftedSerre z ^ n * ↑B) *
          ((↑B⁻¹ : Mat4) * shiftedSerre z * ↑B) =
        (↑B⁻¹ : Mat4) * shiftedSerre z ^ n *
          ((B : Mat4) * ↑B⁻¹) * shiftedSerre z * ↑B := by noncomm_ring
      _ = (↑B⁻¹ : Mat4) * (shiftedSerre z ^ n * shiftedSerre z) * ↑B := by
        rw [show (B : Mat4) * (↑B⁻¹ : Mat4) = 1 by simp]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem latticeEquivalent_shifted_power_zero {z w : Six}
    (h : LatticeEquivalent z w) (n : ℕ) :
    shiftedSerre z ^ n = 0 ↔ shiftedSerre w ^ n = 0 := by
  constructor
  · intro hz
    obtain ⟨B, hB⟩ := h
    rw [shiftedSerre_unit_conjugate_pow B hB n, hz]
    simp
  · intro hw
    obtain ⟨B, hB⟩ := latticeEquivalent_symm h
    rw [shiftedSerre_unit_conjugate_pow B hB n, hw]
    simp

theorem reachable_shifted_power_zero {z w : Six}
    (h : Reachable z w) (n : ℕ) :
    shiftedSerre z ^ n = 0 ↔ shiftedSerre w ^ n = 0 :=
  latticeEquivalent_shifted_power_zero (reachable_latticeEquivalent h) n

end SerreMarkov
