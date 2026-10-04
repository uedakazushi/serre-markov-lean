import SerreMarkov.LatticeQuotient

/-!
# Integral invariance of the divisors of second minors

The argument uses expansion of finite matrix products, rather than a
Smith-normal-form computation.  It therefore applies to every integral
Euler-lattice isomorphism, including changes of basis outside mutation words.
-/

namespace SerreMarkov

open Matrix
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

def secondMinor (A : Mat4) (i j k l : Fin 4) : ℤ :=
  A i k * A j l - A i l * A j k

def MinorDvd (d : ℤ) (A : Mat4) : Prop :=
  ∀ i j k l, d ∣ secondMinor A i j k l

theorem secondMinor_mul_left (B A : Mat4) (i j k l : Fin 4) :
    secondMinor (B * A) i j k l =
      ∑ p : Fin 4, ∑ q : Fin 4,
        B i p * B j q * secondMinor A p q k l := by
  simp only [secondMinor, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem secondMinor_mul_right (A B : Mat4) (i j k l : Fin 4) :
    secondMinor (A * B) i j k l =
      ∑ p : Fin 4, ∑ q : Fin 4,
        secondMinor A i j p q * B p k * B q l := by
  simp only [secondMinor, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem minorDvd_mul_left {d : ℤ} {A : Mat4}
    (h : MinorDvd d A) (B : Mat4) : MinorDvd d (B * A) := by
  intro i j k l
  rw [secondMinor_mul_left]
  apply Finset.dvd_sum
  intro p _
  apply Finset.dvd_sum
  intro q _
  exact dvd_mul_of_dvd_right (h p q k l) _

theorem minorDvd_mul_right {d : ℤ} {A : Mat4}
    (h : MinorDvd d A) (B : Mat4) : MinorDvd d (A * B) := by
  intro i j k l
  rw [secondMinor_mul_right]
  apply Finset.dvd_sum
  intro p _
  apply Finset.dvd_sum
  intro q _
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (h i j p q) _) _

theorem minorDvd_congruence {d : ℤ} {A : Mat4}
    (h : MinorDvd d A) (B : Mat4) : MinorDvd d (Bᵀ * A * B) :=
  minorDvd_mul_right (minorDvd_mul_left h Bᵀ) B

theorem symmetricForm_congruence {z w : Six} (B : Mat4)
    (h : Bᵀ * gram z * B = gram w) :
    Bᵀ * symmetricForm z * B = symmetricForm w := by
  simp only [symmetricForm, Matrix.mul_add, Matrix.add_mul]
  rw [h]
  congr 1
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using ht

theorem latticeEquivalent_minorDvd {z w : Six}
    (h : LatticeEquivalent z w) (d : ℤ) :
    MinorDvd d (symmetricForm z) ↔ MinorDvd d (symmetricForm w) := by
  constructor
  · intro hd
    obtain ⟨B, hB⟩ := h
    rw [← symmetricForm_congruence (B : Mat4) hB]
    exact minorDvd_congruence hd (B : Mat4)
  · intro hd
    obtain ⟨B, hB⟩ := latticeEquivalent_symm h
    rw [← symmetricForm_congruence (B : Mat4) hB]
    exact minorDvd_congruence hd (B : Mat4)

theorem degenerate_family_minorDvd (k d : ℤ) :
    MinorDvd d (symmetricForm (family k (-k))) ↔ d ∣ 4 - k ^ 2 := by
  constructor
  · intro h
    simpa [secondMinor, symmetricForm, gram, family, pow_two] using h 0 1 0 1
  · intro h
    have hn : d ∣ -(4 - k ^ 2) := dvd_neg.mpr h
    intro i j p q
    fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
      simp [secondMinor, symmetricForm, gram, family] <;>
      ring_nf at h hn ⊢ <;>
      first | exact dvd_zero d | exact h | exact hn

theorem degenerate_family_minor_content {k l : ℤ}
    (h : LatticeEquivalent (family k (-k)) (family l (-l))) :
    (4 - k ^ 2).natAbs = (4 - l ^ 2).natAbs := by
  have forward : (4 - k ^ 2) ∣ (4 - l ^ 2) := by
    apply (degenerate_family_minorDvd l _).mp
    apply (latticeEquivalent_minorDvd h _).mp
    exact (degenerate_family_minorDvd k _).mpr (dvd_refl _)
  have backward : (4 - l ^ 2) ∣ (4 - k ^ 2) := by
    apply (degenerate_family_minorDvd k _).mp
    apply (latticeEquivalent_minorDvd h _).mpr
    exact (degenerate_family_minorDvd l _).mpr (dvd_refl _)
  exact Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr forward)
    (Int.natAbs_dvd_natAbs.mpr backward)

end SerreMarkov
