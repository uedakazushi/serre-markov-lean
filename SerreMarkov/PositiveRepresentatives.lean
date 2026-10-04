import SerreMarkov.Content
import SerreMarkov.SerreInvariant
import SerreMarkov.IntrinsicType

/-! # The five explicit six-tuples and their distinct integral lattice classes

These are the manuscript's actual Gram coordinates. The proof computes the
content of the cube of the shifted Serre matrix in Lean's kernel, then uses
integral conjugacy invariance to distinguish all five representatives.
This module proves the concrete positive examples and their separation. It
does not assert exhaustiveness of the positive solution locus.
-/

namespace SerreMarkov.PositiveExamples

open Matrix

def representative (i : Fin 5) : Six :=
  ![⟨4,10,20,4,10,4⟩, ⟨5,14,40,5,16,4⟩, ⟨5,7,25,5,22,5⟩,
    ⟨7,8,18,4,13,4⟩, ⟨-6,-7,-3,3,7,6⟩] i

def cubeContent (i : Fin 5) : ℕ := ![64,54,40,22,72] i

theorem representative_q1 (i : Fin 5) : q1 (representative i) = 8 := by
  fin_cases i <;> norm_num [representative, q1]

theorem representative_q2 (i : Fin 5) :
    q2 (representative i) = ![-4,-4,-4,-4,4] i := by
  fin_cases i <;> norm_num [representative, q2]

theorem representative_isSolution (i : Fin 5) : isSolution (representative i) := by
  refine ⟨representative_q1 i, ?_⟩
  rw [representative_q2]
  fin_cases i <;> decide

theorem representative_cube_content (i : Fin 5) :
    matrixContent (shiftedSerre (representative i) ^ 3) = cubeContent i := by
  fin_cases i <;> decide

theorem cubeContent_positive (i : Fin 5) : 0 < cubeContent i := by
  fin_cases i <;> decide

theorem representative_regular (i : Fin 5) :
    shiftedSerre (representative i) ^ 3 ≠ 0 := by
  intro h
  have hc := representative_cube_content i
  rw [h, (matrixContent_eq_zero_iff 0).mpr rfl] at hc
  exact (cubeContent_positive i).ne' hc.symm

theorem representative_positive_marker (i : Fin 5) :
    0 < IntrinsicSigns.thirdMinorSum (representative i) := by
  fin_cases i <;> norm_num [IntrinsicSigns.thirdMinorSum, representative]

theorem representative_frame_A_positive (i : Fin 5)
    (R : IntrinsicFrame.Frame (representative i)) : 0 < IntrinsicFrame.A R :=
  (IntrinsicSigns.frame_thirdMinorSum_pos_iff R).mp (representative_positive_marker i)

theorem representative_intrinsicKind (i : Fin 5) :
    intrinsicKind (representative i) = .positive :=
  (intrinsicKind_positive_iff (representative i) (representative_isSolution i)).mpr
    (representative_positive_marker i)

theorem cubeContent_injective : Function.Injective cubeContent := by decide

end SerreMarkov.PositiveExamples

namespace SerreMarkov

theorem latticeEquivalent_shifted_power_content {z w : Six}
    (h : LatticeEquivalent z w) (n : ℕ) :
    matrixContent (shiftedSerre z ^ n) = matrixContent (shiftedSerre w ^ n) := by
  obtain ⟨B, hB⟩ := h
  rw [shiftedSerre_unit_conjugate_pow B hB]
  exact (matrixContent_conjugate (shiftedSerre z ^ n)
    (↑B⁻¹ : Mat4) (B : Mat4) (by simp) (by simp)).symm

namespace PositiveExamples

theorem representatives_not_latticeEquivalent {i j : Fin 5} (hne : i ≠ j) :
    ¬ LatticeEquivalent (representative i) (representative j) := by
  intro h
  have hc := latticeEquivalent_shifted_power_content h 3
  rw [representative_cube_content, representative_cube_content] at hc
  exact hne (cubeContent_injective hc)

theorem representatives_not_reachable {i j : Fin 5} (hne : i ≠ j) :
    ¬ Reachable (representative i) (representative j) := by
  intro h
  exact representatives_not_latticeEquivalent hne (reachable_latticeEquivalent h)

theorem representatives_latticeEquivalent_iff (i j : Fin 5) :
    LatticeEquivalent (representative i) (representative j) ↔ i = j := by
  constructor
  · intro h
    by_contra hne
    exact representatives_not_latticeEquivalent hne h
  · intro h
    subst j
    exact latticeEquivalent_refl _

theorem representatives_reachable_iff (i j : Fin 5) :
    Reachable (representative i) (representative j) ↔ i = j := by
  constructor
  · intro h
    exact (representatives_latticeEquivalent_iff i j).mp (reachable_latticeEquivalent h)
  · intro h
    subst j
    exact reachable_refl _

end PositiveExamples
end SerreMarkov
