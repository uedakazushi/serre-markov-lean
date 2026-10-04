import SerreMarkov.IntrinsicSigns
import SerreMarkov.IntrinsicUnique

/-! # The three intrinsic types on the actual solution set

The type is computed from the integer Serre cube and symmetric cofactors.
It is invariant under arbitrary integral Euler isomorphisms. No regular
classification or chamber theorem is assumed.
-/

namespace SerreMarkov

open Matrix IntrinsicFrame IntrinsicSigns IntrinsicUnique

theorem latticeEquivalent_isSolution {z w : Six} (h : LatticeEquivalent z w) :
    isSolution z ↔ isSolution w :=
  (solution_iff_fourth_power_zero z).trans
    ((latticeEquivalent_shifted_power_zero h 4).trans
      (solution_iff_fourth_power_zero w).symm)

theorem solution_cube_zero_iff_thirdMinorSum_zero (z : Six) (hz : isSolution z) :
    shiftedSerre z ^ 3 = 0 ↔ thirdMinorSum z = 0 := by
  constructor
  · intro h
    rw [← trace_adjugate_symmetric, ← symmetricCofactors_eq_adjugate,
      cofactor_zero_of_cube_zero z hz h]
    simp
  · intro h
    by_contra hreg
    exact solution_regular_thirdMinorSum_ne_zero z hz hreg h

theorem latticeEquivalent_regular_signs {z w : Six} (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) (h : LatticeEquivalent z w) :
    (0 < thirdMinorSum z ↔ 0 < thirdMinorSum w) ∧
      (thirdMinorSum z < 0 ↔ thirdMinorSum w < 0) := by
  have hw := (latticeEquivalent_isSolution h).mp hz
  have hwreg : shiftedSerre w ^ 3 ≠ 0 := by
    intro hc
    exact hreg ((latticeEquivalent_shifted_power_zero h 3).mpr hc)
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  obtain ⟨S⟩ := solution_regular_has_frame w hw hwreg
  have hA := (latticeEquivalent_frame_invariants R S h).2
  constructor
  · rw [frame_thirdMinorSum_pos_iff R, frame_thirdMinorSum_pos_iff S, hA]
  · rw [frame_thirdMinorSum_neg_iff R, frame_thirdMinorSum_neg_iff S, hA]

inductive IntrinsicKind where
  | degenerate
  | positive
  | negative
  deriving DecidableEq, Repr

def intrinsicKind (z : Six) : IntrinsicKind :=
  if shiftedSerre z ^ 3 = 0 then .degenerate
  else if 0 < thirdMinorSum z then .positive else .negative

theorem intrinsicKind_degenerate_iff (z : Six) :
    intrinsicKind z = .degenerate ↔ shiftedSerre z ^ 3 = 0 := by
  by_cases hc : shiftedSerre z ^ 3 = 0
  · simp [intrinsicKind, hc]
  · by_cases hp : 0 < thirdMinorSum z <;> simp [intrinsicKind, hc, hp]

theorem intrinsicKind_positive_iff (z : Six) (hz : isSolution z) :
    intrinsicKind z = .positive ↔ 0 < thirdMinorSum z := by
  by_cases hc : shiftedSerre z ^ 3 = 0
  · have hs := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hc
    simp [intrinsicKind, hc, hs]
  · simp [intrinsicKind, hc]

theorem intrinsicKind_negative_iff (z : Six) (hz : isSolution z) :
    intrinsicKind z = .negative ↔ thirdMinorSum z < 0 := by
  by_cases hc : shiftedSerre z ^ 3 = 0
  · have hs := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hc
    simp [intrinsicKind, hc, hs]
  · have hs := solution_regular_thirdMinorSum_ne_zero z hz hc
    by_cases hp : 0 < thirdMinorSum z
    · have hn : ¬ thirdMinorSum z < 0 := by omega
      simp [intrinsicKind, hc, hp, hn]
    · have hn : thirdMinorSum z < 0 := by omega
      simp [intrinsicKind, hc, hp, hn]

theorem latticeEquivalent_intrinsicKind {z w : Six} (hz : isSolution z)
    (h : LatticeEquivalent z w) : intrinsicKind z = intrinsicKind w := by
  by_cases hc : shiftedSerre z ^ 3 = 0
  · have hwc := (latticeEquivalent_shifted_power_zero h 3).mp hc
    simp [intrinsicKind, hc, hwc]
  · have hwc : shiftedSerre w ^ 3 ≠ 0 := by
      intro h0
      exact hc ((latticeEquivalent_shifted_power_zero h 3).mpr h0)
    have hp := (latticeEquivalent_regular_signs hz hc h).1
    simp only [intrinsicKind, hc, hwc, ↓reduceIte]
    simp only [hp]

theorem reachable_intrinsicKind {z w : Six} (hz : isSolution z)
    (h : Reachable z w) : intrinsicKind z = intrinsicKind w :=
  latticeEquivalent_intrinsicKind hz (reachable_latticeEquivalent h)

end SerreMarkov
