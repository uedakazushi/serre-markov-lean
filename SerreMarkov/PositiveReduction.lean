import SerreMarkov.PositiveBoundedSigned

/-! # An exact finite-reduction boundary for the positive classification

All five original representatives themselves reach the bounded chamber.
Consequently reaching that chamber is necessary and sufficient for membership
in exactly one sporadic orbit. This is an equivalence, not an assertion of
unbounded descent or an assumption of a geometric degree/index theorem.
-/

namespace SerreMarkov.PositiveReduction

open PositiveBounded IntrinsicSigns

def representativeRow (r : Fin 5) : Fin 23 := ![6,5,0,1,2] r

theorem representativeRow_index (r : Fin 5) :
    PositiveBoundedTable.representativeIndex (representativeRow r) = r := by
  fin_cases r <;> decide +kernel

theorem representative_reaches_bounded (r : Fin 5) :
    ∃ w : Six, Bounded w ∧ Reachable (PositiveExamples.representative r) w := by
  refine ⟨PositiveBoundedTable.tuple (representativeRow r),table_bounded _,?_⟩
  simpa only [representativeRow_index] using
    reachable_symm (PositiveBoundedTable.tuple_reachable (representativeRow r))

/-- An exact characterization of the five actual mutation orbits, valid
for every starting tuple. The bounded reachability proposition is the precise
remaining reduction task when applied to arbitrary positive solutions. -/
theorem sporadic_classification_iff_bounded_reachability (z : Six) :
    (∃! r : Fin 5, Reachable z (PositiveExamples.representative r)) ↔
      ∃ w : Six, Bounded w ∧ Reachable z w := by
  constructor
  · rintro ⟨r,hr,_⟩
    obtain ⟨w,hw,hrw⟩ := representative_reaches_bounded r
    exact ⟨w,hw,reachable_trans hr hrw⟩
  · rintro ⟨w,hw,hr⟩
    exact reachable_bounded_classification_unique z w hw hr

/-- The universal positive classification is equivalent to the explicit
unbounded bounded-chamber reduction. Neither side is postulated here. -/
theorem positive_classification_iff_bounded_reduction :
    (∀ z : Six, isSolution z → shiftedSerre z^3 ≠ 0 → 0 < thirdMinorSum z →
      ∃! r : Fin 5, Reachable z (PositiveExamples.representative r)) ↔
    (∀ z : Six, isSolution z → shiftedSerre z^3 ≠ 0 → 0 < thirdMinorSum z →
      ∃ w : Six, Bounded w ∧ Reachable z w) := by
  constructor <;> intro h z hz hreg hpos
  · exact (sporadic_classification_iff_bounded_reachability z).mp (h z hz hreg hpos)
  · exact (sporadic_classification_iff_bounded_reachability z).mpr (h z hz hreg hpos)

end SerreMarkov.PositiveReduction
