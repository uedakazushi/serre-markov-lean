import SerreMarkov.PositiveBoundedCensus
import SerreMarkov.PositiveHeightNormalization

/-! # The complete positive classification at bounded absolute height

The starting solution may have arbitrary signs. Actual intrinsic ranks supply
the sign normalization, and the exhaustive bounded census supplies the
mutation orbit. The sole bound is on the original six-coordinate height.
-/

namespace SerreMarkov.PositiveBounded

open IntrinsicSigns NegativeDescent

theorem positive_solution_bounded_classification (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z^3 ≠ 0) (hpos : 0 < thirdMinorSum z)
    (hheight : l1 z ≤ 37) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨w,hr,hw,hposw,hcoords,hl⟩ :=
    PositiveHeightNormalization.positive_solution_height_normalization z hz hreg hpos
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hcoords
  have hbound : (l1 w : ℤ) ≤ 37 := by
    rw [hl]
    exact_mod_cast hheight
  rw [← integerL1_cast] at hbound
  have hsum : w.a+w.b+w.c+w.d+w.e+w.f ≤ 37 := by
    simpa only [integerL1,
      abs_of_nonneg (by omega : 0 ≤ w.a), abs_of_nonneg (by omega : 0 ≤ w.b),
      abs_of_nonneg (by omega : 0 ≤ w.c), abs_of_nonneg (by omega : 0 ≤ w.d),
      abs_of_nonneg (by omega : 0 ≤ w.e), abs_of_nonneg (by omega : 0 ≤ w.f)] using hbound
  exact reachable_bounded_classification_unique z w
    ⟨hw,ha,hb,hc,hd,he,hf,hposw,hsum⟩ hr

end SerreMarkov.PositiveBounded
