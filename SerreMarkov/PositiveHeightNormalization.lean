import SerreMarkov.SignGaugeDescent

/-! # Positive sign normalization preserves the actual absolute height

This is a solution-level bridge to an arithmetic bounded classification. It
uses the actual rank signs and preserves height exactly; no terminal-height
bound or hyperbolic property is assumed.
-/

namespace SerreMarkov.PositiveHeightNormalization

open IntrinsicFrame IntrinsicSigns PositiveNormalization NegativeDescent
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

theorem positive_frame_height_normalization {z : Six} (R : Frame z)
    (hz : isSolution z) (hA : 0 < A R) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ 0 < thirdMinorSum w ∧
      (3 ≤ w.a ∧ 3 ≤ w.b ∧ 3 ≤ w.c ∧ 3 ≤ w.d ∧ 3 ≤ w.e ∧ 3 ≤ w.f) ∧
      l1 w = l1 z := by
  let w := signedSix z (rankSigns R)
  let S := signedFrame R (rankSigns R) (rankSigns_square R)
  have hr : Reachable z w := signedSix_reachable z _ (rankSigns_square R)
  have hw : isSolution w := by
    obtain ⟨word,hword⟩ := hr
    rw [← hword]
    exact applyWord_preserves_solution word z hz
  have hAS : A S = A R := (signedFrame_parameters R _ _).2
  have hS : 0 < A S := by rw [hAS]; exact hA
  have hpos : 0 < thirdMinorSum w := (frame_thirdMinorSum_pos_iff S).mpr hS
  have hri : ∀ i, 0 < basisRank S i := signedFrame_rank_positive R hA
  have hp : ∀ i j : Fin 4, i ≠ j → 3 ≤ symmetricForm w i j := by
    intro i j hij
    exact PositiveSeparation.positive_basis_pair_ge_three S hw hS i j hij (hri i) (hri j)
  have hcoords : 3 ≤ w.a ∧ 3 ≤ w.b ∧ 3 ≤ w.c ∧ 3 ≤ w.d ∧ 3 ≤ w.e ∧ 3 ≤ w.f := by
    simpa [symmetricForm,gram] using
      And.intro (hp 0 1 (by decide))
        (And.intro (hp 0 2 (by decide))
          (And.intro (hp 0 3 (by decide))
            (And.intro (hp 1 2 (by decide))
              (And.intro (hp 1 3 (by decide)) (hp 2 3 (by decide))))))
  exact ⟨w,hr,hw,hpos,hcoords,SignGaugeDescent.l1_signedSix z _ (rankSigns_square R)⟩

theorem positive_solution_height_normalization (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z^3 ≠ 0) (hpos : 0 < thirdMinorSum z) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ 0 < thirdMinorSum w ∧
      (3 ≤ w.a ∧ 3 ≤ w.b ∧ 3 ≤ w.c ∧ 3 ≤ w.d ∧ 3 ≤ w.e ∧ 3 ≤ w.f) ∧
      l1 w = l1 z := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  exact positive_frame_height_normalization R hz ((frame_thirdMinorSum_pos_iff R).mp hpos)

end SerreMarkov.PositiveHeightNormalization
