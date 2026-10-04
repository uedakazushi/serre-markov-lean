import SerreMarkov.IntrinsicFrame
import SerreMarkov.RationalLattice
import SerreMarkov.IntrinsicSigns

/-!
# Arithmetic integerization of every positive intrinsic frame

The half-turn input here is extracted from the actual integer exceptional
basis by `IntrinsicFrame.positiveHalfTurnData`. Thus the common conjugation is obtained
from the integral Euler form itself, without assuming rational even monomials
or a finitely generated integral order as extra hypotheses.

This theorem does not assert finite covolume or index twelve.
-/

namespace SerreMarkov.PositiveIntegral

open RationalClifford CliffordOrder IntrinsicFrame

/-- All even words attached to one positive integral Serre frame become
determinant-one integer matrices under the same rational conjugation, whose
determinant is positive. The half-turns are the ones extracted from `z`. -/
theorem positive_frame_even_words_integral_SL2 (z : Six) (R : Frame z)
    (hA : 0 < IntrinsicFrame.A R) :
    ∃ C Cinv : RatMat2, 0 < C.det ∧ C*Cinv = 1 ∧ Cinv*C = 1 ∧
      ∀ w : List (Fin 4), Even w.length →
        ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det = 1 ∧
          rationalMatrixCast Cinv *
              wordProduct (NormedClifford.generators (positiveHalfTurnData R hA)) w *
            rationalMatrixCast C = Z.map (Int.cast : ℤ → ℝ) :=
  normalized_even_words_integral_SL2_positive_conjugation (positiveHalfTurnData R hA)

/-- The positive sign criterion on an arbitrary regular solution suffices for
the entire frame-to-integerization construction. No frame is assumed. -/
theorem positive_solution_even_words_integral_SL2 (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) (hpos : 0 < IntrinsicSigns.thirdMinorSum z) :
    ∃ (R : Frame z) (hA : 0 < IntrinsicFrame.A R) (C Cinv : RatMat2),
      0 < C.det ∧ C*Cinv = 1 ∧ Cinv*C = 1 ∧
        ∀ w : List (Fin 4), Even w.length →
          ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det = 1 ∧
            rationalMatrixCast Cinv *
                wordProduct (NormedClifford.generators (positiveHalfTurnData R hA)) w *
              rationalMatrixCast C = Z.map (Int.cast : ℤ → ℝ) := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  have hA := (IntrinsicSigns.frame_thirdMinorSum_pos_iff R).mp hpos
  obtain ⟨C, Cinv, hC⟩ := positive_frame_even_words_integral_SL2 z R hA
  exact ⟨R, hA, C, Cinv, hC⟩

end SerreMarkov.PositiveIntegral
