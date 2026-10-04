import SerreMarkov.PositiveSmallThreeTerminal
import SerreMarkov.PositiveThreeSixCensus
import SerreMarkov.PositiveThreeSevenCensus
import SerreMarkov.PositiveThreeEightCensus

/-! # Complete terminal classification with end pairing three and d≤8

The upper bound d≤8 is an explicit restriction on this theorem's region.
It is not asserted for arbitrary positive terminal points. Each fixed slice
is bounded by actual short-word comparisons and exhaustively kernel checked.
-/
namespace SerreMarkov.PositiveThreeTerminalUpToEight
open PositiveChamber PositiveShortWord PositiveAdjacentThrees PositiveReversal NegativeDescent

theorem first_three_middle_upto_eight_terminal_bounded (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hdHi : z.d≤8) (ht : ShortTerminal z 2) : PositiveBounded.Bounded z := by
  have hdLo : 3 ≤ z.d := hz.2.2.2.2.2.1
  have hd : z.d=3 ∨ z.d=4 ∨ z.d=5 ∨ z.d=6 ∨ z.d=7 ∨ z.d=8 := by omega
  rcases hd with hd|hd|hd|hd|hd|hd
  · exact (chamber_no_adjacent_threes z hz ha hd).elim
  · rw [PositiveThreeFour.a_three_d_four_terminal_unique z hz ha hd ht]
    decide +kernel
  · obtain h|h := PositiveThreeFive.a_three_d_five_terminal_census z hz ha hd ht
    · rw [h]; decide +kernel
    · rw [h]; decide +kernel
  · rw [PositiveThreeSix.a_three_d_six_terminal_unique z hz ha hd ht]
    decide +kernel
  · rw [PositiveThreeSeven.a_three_d_seven_terminal_unique z hz ha hd ht]
    decide +kernel
  · exact (PositiveThreeEight.a_three_d_eight_terminal_impossible z hz ha hd ht).elim

theorem end_three_middle_upto_eight_terminal_bounded (z : Six) (hz : Chamber z)
    (hend : z.a=3 ∨ z.f=3) (hdHi : z.d≤8) (ht : ShortTerminal z 2) : PositiveBounded.Bounded z := by
  rcases hend with ha|hf
  · exact first_three_middle_upto_eight_terminal_bounded z hz ha hdHi ht
  · have hb := first_three_middle_upto_eight_terminal_bounded (reverseSix z)
      (reverseSix_chamber z hz) hf hdHi (reverseSix_shortTerminal z 2 ht)
    obtain ⟨_,_,_,_,_,_,_,_,hsum⟩ := hb
    obtain ⟨hsol,hpos,ha,hb,hc,hd,he,hf⟩ := hz
    refine ⟨hsol,ha,hb,hc,hd,he,hf,hpos,?_⟩
    dsimp [reverseSix] at hsum
    omega

theorem end_three_middle_upto_eight_terminal_classification (z : Six) (hz : Chamber z)
    (hend : z.a=3 ∨ z.f=3) (hdHi : z.d≤8) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) :=
  PositiveBounded.bounded_classification_unique z
    (end_three_middle_upto_eight_terminal_bounded z hz hend hdHi ht)

end SerreMarkov.PositiveThreeTerminalUpToEight
