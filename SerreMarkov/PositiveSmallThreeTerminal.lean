import SerreMarkov.PositiveThreeFourCensus
import SerreMarkov.PositiveThreeFiveCensus
import SerreMarkov.PositiveReversal

/-! Reflected terminal slices, derived by the actual generator automorphism. -/
namespace SerreMarkov.PositiveSmallThreeTerminal
open PositiveChamber PositiveShortWord PositiveAdjacentThrees PositiveReversal NegativeDescent

theorem d_four_f_three_terminal_unique (z : Six) (hz : Chamber z)
    (hd : z.d=4) (hf : z.f=3) (ht : ShortTerminal z 2) :
    z=⟨8,7,7,4,8,3⟩ := by
  have h := PositiveThreeFour.a_three_d_four_terminal_unique (reverseSix z)
    (reverseSix_chamber z hz) hf hd (reverseSix_shortTerminal z 2 ht)
  have heq := congrArg reverseSix h
  simpa only [reverseSix_involutive,reverseSix] using heq

theorem d_five_f_three_terminal_census (z : Six) (hz : Chamber z)
    (hd : z.d=5) (hf : z.f=3) (ht : ShortTerminal z 2) :
    z=⟨7,10,5,5,5,3⟩ ∨ z=⟨7,5,5,5,10,3⟩ := by
  obtain h|h := PositiveThreeFive.a_three_d_five_terminal_census (reverseSix z)
    (reverseSix_chamber z hz) hf hd (reverseSix_shortTerminal z 2 ht)
  · exact Or.inl (by simpa only [reverseSix_involutive,reverseSix] using congrArg reverseSix h)
  · exact Or.inr (by simpa only [reverseSix_involutive,reverseSix] using congrArg reverseSix h)

theorem d_four_f_three_terminal_height (z : Six) (hz : Chamber z)
    (hd : z.d=4) (hf : z.f=3) (ht : ShortTerminal z 2) : l1 z=37 := by
  rw [d_four_f_three_terminal_unique z hz hd hf ht]
  decide +kernel

theorem d_five_f_three_terminal_height (z : Six) (hz : Chamber z)
    (hd : z.d=5) (hf : z.f=3) (ht : ShortTerminal z 2) : l1 z=35 := by
  obtain h|h := d_five_f_three_terminal_census z hz hd hf ht
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel

theorem d_four_f_three_terminal_classification (z : Six) (hz : Chamber z)
    (hd : z.d=4) (hf : z.f=3) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  rw [d_four_f_three_terminal_unique z hz hd hf ht]
  decide +kernel

theorem d_five_f_three_terminal_classification (z : Six) (hz : Chamber z)
    (hd : z.d=5) (hf : z.f=3) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  obtain h|h := d_five_f_three_terminal_census z hz hd hf ht
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel

/-- Every terminal point with an end pairing three and middle pairing at
most five lies in the fully classified bounded chamber. -/
theorem end_three_middle_small_terminal_bounded (z : Six) (hz : Chamber z)
    (hend : z.a=3 ∨ z.f=3) (hsmall : z.d ≤ 5) (ht : ShortTerminal z 2) :
    PositiveBounded.Bounded z := by
  have hdLo : 3 ≤ z.d := hz.2.2.2.2.2.1
  have hd : z.d=3 ∨ z.d=4 ∨ z.d=5 := by omega
  rcases hend with ha|hf
  · rcases hd with hd|hd|hd
    · exact (chamber_no_adjacent_threes z hz ha hd).elim
    · rw [PositiveThreeFour.a_three_d_four_terminal_unique z hz ha hd ht]
      decide +kernel
    · obtain h|h := PositiveThreeFive.a_three_d_five_terminal_census z hz ha hd ht
      · rw [h]; decide +kernel
      · rw [h]; decide +kernel
  · rcases hd with hd|hd|hd
    · exact (chamber_no_last_adjacent_threes z hz hd hf).elim
    · rw [d_four_f_three_terminal_unique z hz hd hf ht]
      decide +kernel
    · obtain h|h := d_five_f_three_terminal_census z hz hd hf ht
      · rw [h]; decide +kernel
      · rw [h]; decide +kernel

theorem end_three_middle_small_terminal_classification (z : Six) (hz : Chamber z)
    (hend : z.a=3 ∨ z.f=3) (hsmall : z.d ≤ 5) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) :=
  PositiveBounded.bounded_classification_unique z
    (end_three_middle_small_terminal_bounded z hz hend hsmall ht)

end SerreMarkov.PositiveSmallThreeTerminal
