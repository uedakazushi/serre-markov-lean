import SerreMarkov.PositiveThreeSevenChecks
import SerreMarkov.PositiveThreeSevenCensusCore
import SerreMarkov.PositiveBoundedCensus

/-! Universal terminal classification in the fixed slice a=3,d=7.
Bounds are derived from genuine short words; every candidate is checked by
the Lean kernel. No general upper bound on d is asserted here. -/
namespace SerreMarkov.PositiveThreeSeven
open PositiveChamber PositiveShortWord NegativeDescent

theorem a_three_d_seven_terminal_unique (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=7) (ht : ShortTerminal z 2) : z=⟨3,7,4,7,8,8⟩ := by
  obtain h|h := chamber_census all_blocks_checked z hz ha hd ht
  · exact h
  · exact h

theorem a_three_d_seven_terminal_height (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=7) (ht : ShortTerminal z 2) : l1 z=37 := by
  rw [a_three_d_seven_terminal_unique z hz ha hd ht]
  decide +kernel

theorem a_three_d_seven_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=7) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  rw [a_three_d_seven_terminal_unique z hz ha hd ht]
  decide +kernel

end SerreMarkov.PositiveThreeSeven
