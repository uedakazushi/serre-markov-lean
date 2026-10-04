import SerreMarkov.PositiveThreeSixChecks
import SerreMarkov.PositiveThreeSixCensusCore
import SerreMarkov.PositiveBoundedCensus

/-! Universal terminal classification in the fixed slice a=3,d=6.
Bounds are derived from genuine short words; every candidate is checked by
the Lean kernel. No general upper bound on d is asserted here. -/
namespace SerreMarkov.PositiveThreeSix
open PositiveChamber PositiveShortWord NegativeDescent

theorem a_three_d_six_terminal_unique (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=6) (ht : ShortTerminal z 2) : z=⟨3,7,6,6,7,3⟩ := by
  obtain h|h := chamber_census all_blocks_checked z hz ha hd ht
  · exact h
  · exact h

theorem a_three_d_six_terminal_height (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=6) (ht : ShortTerminal z 2) : l1 z=32 := by
  rw [a_three_d_six_terminal_unique z hz ha hd ht]
  decide +kernel

theorem a_three_d_six_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=6) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  rw [a_three_d_six_terminal_unique z hz ha hd ht]
  decide +kernel

end SerreMarkov.PositiveThreeSix
