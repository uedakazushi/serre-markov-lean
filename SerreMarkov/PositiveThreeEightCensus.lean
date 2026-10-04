import SerreMarkov.PositiveThreeEightChecks
import SerreMarkov.PositiveThreeEightCensusCore
import SerreMarkov.PositiveBoundedCensus

/-! Universal terminal classification in the fixed slice a=3,d=8.
Bounds are derived from genuine short words; every candidate is checked by
the Lean kernel. No general upper bound on d is asserted here. -/
namespace SerreMarkov.PositiveThreeEight
open PositiveChamber PositiveShortWord NegativeDescent

theorem a_three_d_eight_terminal_impossible (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=8) (ht : ShortTerminal z 2) : False := by
  obtain h|h := chamber_census all_blocks_checked z hz ha hd ht
  · rw [h] at ha; norm_num [first] at ha
  · rw [h] at ha; norm_num [second] at ha

end SerreMarkov.PositiveThreeEight
