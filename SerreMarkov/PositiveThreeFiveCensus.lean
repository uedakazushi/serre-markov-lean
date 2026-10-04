import SerreMarkov.PositiveThreeFiveChecks
import SerreMarkov.PositiveThreeFiveCensusCore
import SerreMarkov.PositiveBoundedCensus

/-! # Complete two-step terminal classification for a=3,d=5

The finite box is proved from genuine short-word height comparisons and the
solution equations. Every encoded candidate is checked in the Lean kernel.
No height bound, properness, or finite-index hypothesis is assumed.
-/
namespace SerreMarkov.PositiveThreeFive
open PositiveChamber PositiveThreeFourBounds PositiveShortWord NegativeDescent

/-- These are all two-step terminal points in the slice. -/
theorem a_three_d_five_terminal_census (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=5) (ht : ShortTerminal z 2) :
    z=⟨3,5,5,5,10,7⟩ ∨ z=⟨3,10,5,5,5,7⟩ :=
  chamber_census all_blocks_checked z hz ha hd ht

theorem a_three_d_five_terminal_height (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=5) (ht : ShortTerminal z 2) : l1 z=35 := by
  obtain h|h := a_three_d_five_terminal_census z hz ha hd ht
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel

/-- The finite census connects both tuples to the genuine manuscript orbit. -/
theorem a_three_d_five_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=5) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  apply PositiveBounded.bounded_classification_unique z
  obtain h|h := a_three_d_five_terminal_census z hz ha hd ht
  · rw [h]; decide +kernel
  · rw [h]; decide +kernel

end SerreMarkov.PositiveThreeFive
