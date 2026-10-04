import SerreMarkov.PositiveThreeFourChecks
import SerreMarkov.PositiveThreeFourCensusCore
import SerreMarkov.PositiveBoundedCensus

/-! # Complete two-step terminal classification in the slice a=3,d=4

The equations and actual short-word comparisons imply a finite conic box.
All encoded points in that box are checked by the Lean kernel. One-step
terminal points consist of two tuples, and an actual two-step word eliminates
the larger one. This is a universal theorem for this slice, not a global
height bound or a classification of every positive solution.
-/
namespace SerreMarkov.PositiveThreeFour

open PositiveChamber PositiveThreeFourBounds NegativeDescent PositiveShortWord

/-- All one-step terminal points in the slice; no coordinate box is assumed. -/
theorem a_three_d_four_one_step_census (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=4) (hone : oneStepCheck z=true) :
    z=first ∨ z=extra :=
  chamber_census all_blocks_checked z hz ha hd hone

/-- A two-step terminal point in the slice is the unique small tuple. -/
theorem a_three_d_four_terminal_unique (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=4) (ht : ShortTerminal z 2) :
    z=⟨3,8,7,4,7,8⟩ := by
  obtain h|h := a_three_d_four_one_step_census z hz ha hd (shortTerminal_oneStepCheck z ht)
  · exact h
  · have hword : [.m2,.m1] ∈ braidWords 2 := by decide +kernel
    have hn := ht [.m2,.m1] hword
    rw [h] at hn
    have hd := extra_short_descent
    omega

theorem a_three_d_four_terminal_height (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=4) (ht : ShortTerminal z 2) : l1 z=37 := by
  rw [a_three_d_four_terminal_unique z hz ha hd ht]
  decide +kernel

/-- The actual manuscript orbit follows from the full bounded census. -/
theorem a_three_d_four_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=4) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  have heq := a_three_d_four_terminal_unique z hz ha hd ht
  apply PositiveBounded.bounded_classification_unique z
  rw [heq]
  decide +kernel

end SerreMarkov.PositiveThreeFour
