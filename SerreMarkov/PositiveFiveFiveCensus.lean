import SerreMarkov.PositiveFiveFiveChecks

/-! # Complete classification of the positive terminal slice `a=d=5`

The input coordinates have no assumed upper bound. The proved conic bounds,
complete finite encoding, and kernel-checked blocks classify every terminal
point in the slice and supply a genuine mutation witness to its representative.
-/

namespace SerreMarkov.PositiveFiveFiveCensus

open PositiveChamber PositiveShortWord NegativeDescent

/-- The terminal tuple itself satisfies the original positive solution equations. -/
theorem terminal_chamber : Chamber PositiveFiveFive.terminal := by
  norm_num [Chamber,Coordinates,PositiveFiveFive.terminal,isSolution,q1,q2,
    IntrinsicSigns.thirdMinorSum]

theorem terminal_shortTerminal : ShortTerminal PositiveFiveFive.terminal 2 := by
  unfold ShortTerminal
  decide +kernel

theorem chamber_census (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5)
    (ht : ShortTerminal z 2) : z=PositiveFiveFive.terminal := by
  apply PositiveFiveFive.a_five_d_five_eq_of_checks _ z hz ha hd ht
  intro bi t hbi hti
  exact PositiveFiveFiveChecks.block_checks ⟨bi,hbi⟩ ⟨t,hti⟩

theorem a_five_d_five_height (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5)
    (ht : ShortTerminal z 2) : l1 z=33 := by
  rw [chamber_census z hz ha hd ht]
  rfl

theorem a_five_d_five_height_le (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5)
    (ht : ShortTerminal z 2) : l1 z≤37 := by
  rw [a_five_d_five_height z hz ha hd ht]
  norm_num

/-- The classified tuple belongs to the second original positive representative's actual orbit. -/
theorem a_five_d_five_reaches_representative (z : Six) (hz : Chamber z)
    (ha : z.a=5) (hd : z.d=5) (ht : ShortTerminal z 2) :
    Reachable z (PositiveExamples.representative 1) := by
  rw [chamber_census z hz ha hd ht]
  have h := PositiveBoundedTable.tuple_reachable (15 : Fin 23)
  change Reachable PositiveFiveFive.terminal (PositiveExamples.representative 1) at h
  exact h

end SerreMarkov.PositiveFiveFiveCensus
