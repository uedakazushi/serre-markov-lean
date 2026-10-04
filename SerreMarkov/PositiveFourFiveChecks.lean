import SerreMarkov.PositiveFourFiveData

/-! # The complete actual short-terminal classification for `a=4,d=5` -/
namespace SerreMarkov.PositiveFourFive
open PositiveChamber PositiveShortWord
def terminalBlock (b : ℤ) (t : ℕ) : List Six :=
  if b=4 ∧ t=0 then [⟨4,4,4,5,11,5⟩] else []

private theorem verified_blocks (bi t : ℕ) (hb : bi<14) (ht : t<blockCount (bi+3)) :
    blockSolutions (bi+3) t=terminalBlock (bi+3) t := by
  interval_cases bi

  · change t<1 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_3_0

  · change t<17 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_4_0

    · simpa [terminalBlock] using CensusData.verified_4_1

    · simpa [terminalBlock] using CensusData.verified_4_2

    · simpa [terminalBlock] using CensusData.verified_4_3

    · simpa [terminalBlock] using CensusData.verified_4_4

    · simpa [terminalBlock] using CensusData.verified_4_5

    · simpa [terminalBlock] using CensusData.verified_4_6

    · simpa [terminalBlock] using CensusData.verified_4_7

    · simpa [terminalBlock] using CensusData.verified_4_8

    · simpa [terminalBlock] using CensusData.verified_4_9

    · simpa [terminalBlock] using CensusData.verified_4_10

    · simpa [terminalBlock] using CensusData.verified_4_11

    · simpa [terminalBlock] using CensusData.verified_4_12

    · simpa [terminalBlock] using CensusData.verified_4_13

    · simpa [terminalBlock] using CensusData.verified_4_14

    · simpa [terminalBlock] using CensusData.verified_4_15

    · simpa [terminalBlock] using CensusData.verified_4_16

  · change t<13 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_5_0

    · simpa [terminalBlock] using CensusData.verified_5_1

    · simpa [terminalBlock] using CensusData.verified_5_2

    · simpa [terminalBlock] using CensusData.verified_5_3

    · simpa [terminalBlock] using CensusData.verified_5_4

    · simpa [terminalBlock] using CensusData.verified_5_5

    · simpa [terminalBlock] using CensusData.verified_5_6

    · simpa [terminalBlock] using CensusData.verified_5_7

    · simpa [terminalBlock] using CensusData.verified_5_8

    · simpa [terminalBlock] using CensusData.verified_5_9

    · simpa [terminalBlock] using CensusData.verified_5_10

    · simpa [terminalBlock] using CensusData.verified_5_11

    · simpa [terminalBlock] using CensusData.verified_5_12

  · change t<11 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_6_0

    · simpa [terminalBlock] using CensusData.verified_6_1

    · simpa [terminalBlock] using CensusData.verified_6_2

    · simpa [terminalBlock] using CensusData.verified_6_3

    · simpa [terminalBlock] using CensusData.verified_6_4

    · simpa [terminalBlock] using CensusData.verified_6_5

    · simpa [terminalBlock] using CensusData.verified_6_6

    · simpa [terminalBlock] using CensusData.verified_6_7

    · simpa [terminalBlock] using CensusData.verified_6_8

    · simpa [terminalBlock] using CensusData.verified_6_9

    · simpa [terminalBlock] using CensusData.verified_6_10

  · change t<9 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_7_0

    · simpa [terminalBlock] using CensusData.verified_7_1

    · simpa [terminalBlock] using CensusData.verified_7_2

    · simpa [terminalBlock] using CensusData.verified_7_3

    · simpa [terminalBlock] using CensusData.verified_7_4

    · simpa [terminalBlock] using CensusData.verified_7_5

    · simpa [terminalBlock] using CensusData.verified_7_6

    · simpa [terminalBlock] using CensusData.verified_7_7

    · simpa [terminalBlock] using CensusData.verified_7_8

  · change t<8 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_8_0

    · simpa [terminalBlock] using CensusData.verified_8_1

    · simpa [terminalBlock] using CensusData.verified_8_2

    · simpa [terminalBlock] using CensusData.verified_8_3

    · simpa [terminalBlock] using CensusData.verified_8_4

    · simpa [terminalBlock] using CensusData.verified_8_5

    · simpa [terminalBlock] using CensusData.verified_8_6

    · simpa [terminalBlock] using CensusData.verified_8_7

  · change t<7 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_9_0

    · simpa [terminalBlock] using CensusData.verified_9_1

    · simpa [terminalBlock] using CensusData.verified_9_2

    · simpa [terminalBlock] using CensusData.verified_9_3

    · simpa [terminalBlock] using CensusData.verified_9_4

    · simpa [terminalBlock] using CensusData.verified_9_5

    · simpa [terminalBlock] using CensusData.verified_9_6

  · change t<6 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_10_0

    · simpa [terminalBlock] using CensusData.verified_10_1

    · simpa [terminalBlock] using CensusData.verified_10_2

    · simpa [terminalBlock] using CensusData.verified_10_3

    · simpa [terminalBlock] using CensusData.verified_10_4

    · simpa [terminalBlock] using CensusData.verified_10_5

  · change t<5 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_11_0

    · simpa [terminalBlock] using CensusData.verified_11_1

    · simpa [terminalBlock] using CensusData.verified_11_2

    · simpa [terminalBlock] using CensusData.verified_11_3

    · simpa [terminalBlock] using CensusData.verified_11_4

  · change t<4 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_12_0

    · simpa [terminalBlock] using CensusData.verified_12_1

    · simpa [terminalBlock] using CensusData.verified_12_2

    · simpa [terminalBlock] using CensusData.verified_12_3

  · change t<3 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_13_0

    · simpa [terminalBlock] using CensusData.verified_13_1

    · simpa [terminalBlock] using CensusData.verified_13_2

  · change t<3 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_14_0

    · simpa [terminalBlock] using CensusData.verified_14_1

    · simpa [terminalBlock] using CensusData.verified_14_2

  · change t<2 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_15_0

    · simpa [terminalBlock] using CensusData.verified_15_1

  · change t<1 at ht
    interval_cases t

    · simpa [terminalBlock] using CensusData.verified_16_0

/-- The unique actual two-step terminal tuple in this positive slice. -/
theorem a_four_d_five_short_terminal_case (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=5) (ht : ShortTerminal z 2) : z=⟨4,4,4,5,11,5⟩ := by
  obtain ⟨bi,t,hbi,htb,hm⟩ := a_four_d_five_mem_block z hz ha hd ht
  rw [verified_blocks bi t hbi htb] at hm
  dsimp [terminalBlock] at hm
  split_ifs at hm
  · simpa using hm
  · simp at hm

/-- The explicit tuple reaches the original second sporadic representative. -/
theorem a_four_d_five_short_terminal_reachable (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=5) (ht : ShortTerminal z 2) :
    Reachable z (PositiveExamples.representative 1) := by
  rw [a_four_d_five_short_terminal_case z hz ha hd ht]
  exact PositiveBoundedTable.tuple_reachable (5 : Fin 23)

/-- Uniqueness uses integral lattice invariants already verified for the five classes. -/
theorem a_four_d_five_short_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=5) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  have hr := a_four_d_five_short_terminal_reachable z hz ha hd ht
  refine ⟨1,hr,?_⟩
  intro s hs
  exact (PositiveExamples.representatives_reachable_iff s 1).mp
    (reachable_trans (reachable_symm hs) hr)

end SerreMarkov.PositiveFourFive
