import SerreMarkov.PositiveFourFour

/-! # Kernel-checked terminal points of the slice `a=d=4`

Each declaration checks a block of ten consecutive third coefficients after
the exact binary-conic filter. Completeness was proved separately from these
computed outputs. The conclusion is restricted to this short-terminal slice.
-/
namespace SerreMarkov.PositiveFourFour
open PositiveChamber PositiveShortWord
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem verified_3_0 : blockSolutions 3 0=[] := by decide +kernel

private theorem verified_3_1 : blockSolutions 3 1=[] := by decide +kernel

private theorem verified_3_2 : blockSolutions 3 2=[] := by decide +kernel

private theorem verified_3_3 : blockSolutions 3 3=[] := by decide +kernel

private theorem verified_3_4 : blockSolutions 3 4=[] := by decide +kernel

private theorem verified_3_5 : blockSolutions 3 5=[] := by decide +kernel

private theorem verified_3_6 : blockSolutions 3 6=[] := by decide +kernel

private theorem verified_3_7 : blockSolutions 3 7=[] := by decide +kernel

private theorem verified_3_8 : blockSolutions 3 8=[] := by decide +kernel

private theorem verified_3_9 : blockSolutions 3 9=[] := by decide +kernel

#print axioms verified_3_9

private theorem verified_4_0 : blockSolutions 4 0=[] := by decide +kernel

private theorem verified_4_1 : blockSolutions 4 1=[] := by decide +kernel

private theorem verified_4_2 : blockSolutions 4 2=[] := by decide +kernel

private theorem verified_4_3 : blockSolutions 4 3=[] := by decide +kernel

private theorem verified_4_4 : blockSolutions 4 4=[] := by decide +kernel

private theorem verified_4_5 : blockSolutions 4 5=[] := by decide +kernel

private theorem verified_4_6 : blockSolutions 4 6=[] := by decide +kernel

private theorem verified_4_7 : blockSolutions 4 7=[] := by decide +kernel

private theorem verified_4_8 : blockSolutions 4 8=[] := by decide +kernel

private theorem verified_4_9 : blockSolutions 4 9=[] := by decide +kernel

#print axioms verified_4_9

private theorem verified_5_0 : blockSolutions 5 0=[] := by decide +kernel

private theorem verified_5_1 : blockSolutions 5 1=[] := by decide +kernel

private theorem verified_5_2 : blockSolutions 5 2=[] := by decide +kernel

private theorem verified_5_3 : blockSolutions 5 3=[] := by decide +kernel

private theorem verified_5_4 : blockSolutions 5 4=[] := by decide +kernel

private theorem verified_5_5 : blockSolutions 5 5=[] := by decide +kernel

private theorem verified_5_6 : blockSolutions 5 6=[] := by decide +kernel

private theorem verified_5_7 : blockSolutions 5 7=[] := by decide +kernel

private theorem verified_5_8 : blockSolutions 5 8=[] := by decide +kernel

private theorem verified_5_9 : blockSolutions 5 9=[] := by decide +kernel

#print axioms verified_5_9

private theorem verified_6_0 : blockSolutions 6 0=[⟨4,6,4,4,6,4⟩] := by decide +kernel

private theorem verified_6_1 : blockSolutions 6 1=[] := by decide +kernel

private theorem verified_6_2 : blockSolutions 6 2=[] := by decide +kernel

private theorem verified_6_3 : blockSolutions 6 3=[] := by decide +kernel

private theorem verified_6_4 : blockSolutions 6 4=[] := by decide +kernel

private theorem verified_6_5 : blockSolutions 6 5=[] := by decide +kernel

private theorem verified_6_6 : blockSolutions 6 6=[] := by decide +kernel

private theorem verified_6_7 : blockSolutions 6 7=[] := by decide +kernel

private theorem verified_6_8 : blockSolutions 6 8=[] := by decide +kernel

private theorem verified_6_9 : blockSolutions 6 9=[] := by decide +kernel

#print axioms verified_6_9

private theorem verified_7_0 : blockSolutions 7 0=[] := by decide +kernel

private theorem verified_7_1 : blockSolutions 7 1=[] := by decide +kernel

private theorem verified_7_2 : blockSolutions 7 2=[] := by decide +kernel

private theorem verified_7_3 : blockSolutions 7 3=[] := by decide +kernel

private theorem verified_7_4 : blockSolutions 7 4=[] := by decide +kernel

private theorem verified_7_5 : blockSolutions 7 5=[] := by decide +kernel

private theorem verified_7_6 : blockSolutions 7 6=[] := by decide +kernel

private theorem verified_7_7 : blockSolutions 7 7=[] := by decide +kernel

private theorem verified_7_8 : blockSolutions 7 8=[] := by decide +kernel

private theorem verified_7_9 : blockSolutions 7 9=[] := by decide +kernel

#print axioms verified_7_9

private theorem verified_8_0 : blockSolutions 8 0=[] := by decide +kernel

private theorem verified_8_1 : blockSolutions 8 1=[] := by decide +kernel

private theorem verified_8_2 : blockSolutions 8 2=[] := by decide +kernel

private theorem verified_8_3 : blockSolutions 8 3=[] := by decide +kernel

private theorem verified_8_4 : blockSolutions 8 4=[] := by decide +kernel

private theorem verified_8_5 : blockSolutions 8 5=[] := by decide +kernel

private theorem verified_8_6 : blockSolutions 8 6=[] := by decide +kernel

private theorem verified_8_7 : blockSolutions 8 7=[] := by decide +kernel

private theorem verified_8_8 : blockSolutions 8 8=[] := by decide +kernel

private theorem verified_8_9 : blockSolutions 8 9=[] := by decide +kernel

#print axioms verified_8_9

private theorem verified_9_0 : blockSolutions 9 0=[] := by decide +kernel

private theorem verified_9_1 : blockSolutions 9 1=[] := by decide +kernel

private theorem verified_9_2 : blockSolutions 9 2=[] := by decide +kernel

private theorem verified_9_3 : blockSolutions 9 3=[] := by decide +kernel

private theorem verified_9_4 : blockSolutions 9 4=[] := by decide +kernel

private theorem verified_9_5 : blockSolutions 9 5=[] := by decide +kernel

private theorem verified_9_6 : blockSolutions 9 6=[] := by decide +kernel

private theorem verified_9_7 : blockSolutions 9 7=[] := by decide +kernel

private theorem verified_9_8 : blockSolutions 9 8=[] := by decide +kernel

private theorem verified_9_9 : blockSolutions 9 9=[] := by decide +kernel

#print axioms verified_9_9

private theorem verified_10_0 : blockSolutions 10 0=[] := by decide +kernel

private theorem verified_10_1 : blockSolutions 10 1=[] := by decide +kernel

private theorem verified_10_2 : blockSolutions 10 2=[] := by decide +kernel

private theorem verified_10_3 : blockSolutions 10 3=[] := by decide +kernel

private theorem verified_10_4 : blockSolutions 10 4=[] := by decide +kernel

private theorem verified_10_5 : blockSolutions 10 5=[] := by decide +kernel

private theorem verified_10_6 : blockSolutions 10 6=[] := by decide +kernel

private theorem verified_10_7 : blockSolutions 10 7=[] := by decide +kernel

private theorem verified_10_8 : blockSolutions 10 8=[] := by decide +kernel

private theorem verified_10_9 : blockSolutions 10 9=[] := by decide +kernel

#print axioms verified_10_9

private theorem verified_11_0 : blockSolutions 11 0=[⟨4,11,5,4,4,5⟩] := by decide +kernel

private theorem verified_11_1 : blockSolutions 11 1=[] := by decide +kernel

private theorem verified_11_2 : blockSolutions 11 2=[] := by decide +kernel

private theorem verified_11_3 : blockSolutions 11 3=[] := by decide +kernel

private theorem verified_11_4 : blockSolutions 11 4=[] := by decide +kernel

private theorem verified_11_5 : blockSolutions 11 5=[] := by decide +kernel

private theorem verified_11_6 : blockSolutions 11 6=[] := by decide +kernel

private theorem verified_11_7 : blockSolutions 11 7=[] := by decide +kernel

private theorem verified_11_8 : blockSolutions 11 8=[] := by decide +kernel

private theorem verified_11_9 : blockSolutions 11 9=[] := by decide +kernel

#print axioms verified_11_9

private theorem verified_12_0 : blockSolutions 12 0=[] := by decide +kernel

private theorem verified_12_1 : blockSolutions 12 1=[] := by decide +kernel

private theorem verified_12_2 : blockSolutions 12 2=[] := by decide +kernel

private theorem verified_12_3 : blockSolutions 12 3=[] := by decide +kernel

private theorem verified_12_4 : blockSolutions 12 4=[] := by decide +kernel

private theorem verified_12_5 : blockSolutions 12 5=[] := by decide +kernel

private theorem verified_12_6 : blockSolutions 12 6=[] := by decide +kernel

private theorem verified_12_7 : blockSolutions 12 7=[] := by decide +kernel

private theorem verified_12_8 : blockSolutions 12 8=[] := by decide +kernel

private theorem verified_12_9 : blockSolutions 12 9=[] := by decide +kernel

#print axioms verified_12_9

private theorem verified_13_0 : blockSolutions 13 0=[] := by decide +kernel

private theorem verified_13_1 : blockSolutions 13 1=[] := by decide +kernel

private theorem verified_13_2 : blockSolutions 13 2=[] := by decide +kernel

private theorem verified_13_3 : blockSolutions 13 3=[] := by decide +kernel

private theorem verified_13_4 : blockSolutions 13 4=[] := by decide +kernel

private theorem verified_13_5 : blockSolutions 13 5=[] := by decide +kernel

private theorem verified_13_6 : blockSolutions 13 6=[] := by decide +kernel

private theorem verified_13_7 : blockSolutions 13 7=[] := by decide +kernel

private theorem verified_13_8 : blockSolutions 13 8=[] := by decide +kernel

private theorem verified_13_9 : blockSolutions 13 9=[] := by decide +kernel

#print axioms verified_13_9

def terminalBlock (b : ℤ) (t : ℕ) : List Six :=
  if b=6 ∧ t=0 then [⟨4,6,4,4,6,4⟩] else
  if b=11 ∧ t=0 then [⟨4,11,5,4,4,5⟩] else []

private theorem verified_blocks (bi t : ℕ) (hb : bi<11) (ht : t<10) :
    blockSolutions (bi+3) t=terminalBlock (bi+3) t := by
  interval_cases bi

  · interval_cases t

    · simpa [terminalBlock] using verified_3_0

    · simpa [terminalBlock] using verified_3_1

    · simpa [terminalBlock] using verified_3_2

    · simpa [terminalBlock] using verified_3_3

    · simpa [terminalBlock] using verified_3_4

    · simpa [terminalBlock] using verified_3_5

    · simpa [terminalBlock] using verified_3_6

    · simpa [terminalBlock] using verified_3_7

    · simpa [terminalBlock] using verified_3_8

    · simpa [terminalBlock] using verified_3_9

  · interval_cases t

    · simpa [terminalBlock] using verified_4_0

    · simpa [terminalBlock] using verified_4_1

    · simpa [terminalBlock] using verified_4_2

    · simpa [terminalBlock] using verified_4_3

    · simpa [terminalBlock] using verified_4_4

    · simpa [terminalBlock] using verified_4_5

    · simpa [terminalBlock] using verified_4_6

    · simpa [terminalBlock] using verified_4_7

    · simpa [terminalBlock] using verified_4_8

    · simpa [terminalBlock] using verified_4_9

  · interval_cases t

    · simpa [terminalBlock] using verified_5_0

    · simpa [terminalBlock] using verified_5_1

    · simpa [terminalBlock] using verified_5_2

    · simpa [terminalBlock] using verified_5_3

    · simpa [terminalBlock] using verified_5_4

    · simpa [terminalBlock] using verified_5_5

    · simpa [terminalBlock] using verified_5_6

    · simpa [terminalBlock] using verified_5_7

    · simpa [terminalBlock] using verified_5_8

    · simpa [terminalBlock] using verified_5_9

  · interval_cases t

    · simpa [terminalBlock] using verified_6_0

    · simpa [terminalBlock] using verified_6_1

    · simpa [terminalBlock] using verified_6_2

    · simpa [terminalBlock] using verified_6_3

    · simpa [terminalBlock] using verified_6_4

    · simpa [terminalBlock] using verified_6_5

    · simpa [terminalBlock] using verified_6_6

    · simpa [terminalBlock] using verified_6_7

    · simpa [terminalBlock] using verified_6_8

    · simpa [terminalBlock] using verified_6_9

  · interval_cases t

    · simpa [terminalBlock] using verified_7_0

    · simpa [terminalBlock] using verified_7_1

    · simpa [terminalBlock] using verified_7_2

    · simpa [terminalBlock] using verified_7_3

    · simpa [terminalBlock] using verified_7_4

    · simpa [terminalBlock] using verified_7_5

    · simpa [terminalBlock] using verified_7_6

    · simpa [terminalBlock] using verified_7_7

    · simpa [terminalBlock] using verified_7_8

    · simpa [terminalBlock] using verified_7_9

  · interval_cases t

    · simpa [terminalBlock] using verified_8_0

    · simpa [terminalBlock] using verified_8_1

    · simpa [terminalBlock] using verified_8_2

    · simpa [terminalBlock] using verified_8_3

    · simpa [terminalBlock] using verified_8_4

    · simpa [terminalBlock] using verified_8_5

    · simpa [terminalBlock] using verified_8_6

    · simpa [terminalBlock] using verified_8_7

    · simpa [terminalBlock] using verified_8_8

    · simpa [terminalBlock] using verified_8_9

  · interval_cases t

    · simpa [terminalBlock] using verified_9_0

    · simpa [terminalBlock] using verified_9_1

    · simpa [terminalBlock] using verified_9_2

    · simpa [terminalBlock] using verified_9_3

    · simpa [terminalBlock] using verified_9_4

    · simpa [terminalBlock] using verified_9_5

    · simpa [terminalBlock] using verified_9_6

    · simpa [terminalBlock] using verified_9_7

    · simpa [terminalBlock] using verified_9_8

    · simpa [terminalBlock] using verified_9_9

  · interval_cases t

    · simpa [terminalBlock] using verified_10_0

    · simpa [terminalBlock] using verified_10_1

    · simpa [terminalBlock] using verified_10_2

    · simpa [terminalBlock] using verified_10_3

    · simpa [terminalBlock] using verified_10_4

    · simpa [terminalBlock] using verified_10_5

    · simpa [terminalBlock] using verified_10_6

    · simpa [terminalBlock] using verified_10_7

    · simpa [terminalBlock] using verified_10_8

    · simpa [terminalBlock] using verified_10_9

  · interval_cases t

    · simpa [terminalBlock] using verified_11_0

    · simpa [terminalBlock] using verified_11_1

    · simpa [terminalBlock] using verified_11_2

    · simpa [terminalBlock] using verified_11_3

    · simpa [terminalBlock] using verified_11_4

    · simpa [terminalBlock] using verified_11_5

    · simpa [terminalBlock] using verified_11_6

    · simpa [terminalBlock] using verified_11_7

    · simpa [terminalBlock] using verified_11_8

    · simpa [terminalBlock] using verified_11_9

  · interval_cases t

    · simpa [terminalBlock] using verified_12_0

    · simpa [terminalBlock] using verified_12_1

    · simpa [terminalBlock] using verified_12_2

    · simpa [terminalBlock] using verified_12_3

    · simpa [terminalBlock] using verified_12_4

    · simpa [terminalBlock] using verified_12_5

    · simpa [terminalBlock] using verified_12_6

    · simpa [terminalBlock] using verified_12_7

    · simpa [terminalBlock] using verified_12_8

    · simpa [terminalBlock] using verified_12_9

  · interval_cases t

    · simpa [terminalBlock] using verified_13_0

    · simpa [terminalBlock] using verified_13_1

    · simpa [terminalBlock] using verified_13_2

    · simpa [terminalBlock] using verified_13_3

    · simpa [terminalBlock] using verified_13_4

    · simpa [terminalBlock] using verified_13_5

    · simpa [terminalBlock] using verified_13_6

    · simpa [terminalBlock] using verified_13_7

    · simpa [terminalBlock] using verified_13_8

    · simpa [terminalBlock] using verified_13_9

/-- Every actual length-two terminal point in this slice is one of two tuples. -/
theorem a_four_d_four_short_terminal_cases (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=4) (ht : ShortTerminal z 2) :
    z=⟨4,6,4,4,6,4⟩ ∨ z=⟨4,11,5,4,4,5⟩ := by
  obtain ⟨bi,t,hbi,htb,hm⟩ := a_four_d_four_mem_block z hz ha hd ht
  rw [verified_blocks bi t hbi htb] at hm
  dsimp [terminalBlock] at hm
  split_ifs at hm
  · exact Or.inl (by simpa using hm)
  · exact Or.inr (by simpa using hm)
  · simp at hm

/-- The two tuples reach their original manuscript representatives by actual words. -/
theorem a_four_d_four_short_terminal_reachable (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=4) (ht : ShortTerminal z 2) :
    ∃ r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  rcases a_four_d_four_short_terminal_cases z hz ha hd ht with h|h
  · refine ⟨0,?_⟩
    rw [h]
    exact PositiveBoundedTable.tuple_reachable (6 : Fin 23)
  · refine ⟨1,?_⟩
    rw [h]
    exact PositiveBoundedTable.tuple_reachable (9 : Fin 23)

/-- Uniqueness uses the already proved integral lattice invariant separation. -/
theorem a_four_d_four_short_terminal_classification (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=4) (ht : ShortTerminal z 2) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨r,hr⟩ := a_four_d_four_short_terminal_reachable z hz ha hd ht
  refine ⟨r,hr,?_⟩
  intro s hs
  exact (PositiveExamples.representatives_reachable_iff s r).mp
    (reachable_trans (reachable_symm hs) hr)

end SerreMarkov.PositiveFourFour
