import SerreMarkov.PositiveSortedTerminal
import SerreMarkov.PositiveSortedThreeLarge
import SerreMarkov.PositiveThreeTerminalUpToEight
import SerreMarkov.PositiveSmallEndpointCensus
import SerreMarkov.PositiveSortedFour

/-! # Classification of ordered terminal chambers with first edge at most four

The large sorted three and four regions are excluded by polynomial
certificates. Their complementary regions are the already exhaustive finite
censuses. No initial height bound is imposed.
-/

namespace SerreMarkov.PositiveSortedTerminalSmall
open PositiveChamber PositiveShortWord PositiveSortedTerminal

theorem first_three_sorted_classification (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hcd : z.d≤z.c) (ht : ShortTerminal z 3) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  have ht2 := shortTerminal_mono (by decide : 2≤3) ht
  rcases PositiveSortedThreeLarge.a_three_sorted_small_boundary z hz ha hcd ht with hd|hf
  · exact PositiveThreeTerminalUpToEight.end_three_middle_upto_eight_terminal_classification
      z hz (Or.inl ha) hd ht2
  · exact PositiveSmallEndpointCensus.small_endpoints_classification_unique z hz
      (by omega) hf ht2

theorem first_edge_le_four_sorted_classification (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 3) (hs : SortedOuter z) (ha : z.a≤4) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  have haLo : 3≤z.a := hz.2.2.1
  have hcases : z.a=3 ∨ z.a=4 := by omega
  rcases hcases with ha3|ha4
  · exact first_three_sorted_classification z hz ha3 hs.2.2.2 ht
  · exact PositiveSortedFour.a_four_sorted_short_terminal_classification z hz ha4
      (by have h := hs.2.1; omega) hs.2.2.2
      (by have h := hs.2.2.1; omega) ht

end SerreMarkov.PositiveSortedTerminalSmall
