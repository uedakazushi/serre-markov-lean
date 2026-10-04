import SerreMarkov.PositiveSortedTerminal
import SerreMarkov.PositiveSmallEndpointCensus
import SerreMarkov.PositiveFiveFiveCensus

/-! # The finite boundary of the ordered first-edge-five region -/

namespace SerreMarkov.PositiveSortedFiveBoundary
open PositiveChamber PositiveShortWord PositiveSortedTerminal

theorem bounded_outer_edge_le_four (z : Six) (hz : PositiveBounded.Bounded z) :
    z.a≤4 ∨ z.c≤4 ∨ z.d≤4 ∨ z.f≤4 := by
  have htable : ∀ i : Fin 23, (PositiveBoundedTable.tuple i).a≤4 ∨
      (PositiveBoundedTable.tuple i).c≤4 ∨ (PositiveBoundedTable.tuple i).d≤4 ∨
      (PositiveBoundedTable.tuple i).f≤4 := by decide +kernel
  obtain ⟨i,rfl⟩ := (PositiveBounded.bounded_iff_table z).mp hz
  exact htable i

theorem sorted_small_endpoints_first_le_four (z : Six) (hz : Chamber z)
    (hs : SortedOuter z) (ha : z.a≤5) (hf : z.f≤5) (ht : ShortTerminal z 2) :
    z.a≤4 := by
  have hb := PositiveSmallEndpointCensus.small_endpoints_bounded z hz ha hf ht
  have hsmall := bounded_outer_edge_le_four z hb
  obtain ⟨hac,had,haf,_⟩ := hs
  omega

theorem first_five_sorted_middle_five_impossible (z : Six) (hz : Chamber z)
    (ha : z.a=5) (hd : z.d=5) (hs : SortedOuter z) (ht : ShortTerminal z 2) : False := by
  have h := PositiveFiveFiveCensus.chamber_census z hz ha hd ht
  have hc : z.c=4 := by rw [h]; rfl
  have hmin : z.a≤z.c := hs.1
  omega

theorem first_five_sorted_large_region (z : Six) (hz : Chamber z)
    (ha : z.a=5) (hs : SortedOuter z) (ht : ShortTerminal z 2) :
    6≤z.d ∧ 6≤z.f := by
  have hdc : 5≤z.d := by have h := hs.2.1; omega
  have hfc : 5≤z.f := by have h := hs.2.2.1; omega
  have hdne : z.d≠5 := fun hd => first_five_sorted_middle_five_impossible z hz ha hd hs ht
  have hfne : z.f≠5 := by
    intro hf
    have h := sorted_small_endpoints_first_le_four z hz hs (by omega) (by omega) ht
    omega
  omega

end SerreMarkov.PositiveSortedFiveBoundary
