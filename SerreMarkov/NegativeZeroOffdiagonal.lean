import SerreMarkov.ZeroIncidentBoundary
import SerreMarkov.NegativeZeroUnitBoundary
import SerreMarkov.NegativeZeroAffineBoundary
import SerreMarkov.NegativeAtLeastTwoReduction

/-! # Complete reduction at any off-diagonal zero edge

All integer branches at a zero first edge are closed. A height-preserving
actual cyclic mutation word transfers the result to the other three edges
in its coordinate orbit. No bound on any remaining coefficient is assumed.
-/

namespace SerreMarkov.NegativeZeroOffdiagonal
open NegativeDescent NegativeTwoEdge CyclicMutation

theorem first_zero_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=0) : FamilyOrDrop z := by
  by_cases hf0 : z.f=0
  · exact Or.inl (NegativeBoundary.two_zero_edges_reachable_family z hz hneg
      (Or.inl ⟨ha,Or.inr (Or.inr (Or.inr (Or.inr hf0)))⟩))
  by_cases hf1 : |z.f|=1
  · exact Or.inl (NegativeZeroUnitBoundary.zero_opposite_unit_reachable_family z hz hneg ha hf1)
  by_cases hf2 : |z.f|=2
  · exact Or.inl (NegativeZeroAffineBoundary.zero_opposite_affine_reachable_family z hz ha hf2)
  have hf : 3≤|z.f| := by
    have hh : 0≤|z.f| := abs_nonneg _
    have hz0 : |z.f|≠0 := by
      intro h
      have hpos := le_abs_self z.f
      have hneg := neg_le_abs z.f
      exact hf0 (by omega)
    omega
  rcases ZeroIncidentBoundary.zero_large_opposite_family_or_drop z hz hneg ha hf with h | h
  · exact Or.inl h
  · obtain ⟨word,_,hdrop⟩ := h
    exact Or.inr ⟨word,hdrop⟩

theorem offdiagonal_zero_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hzero : z.a=0 ∨ z.c=0 ∨ z.d=0 ∨ z.f=0) : FamilyOrDrop z := by
  have transfer (n : ℕ) (ha : (cyclePower z n).a=0) : FamilyOrDrop z := by
    exact family_or_drop_transfer z n (first_zero_family_or_drop _
      (cyclePower_solution z hz n) (cyclePower_negative z hneg n) ha)
  rcases hzero with ha | hc | hd | hf
  · exact first_zero_family_or_drop z hz hneg ha
  · exact transfer 3 (by simpa only [cyclePower_first_three] using hc)
  · exact transfer 1 (by simpa only [cyclePower_first_one] using hd)
  · exact transfer 2 (by simpa only [cyclePower_first_two] using hf)

end SerreMarkov.NegativeZeroOffdiagonal
