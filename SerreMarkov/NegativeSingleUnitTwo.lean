import SerreMarkov.BoundaryPatterns
import SerreMarkov.NegativeOffdiagonalUnitTwo
import SerreMarkov.NegativeDiagonalUnitTwo

/-! # Complete all-position reduction with exactly one unit and no zero

All five other pairings may have absolute value two. Every sign and position
is handled by an actual finite word or an actual arithmetic family reduction.
-/

namespace SerreMarkov.NegativeSingleUnitTwo
open NegativeTwoEdge BoundaryPatterns NegativeOffdiagonalUnitTwo

theorem single_unit_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hunit : SingleUnitTwo z) : FamilyOrDrop z := by
  rcases hunit with h | h | h | h | h | h
  · exact single_offdiagonal_unit_two_reduction z hz hneg (Or.inl h)
  · obtain ⟨hb,ha,hc,hd,he,hf⟩ := h
    exact NegativeDiagonalUnitTwo.unit_b_two_family_or_drop z hz hb ha hc hd he hf
  · exact single_offdiagonal_unit_two_reduction z hz hneg (Or.inr (Or.inl h))
  · exact single_offdiagonal_unit_two_reduction z hz hneg (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨he,ha,hb,hc,hd,hf⟩ := h
    exact NegativeDiagonalUnitTwo.unit_e_two_family_or_drop z hz he ha hb hc hd hf
  · exact single_offdiagonal_unit_two_reduction z hz hneg (Or.inr (Or.inr (Or.inr h)))

end SerreMarkov.NegativeSingleUnitTwo
