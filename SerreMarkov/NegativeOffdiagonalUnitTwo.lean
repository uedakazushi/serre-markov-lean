import SerreMarkov.NegativeUnitTwoEdge
import SerreMarkov.CyclicMutation

/-! # A single off-diagonal unit edge with arbitrary signs

The other edges may have absolute value two. A genuine height-preserving
cyclic mutation word moves each of the four unit positions to the proved
first-edge branch.
-/

namespace SerreMarkov.NegativeOffdiagonalUnitTwo
open CyclicMutation NegativeTwoEdge

def SingleOffdiagonalUnitTwo (z : Six) : Prop :=
  (|z.a|=1 ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.c|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.d|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.f|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e|)

theorem single_offdiagonal_unit_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hunit : SingleOffdiagonalUnitTwo z) :
    FamilyOrDrop z := by
  have transfer (n : ℕ)
      (h : |(cyclePower z n).a|=1 ∧ 2≤|(cyclePower z n).b| ∧
        2≤|(cyclePower z n).c| ∧ 2≤|(cyclePower z n).d| ∧
        2≤|(cyclePower z n).e| ∧ 2≤|(cyclePower z n).f|) : FamilyOrDrop z := by
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := h
    exact family_or_drop_transfer z n (NegativeUnitTwoEdge.unit_first_edge_two_reduction _
      (cyclePower_solution z hz n) (cyclePower_negative z hneg n) ha hb hc hd he hf)
  rcases hunit with h | h | h | h
  · exact transfer 0 h
  · obtain ⟨hc,ha,hb,hd,he,hf⟩ := h
    exact transfer 3 (by simpa only [cyclePower,cycle] using And.intro hc ⟨he,hf,ha,hb,hd⟩)
  · obtain ⟨hd,ha,hb,hc,he,hf⟩ := h
    exact transfer 1 (by simpa only [cyclePower,cycle] using And.intro hd ⟨he,ha,hf,hb,hc⟩)
  · obtain ⟨hf,ha,hb,hc,hd,he⟩ := h
    exact transfer 2 (by simpa only [cyclePower,cycle] using And.intro hf ⟨hb,hd,hc,he,ha⟩)

end SerreMarkov.NegativeOffdiagonalUnitTwo
