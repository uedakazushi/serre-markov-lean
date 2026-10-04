import SerreMarkov.NegativeAtLeastTwoReduction
import SerreMarkov.NegativeAdjacentReduction

/-! # Termination at a zero or unit edge, or at the family

The unconditional all-edges-at-least-two reduction is iterated by genuine
strong induction on the original coordinate height. The terminating tuple
is an actual negative solution reached by a finite mutation word.
-/

namespace SerreMarkov.NegativeTinyReduction
open NegativeDescent

def TinyEdge (z : Six) : Prop :=
  |z.a|≤1 ∨ |z.b|≤1 ∨ |z.c|≤1 ∨ |z.d|≤1 ∨ |z.e|≤1 ∨ |z.f|≤1

theorem not_tiny_iff_atLeastTwo (z : Six) : ¬ TinyEdge z ↔
    2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f| := by
  unfold TinyEdge
  omega

theorem negative_reachable_tiny_or_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    (∃ x y : ℤ, Reachable z (family x y)) ∨
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w<0 ∧
      TinyEdge w ∧ l1 w≤l1 z := by
  suffices hind : ∀ n : ℕ, ∀ z : Six, l1 z=n → isSolution z →
      IntrinsicSigns.thirdMinorSum z<0 →
      (∃ x y : ℤ, Reachable z (family x y)) ∨
      ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w<0 ∧
        TinyEdge w ∧ l1 w≤l1 z by
    exact hind (l1 z) z rfl hz hneg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hn hz hneg
    by_cases ht : TinyEdge z
    · exact Or.inr ⟨z,reachable_refl z,hz,hneg,ht,le_rfl⟩
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := (not_tiny_iff_atLeastTwo z).mp ht
    rcases NegativeAtLeastTwoReduction.negative_atLeastTwo_reduction z hz hneg ha hb hc hd he hf with h | h
    · exact Or.inl h
    obtain ⟨word,hdrop⟩ := h
    let w := applyWord z word
    have hr : Reachable z w := ⟨word,rfl⟩
    have hw := reachable_preserves_solution hr hz
    have hwneg := NegativeAdjacentReduction.reachable_negative hz hneg hr
    rcases ih (l1 w) (by change l1 (applyWord z word)<n; omega) w rfl hw hwneg with h | h
    · obtain ⟨x,y,hxy⟩ := h
      exact Or.inl ⟨x,y,reachable_trans hr hxy⟩
    · obtain ⟨v,hrv,hv,hvn,hvt,hvh⟩ := h
      exact Or.inr ⟨v,reachable_trans hr hrv,hv,hvn,hvt,by
        have hwheight : l1 w<l1 z := hdrop
        omega⟩

end SerreMarkov.NegativeTinyReduction
