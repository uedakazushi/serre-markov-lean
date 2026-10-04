import SerreMarkov.NegativeTinyReduction
import SerreMarkov.NegativeClassification

/-! # Global composition of actual family-or-drop reductions

The step premise is explicit. Its complete boundary implementation is a
separate obligation; this module proves the terminating induction and the
normalization and uniqueness consequences without restricting witness length.
-/

namespace SerreMarkov.NegativeDescentInduction
open NegativeDescent NegativeTwoEdge NegativeClassification

def StepProperty : Prop := ∀ z : Six, isSolution z →
  IntrinsicSigns.thirdMinorSum z<0 → FamilyOrDrop z

theorem negative_family_surjectivity_of_step (hstep : StepProperty)
    (z : Six) (hz : isSolution z) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  suffices hind : ∀ n : ℕ, ∀ z : Six, l1 z=n → isSolution z →
      IntrinsicSigns.thirdMinorSum z<0 → ∃ x y : ℤ, Reachable z (family x y) by
    exact hind (l1 z) z rfl hz hneg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hn hz hneg
    rcases hstep z hz hneg with h | ⟨word,hdrop⟩
    · exact h
    let w := applyWord z word
    have hr : Reachable z w := ⟨word,rfl⟩
    have hw := reachable_preserves_solution hr hz
    have hwn := NegativeAdjacentReduction.reachable_negative hz hneg hr
    obtain ⟨x,y,hxy⟩ := ih (l1 w) (by change l1 (applyWord z word)<n; omega) w rfl hw hwn
    exact ⟨x,y,reachable_trans hr hxy⟩

theorem negative_normalized_existence_of_step (hstep : StepProperty)
    (z : Six) (hz : isSolution z) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃ p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  obtain ⟨x,y,hr⟩ := negative_family_surjectivity_of_step hstep z hz hneg
  have hreg : shiftedSerre z^3≠0 := by
    intro hc
    have hs := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hc
    omega
  have hsum : x+y≠0 := by
    intro hs
    exact hreg ((reachable_shifted_power_zero hr 3).mpr ((family_cube_eq_zero_iff x y).mpr hs))
  obtain ⟨x',y',hnorm,horder,hy,htotal⟩ := family_normalize x y hsum
  refine ⟨(x',y'),⟨hy,horder,?_⟩,reachable_trans hr hnorm⟩
  rw [htotal]
  exact abs_pos.mpr hsum

theorem negative_classification_of_step (hstep : StepProperty)
    (z : Six) (hz : isSolution z) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃! p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  obtain ⟨p,hp,hr⟩ := negative_normalized_existence_of_step hstep z hz hneg
  exact ⟨p,⟨hp,hr⟩,fun q hq => normalized_negative_pair_injective q p hq.1 hp
    (reachable_trans (reachable_symm hq.2) hr)⟩

end SerreMarkov.NegativeDescentInduction
