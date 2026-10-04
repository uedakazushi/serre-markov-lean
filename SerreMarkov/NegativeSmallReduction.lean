import SerreMarkov.NegativeLargeDescent

/-! # Unconditional termination at a small edge on the negative side

Strong induction on the natural coordinate height iterates the proved
large-edge descent. Every intermediate tuple is reached by an actual finite
mutation word and remains a negative solution. No local-descent hypothesis
is used. Classification of the resulting six boundary cases is separate.
-/

namespace SerreMarkov.NegativeSmallReduction

open NegativeDescent NegativeLargeDescent

/-- One of the six Euler pairings has absolute value at most two. -/
def SmallEdge (z : Six) : Prop :=
  |z.a| ≤ 2 ∨ |z.b| ≤ 2 ∨ |z.c| ≤ 2 ∨ |z.d| ≤ 2 ∨ |z.e| ≤ 2 ∨ |z.f| ≤ 2

theorem not_smallEdge_iff_all_large (z : Six) : ¬ SmallEdge z ↔
    3 ≤ |z.a| ∧ 3 ≤ |z.b| ∧ 3 ≤ |z.c| ∧ 3 ≤ |z.d| ∧ 3 ≤ |z.e| ∧ 3 ≤ |z.f| := by
  unfold SmallEdge
  omega

/-- Repeated strict descent terminates at a small edge, preserving solution
and intrinsic negative sign and never increasing the final height. -/
theorem negative_reachable_small_edge_with_height (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧
      SmallEdge w ∧ l1 w ≤ l1 z := by
  suffices hind : ∀ n : ℕ, ∀ z : Six, l1 z = n → isSolution z →
      IntrinsicSigns.thirdMinorSum z < 0 →
      ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧
        SmallEdge w ∧ l1 w ≤ l1 z by
    exact hind (l1 z) z rfl hz hneg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hn hz hneg
    by_cases hsmall : SmallEdge z
    · exact ⟨z,reachable_refl z,hz,hneg,hsmall,le_rfl⟩
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := (not_smallEdge_iff_all_large z).mp hsmall
    obtain ⟨word,_,_,hdrop⟩ := negative_all_large_word_descent z hz hneg ha hb hc hd he hf
    let w := applyWord z word
    have hr : Reachable z w := ⟨word,rfl⟩
    have hw : isSolution w := reachable_preserves_solution hr hz
    have hk : intrinsicKind z = .negative := (intrinsicKind_negative_iff z hz).mpr hneg
    have hkw : intrinsicKind w = .negative := by
      rw [← reachable_intrinsicKind hz hr]
      exact hk
    have hwneg := (intrinsicKind_negative_iff w hw).mp hkw
    obtain ⟨v,hrv,hv,hvneg,hvsmall,hvheight⟩ :=
      ih (l1 w) (by change l1 (applyWord z word) < n; omega) w rfl hw hwneg
    refine ⟨v,reachable_trans hr hrv,hv,hvneg,hvsmall,?_⟩
    have hwheight : l1 w < l1 z := hdrop
    omega

/-- Every negative solution reaches one of the six small-edge boundary cases. -/
theorem negative_reachable_small_edge (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧ SmallEdge w := by
  obtain ⟨w,hr,hw,hwn,hws,_⟩ := negative_reachable_small_edge_with_height z hz hneg
  exact ⟨w,hr,hw,hwn,hws⟩

/-- An explicit finite-word form of the unconditional termination theorem. -/
theorem negative_finite_word_small_edge (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ word : List Generator, isSolution (applyWord z word) ∧
      IntrinsicSigns.thirdMinorSum (applyWord z word) < 0 ∧
      SmallEdge (applyWord z word) ∧ l1 (applyWord z word) ≤ l1 z := by
  obtain ⟨w,⟨word,hw⟩,hs,hn,hsmall,hheight⟩ := negative_reachable_small_edge_with_height z hz hneg
  exact ⟨word,by simpa only [hw] using hs,by simpa only [hw] using hn,
    by simpa only [hw] using hsmall,by simpa only [hw] using hheight⟩

end SerreMarkov.NegativeSmallReduction
