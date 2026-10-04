import SerreMarkov.NegativeUnitSmall
import SerreMarkov.NegativeTwoUnitLarge
import SerreMarkov.CyclicMutation
import SerreMarkov.MirrorDescent
import SerreMarkov.SignGaugeDescent

/-! # Transport of every diagonal and adjacent unit pair

Cyclic mutation and reversal cover all eight placements of a diagonal unit and
an adjacent unit. Both transformations transport actual family witnesses and
preserve the original height in the strict-descent alternative.
-/

namespace SerreMarkov.NegativeDiagonalAdjacentUnits

open NegativeDescent NegativeTwoEdge NegativeUnitSmall NegativeDiagonalDescent

private theorem reverse_solution (z : Six) (hz : isSolution z) : isSolution (reverse z) := by
  have hq : q1 (reverse z)=q1 z := by dsimp [reverse,q1]; ring
  exact ⟨hq.trans hz.1,by rw [reverse_q2]; exact hz.2⟩

private theorem reverse_negative (z : Six) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    IntrinsicSigns.thirdMinorSum (reverse z)<0 := by
  have hq : IntrinsicSigns.thirdMinorSum (reverse z)=IntrinsicSigns.thirdMinorSum z := by
    dsimp [reverse,IntrinsicSigns.thirdMinorSum]
    ring
  rw [hq]
  exact hneg

private theorem cycle_ab (z : Six) (n : ℕ) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : |(CyclicMutation.cyclePower z n).a|=1)
    (hb : |(CyclicMutation.cyclePower z n).b|=1)
    (hAB : ∀ w : Six, isSolution w → IntrinsicSigns.thirdMinorSum w<0 →
      |w.a|=1 → |w.b|=1 → FamilyOrDrop w) : FamilyOrDrop z := by
  apply CyclicMutation.family_or_drop_transfer z n
  exact hAB _ (CyclicMutation.cyclePower_solution z hz n)
    (CyclicMutation.cyclePower_negative z hneg n) ha hb

private theorem reverse_cycle_ab (z : Six) (n : ℕ) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : |(CyclicMutation.cyclePower (reverse z) n).a|=1)
    (hb : |(CyclicMutation.cyclePower (reverse z) n).b|=1)
    (hAB : ∀ w : Six, isSolution w → IntrinsicSigns.thirdMinorSum w<0 →
      |w.a|=1 → |w.b|=1 → FamilyOrDrop w) : FamilyOrDrop z := by
  apply MirrorDescent.family_or_drop_reverse z
  exact cycle_ab (reverse z) n (reverse_solution z hz) (reverse_negative z hneg) ha hb hAB

/-- The eight exact placements are reduced to the first-row pair through genuine
word/reversal transport. The supplied first-row result is explicit in this helper. -/
theorem transfer_diagonal_adjacent_unit_cases (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hdiag : |z.b|=1 ∨ |z.e|=1)
    (hadj : |z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1)
    (hAB : ∀ w : Six, isSolution w → IntrinsicSigns.thirdMinorSum w<0 →
      |w.a|=1 → |w.b|=1 → FamilyOrDrop w) : FamilyOrDrop z := by
  rcases hdiag with hb | he
  · rcases hadj with ha | hc | hd | hf
    · exact hAB z hz hneg ha hb
    · apply reverse_cycle_ab z 3 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using hc
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using hb
    · apply reverse_cycle_ab z 1 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using hd
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using hb
    · apply cycle_ab z 2 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hb
  · rcases hadj with ha | hc | hd | hf
    · apply reverse_cycle_ab z 2 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using ha
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle,reverse] using he
    · apply cycle_ab z 3 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he
    · apply cycle_ab z 1 hz hneg _ _ hAB
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd
      · simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he
    · exact reverse_cycle_ab z 0 hz hneg (by simpa [reverse,CyclicMutation.cyclePower] using hf)
        (by simpa [reverse,CyclicMutation.cyclePower] using he) hAB

private theorem signed_ab_reduction_of_large
    (hlarge : ∀ w : Six, isSolution w → IntrinsicSigns.thirdMinorSum w<0 →
      w.a=1 → w.b=1 → 3≤|w.d| → FamilyOrDrop w)
    (z : Six) (hz : isSolution z) (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : |z.a|=1) (hb : |z.b|=1) : FamilyOrDrop z := by
  obtain ⟨s,hs,hsa,hsb,hsc,hr,hh⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  have hw : isSolution (PositiveNormalization.signedSix z s) := reachable_preserves_solution hr hz
  have hn : IntrinsicSigns.thirdMinorSum (PositiveNormalization.signedSix z s)<0 := by
    change negativeMarker (PositiveNormalization.signedSix z s)<0
    rw [SignGaugeDescent.negativeMarker_signedSix z s hs]
    exact hneg
  have ha' : (PositiveNormalization.signedSix z s).a=1 := hsa.trans ha
  have hb' : (PositiveNormalization.signedSix z s).b=1 := hsb.trans hb
  apply familyOrDrop_of_reachable_same_height hr hh
  by_cases hd : 3≤|(PositiveNormalization.signedSix z s).d|
  · exact hlarge _ hw hn ha' hb' hd
  · exact negative_two_units_small_third_family_or_drop _ hw hn
      (by simp [ha']) (by simp [hb']) (by omega)


/-- The first-row signed unit pair always reaches a family or decreases the
original height. The small and large third-edge branches are both proved. -/
theorem signed_ab_unit_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : |z.a|=1) (hb : |z.b|=1) :
    FamilyOrDrop z := by
  apply signed_ab_reduction_of_large _ z hz hneg ha hb
  intro w hw _ ha' hb' hd'
  exact NegativeTwoUnitLarge.two_unit_large_family_or_drop w hw ha' hb' hd'

/-- Every diagonal/adjacent unit placement reduces without any unproved
classification premise; all other coefficients and signs are arbitrary. -/
theorem diagonal_adjacent_units_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hdiag : |z.b|=1 ∨ |z.e|=1)
    (hadj : |z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1) : FamilyOrDrop z := by
  exact transfer_diagonal_adjacent_unit_cases z hz hneg hdiag hadj signed_ab_unit_family_or_drop

end SerreMarkov.NegativeDiagonalAdjacentUnits
