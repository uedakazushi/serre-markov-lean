import SerreMarkov.BoundaryPatterns
import SerreMarkov.NegativeAtLeastTwoReduction
import SerreMarkov.NegativeSingleUnitTwo
import SerreMarkov.NegativeDoubleUnitReduction
import SerreMarkov.ZeroUnitConic
import SerreMarkov.NegativeDescentInduction

/-! # Unconditional classification of every negative integer solution

The coordinate partition is exhaustive for arbitrary integer six-tuples.
Each of its branches is discharged by a genuine family-or-descent proof.
Strong induction on the full six-coordinate height then gives existence, and
the previously established family orbit invariants give uniqueness.
-/

namespace SerreMarkov.NegativeClassificationFull
open NegativeTwoEdge NegativeClassification

theorem negative_step (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) : FamilyOrDrop z := by
  rcases BoundaryPatterns.coordinate_pattern_partition z with hzero | htwo | hsingle | hdouble
  · exact ZeroUnitConic.zero_edge_family_or_drop z hz hneg hzero
  · exact NegativeAtLeastTwoReduction.negative_atLeastTwo_reduction z hz hneg
      htwo.1 htwo.2.1 htwo.2.2.1 htwo.2.2.2.1 htwo.2.2.2.2.1 htwo.2.2.2.2.2
  · exact NegativeSingleUnitTwo.single_unit_two_reduction z hz hneg hsingle
  · exact NegativeDoubleUnitReduction.double_unit_reduction z hz hneg hdouble

theorem negative_family_surjectivity (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃ x y : ℤ, Reachable z (family x y) :=
  NegativeDescentInduction.negative_family_surjectivity_of_step negative_step z hz hneg

theorem negative_normalized_existence (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃ p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) :=
  NegativeDescentInduction.negative_normalized_existence_of_step negative_step z hz hneg

/-- Every negative solution has exactly one normalized family representative. -/
theorem negative_classification (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃! p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) :=
  NegativeDescentInduction.negative_classification_of_step negative_step z hz hneg

/-- The same unique representative determines the invariant parameters in
every primitive integral frame of the source solution. -/
theorem negative_classification_with_invariants (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    ∃! p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) ∧
      ∀ R : IntrinsicFrame.Frame z, IntrinsicFrame.A R = -1 ∧ R.flag.k=p.1+p.2 := by
  obtain ⟨p,⟨hp,hr⟩,hu⟩ := negative_classification z hz hneg
  exact ⟨p,⟨hp,hr,negative_normalized_frame_invariants z p hp hr⟩,
    fun q hq => hu q ⟨hq.1,hq.2.1⟩⟩

theorem negative_frame_A (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (R : IntrinsicFrame.Frame z) :
    IntrinsicFrame.A R = -1 := by
  obtain ⟨p,⟨hp,hr⟩⟩ := negative_normalized_existence z hz hneg
  exact (negative_normalized_frame_invariants z p hp hr R).1

theorem negative_iff_normalized_reachable (z : Six) (hz : isSolution z) :
    IntrinsicSigns.thirdMinorSum z<0 ↔
      ∃ p : ℤ×ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  constructor
  · exact negative_normalized_existence z hz
  · rintro ⟨p,hp,hr⟩
    have hneg : IntrinsicSigns.thirdMinorSum (family p.1 p.2)<0 := by
      simpa using FamilyIntrinsic.family_negative (p.1+p.2) p.2 hp.2.2
    have hk := (intrinsicKind_negative_iff (family p.1 p.2)
      (family_isSolution p.1 p.2)).mpr hneg
    rw [←reachable_intrinsicKind hz hr] at hk
    exact (intrinsicKind_negative_iff z hz).mp hk

end SerreMarkov.NegativeClassificationFull
