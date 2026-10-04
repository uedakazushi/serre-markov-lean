import SerreMarkov.NegativeDescent
import SerreMarkov.Normalize
import SerreMarkov.FamilyUniqueness
import SerreMarkov.FamilyIntrinsic

/-! # Conditional global classification on the negative locus

The single still-unproved hypothesis `NegativeDescent.LocalDescentProperty`
is explicit in every global existence conclusion in this module. It is the
universal integer short-word inequality, not an axiom of the development.
Normalization, uniqueness, and identification of the intrinsic parameters
are proved. This file therefore gives a precise reduction of the negative
global classification to that one local descent statement; it does not assert
the unconditional manuscript classification.
-/

namespace SerreMarkov.NegativeClassification

open IntrinsicFrame IntrinsicSigns IntrinsicUnique FamilyUniqueness

/-- The manuscript's ordered, nonnegative regular parameter region. -/
def NormalizedNegativePair (p : ℤ × ℤ) : Prop :=
  0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ 0 < p.1 + p.2

/-- Global uniqueness of normalized negative parameters is unconditional. -/
theorem normalized_negative_pair_injective (p q : ℤ × ℤ)
    (hp : NormalizedNegativePair p) (hq : NormalizedNegativePair q)
    (hr : Reachable (family p.1 p.2) (family q.1 q.2)) : p = q := by
  obtain ⟨hp0,hpord,hpsum⟩ := hp
  obtain ⟨hq0,hqord,hqsum⟩ := hq
  have hr' : Reachable (family (p.1+p.2-p.2) p.2)
      (family (q.1+q.2-q.2) q.2) := by simpa using hr
  obtain ⟨hm,hy⟩ := normalized_positive_totals_reachable_unique
    (p.1+p.2) (q.1+q.2) p.2 q.2 hpsum hqsum hp0 hq0
    (by omega) (by omega) hr'
  apply Prod.ext
  · omega
  · exact hy

/-- Well-founded descent followed by finite normalization gives existence
of a normalized representative, conditional on the one local inequality. -/
theorem negative_normalized_existence_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty) (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) :
    ∃ p : ℤ × ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  obtain ⟨x,y,hr⟩ :=
    NegativeDescent.local_descent_implies_negative_family_surjectivity hlocal z hz hneg
  have hreg : shiftedSerre z ^ 3 ≠ 0 := by
    intro hc
    have hs := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hc
    omega
  have hsum : x+y ≠ 0 := by
    intro hs
    exact hreg ((reachable_shifted_power_zero hr 3).mpr
      ((family_cube_eq_zero_iff x y).mpr hs))
  obtain ⟨x',y',hnorm,horder,hy,htotal⟩ := family_normalize x y hsum
  refine ⟨(x',y'),⟨hy,horder,?_⟩,reachable_trans hr hnorm⟩
  rw [htotal]
  exact abs_pos.mpr hsum

/-- The negative global classification follows from the explicit local
descent property. All normalization and orbit uniqueness are discharged. -/
theorem negative_classification_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty) (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) :
    ∃! p : ℤ × ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  obtain ⟨p,hp,hr⟩ := negative_normalized_existence_of_local_descent hlocal z hz hneg
  refine ⟨p,⟨hp,hr⟩,?_⟩
  intro q hq
  exact normalized_negative_pair_injective q p hq.1 hp
    (reachable_trans (reachable_symm hq.2) hr)

/-- A normalized family representative identifies the intrinsic invariants
in every primitive Serre frame of the source, without a descent hypothesis. -/
theorem negative_normalized_frame_invariants (z : Six) (p : ℤ × ℤ)
    (hp : NormalizedNegativePair p) (hr : Reachable z (family p.1 p.2))
    (R : Frame z) : A R = -1 ∧ R.flag.k = p.1+p.2 := by
  have hm := hp.2.2
  let S := FamilyIntrinsic.familyFrame (p.1+p.2) p.2 hm
  have hr' : Reachable z (family (p.1+p.2-p.2) p.2) := by simpa using hr
  have h := reachable_frame_invariants R S hr'
  refine ⟨h.2.trans ?_,h.1⟩
  exact FamilyIntrinsic.familyFrame_A (p.1+p.2) p.2 hm

/-- The conditional classification also identifies the unique intrinsic
pair as `(-1, x+y)` for every frame, rather than merely one chosen frame. -/
theorem negative_classification_with_invariants_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty) (z : Six) (hz : isSolution z)
    (hneg : thirdMinorSum z < 0) :
    ∃! p : ℤ × ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) ∧
      ∀ R : Frame z, A R = -1 ∧ R.flag.k = p.1+p.2 := by
  obtain ⟨p,⟨hp,hr⟩,hu⟩ := negative_classification_of_local_descent hlocal z hz hneg
  refine ⟨p,⟨hp,hr,negative_normalized_frame_invariants z p hp hr⟩,?_⟩
  intro q hq
  exact hu q ⟨hq.1,hq.2.1⟩

/-- The representative condition implies the negative marker; the converse
direction uses only the explicit local descent hypothesis. -/
theorem negative_iff_normalized_reachable_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty) (z : Six) (hz : isSolution z) :
    thirdMinorSum z < 0 ↔
      ∃ p : ℤ × ℤ, NormalizedNegativePair p ∧ Reachable z (family p.1 p.2) := by
  constructor
  · exact negative_normalized_existence_of_local_descent hlocal z hz
  · rintro ⟨p,hp,hr⟩
    have hneg : thirdMinorSum (family p.1 p.2) < 0 := by
      simpa using FamilyIntrinsic.family_negative (p.1+p.2) p.2 hp.2.2
    have hk := (intrinsicKind_negative_iff (family p.1 p.2)
      (family_isSolution p.1 p.2)).mpr hneg
    rw [← reachable_intrinsicKind hz hr] at hk
    exact (intrinsicKind_negative_iff z hz).mp hk

/-- Once normalized representatives are given, equality of their parameter
pairs is the exact mutation-orbit criterion, without a global hypothesis. -/
theorem normalized_representatives_reachable_iff (z w : Six) (p q : ℤ × ℤ)
    (hp : NormalizedNegativePair p) (hq : NormalizedNegativePair q)
    (hzp : Reachable z (family p.1 p.2)) (hwq : Reachable w (family q.1 q.2)) :
    Reachable z w ↔ p = q := by
  constructor
  · intro hzw
    exact normalized_negative_pair_injective p q hp hq
      (reachable_trans (reachable_symm hzp) (reachable_trans hzw hwq))
  · intro hpq
    subst q
    exact reachable_trans hzp (reachable_symm hwq)

end SerreMarkov.NegativeClassification
