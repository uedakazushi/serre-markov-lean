import SerreMarkov.NegativeClassificationFull
import SerreMarkov.IsometryNecessary

/-! # The full lattice criterion for arbitrary negative solutions

Actual normalized representatives are constructed by the unconditional
classification. The family isometry criterion then transfers back to the
original arbitrary integer Euler lattices.
-/

namespace SerreMarkov.NegativeLatticeCriterion
open Matrix NegativeClassification

theorem latticeEquivalent_iff_integral_congruence (z w : Six) :
    LatticeEquivalent z w ↔ ∃ B : Mat4, (B.det=1 ∨ B.det= -1) ∧
      Bᵀ*gram z*B=gram w := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨(B : Mat4),?_,hB⟩
    have hu : IsUnit (B : Mat4) := ⟨B,rfl⟩
    exact Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  · rintro ⟨B,hdet,hB⟩
    exact latticeEquivalent_of_congruence B hdet hB

theorem normalized_lattice_criterion (z w : Six) (p q : ℤ×ℤ)
    (hp : NormalizedNegativePair p) (hq : NormalizedNegativePair q)
    (hzp : Reachable z (family p.1 p.2)) (hwq : Reachable w (family q.1 q.2)) :
    LatticeEquivalent z w ↔ p.1+p.2=q.1+q.2 ∧
      ∃ t : ℤ, p.1+p.2 ∣ p.2-q.2-2*t ∧ p.1+p.2 ∣ t*(t-p.2) := by
  have hcong : LatticeEquivalent z w ↔
      LatticeEquivalent (family p.1 p.2) (family q.1 q.2) := by
    constructor
    · intro h
      exact latticeEquivalent_trans (latticeEquivalent_symm (reachable_latticeEquivalent hzp))
        (latticeEquivalent_trans h (reachable_latticeEquivalent hwq))
    · intro h
      exact latticeEquivalent_trans (reachable_latticeEquivalent hzp)
        (latticeEquivalent_trans h (latticeEquivalent_symm (reachable_latticeEquivalent hwq)))
  rw [hcong,latticeEquivalent_iff_integral_congruence]
  have h := family_positive_isometry_iff (p.1+p.2) (q.1+q.2) p.2 q.2 hp.2.2 hq.2.2
  simpa using h

/-- Both representative parameters and both exact criteria are supplied for
arbitrary negative solutions, with no classification or descent premise. -/
theorem negative_orbit_and_lattice_criteria (z w : Six) (hz : isSolution z) (hw : isSolution w)
    (hzn : IntrinsicSigns.thirdMinorSum z<0) (hwn : IntrinsicSigns.thirdMinorSum w<0) :
    ∃ p q : ℤ×ℤ, NormalizedNegativePair p ∧ NormalizedNegativePair q ∧
      Reachable z (family p.1 p.2) ∧ Reachable w (family q.1 q.2) ∧
      (Reachable z w ↔ p=q) ∧
      (LatticeEquivalent z w ↔ p.1+p.2=q.1+q.2 ∧
        ∃ t : ℤ, p.1+p.2 ∣ p.2-q.2-2*t ∧ p.1+p.2 ∣ t*(t-p.2)) := by
  obtain ⟨p,hp,hrp⟩ := NegativeClassificationFull.negative_normalized_existence z hz hzn
  obtain ⟨q,hq,hrq⟩ := NegativeClassificationFull.negative_normalized_existence w hw hwn
  exact ⟨p,q,hp,hq,hrp,hrq,
    normalized_representatives_reachable_iff z w p q hp hq hrp hrq,
    normalized_lattice_criterion z w p q hp hq hrp hrq⟩

end SerreMarkov.NegativeLatticeCriterion
