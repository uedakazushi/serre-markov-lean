import SerreMarkov.DegenerateAlgebra
import SerreMarkov.DegenerateReduction
import SerreMarkov.DegenerateUniqueness
import SerreMarkov.SerreInvariant

/-! # Global surjectivity in the degenerate classification

Vanishing symmetric cofactors and the Pfaffian give an integral presentation
on the Cayley cubic. The proved terminating mutation descent supplies a
normalized representative. No geometric or Coxeter input is assumed.
-/

namespace SerreMarkov

theorem cofactor_zero_reachable_degenerate_family (z : Six)
    (hc : symmetricCofactors z=0) (hq : q2 z= -4) :
    ∃ k : ℤ, 0≤k ∧ Reachable z (family k (-k)) := by
  have hr := cofactor_zero_reduced z hc hq
  have hm : MarkovFour z.a z.b z.d := by
    have h := reducedDegenerate_q2 z.a z.b z.d
    rw [← hr,hq] at h
    dsimp [MarkovFour]
    omega
  rw [hr]
  exact reducedDegenerate_reachable_family z.a z.b z.d hm

/-- Every degenerate solution has a normalized representative, with a genuine
finite mutation word and without a classification hypothesis. -/
theorem degenerate_classification_surjective (z : Six) (hz : isSolution z)
    (h : shiftedSerre z^3=0) :
    ∃ k : ℤ, 0≤k ∧ Reachable z (family k (-k)) := by
  have hf : (q2 z-4)*(q2 z+4)=0 := by nlinarith [hz.2]
  rcases mul_eq_zero.mp hf with hplus | hminus
  · have hq : q2 z=4 := by omega
    have he : isSolution (eps1 z) := step_preserves_solution .s1 z hz
    have he3 : shiftedSerre (eps1 z)^3=0 := by
      rw [shiftedSerre_eps1_pow,h]
      simp
    have heq : q2 (eps1 z)= -4 := by rw [q2_eps1,hq]
    obtain ⟨k,hk,hkreach⟩ := cofactor_zero_reachable_degenerate_family (eps1 z)
      (cofactor_zero_of_cube_zero (eps1 z) he he3) heq
    exact ⟨k,hk,reachable_trans ⟨[.s1],rfl⟩ hkreach⟩
  · have hq : q2 z= -4 := by omega
    exact cofactor_zero_reachable_degenerate_family z
      (cofactor_zero_of_cube_zero z hz h) hq

/-- The normalized degenerate parameter exists and is unique on each signed
mutation orbit. -/
theorem degenerate_classification (z : Six) (hz : isSolution z)
    (h : shiftedSerre z ^ 3 = 0) :
    ∃! k : ℤ, 0 ≤ k ∧ Reachable z (family k (-k)) := by
  obtain ⟨k, hk, hzk⟩ := degenerate_classification_surjective z hz h
  refine ⟨k, ⟨hk, hzk⟩, ?_⟩
  intro l hl
  have hkl := reachable_trans (reachable_symm hzk) hl.2
  exact (degenerate_family_reachable_iff hk hl.1).mp hkl |>.symm

/-- The same unique parameter classifies the underlying integral Euler
lattice, even if the comparison isomorphism is not a mutation word. -/
theorem degenerate_lattice_classification (z : Six) (hz : isSolution z)
    (h : shiftedSerre z ^ 3 = 0) :
    ∃! k : ℤ, 0 ≤ k ∧ LatticeEquivalent z (family k (-k)) := by
  obtain ⟨k, hk, hzk⟩ := degenerate_classification_surjective z hz h
  have hzke := reachable_latticeEquivalent hzk
  refine ⟨k, ⟨hk, hzke⟩, ?_⟩
  intro l hl
  have hkl := latticeEquivalent_trans (latticeEquivalent_symm hzke) hl.2
  exact (degenerate_family_latticeEquivalent_iff hk hl.1).mp hkl |>.symm

theorem degenerate_iff_reachable_family (z : Six) :
    (isSolution z ∧ shiftedSerre z ^ 3 = 0) ↔
      ∃ k : ℤ, 0 ≤ k ∧ Reachable z (family k (-k)) := by
  constructor
  · rintro ⟨hz, h3⟩
    exact degenerate_classification_surjective z hz h3
  · rintro ⟨k, _, hzk⟩
    have h4 := (reachable_shifted_power_zero hzk 4).mpr (family_fourth_power k (-k))
    refine ⟨(solution_iff_fourth_power_zero z).mpr h4, ?_⟩
    apply (reachable_shifted_power_zero hzk 3).mpr
    exact (family_cube_eq_zero_iff k (-k)).mpr (by ring)

theorem degenerate_iff_latticeEquivalent_family (z : Six) :
    (isSolution z ∧ shiftedSerre z ^ 3 = 0) ↔
      ∃ k : ℤ, 0 ≤ k ∧ LatticeEquivalent z (family k (-k)) := by
  constructor
  · rintro ⟨hz, h3⟩
    obtain ⟨k, hk, hzk⟩ := degenerate_classification_surjective z hz h3
    exact ⟨k, hk, reachable_latticeEquivalent hzk⟩
  · rintro ⟨k, _, hzk⟩
    have h4 := (latticeEquivalent_shifted_power_zero hzk 4).mpr
      (family_fourth_power k (-k))
    refine ⟨(solution_iff_fourth_power_zero z).mpr h4, ?_⟩
    apply (latticeEquivalent_shifted_power_zero hzk 3).mpr
    exact (family_cube_eq_zero_iff k (-k)).mpr (by ring)

/-- Integral Euler-lattice isomorphism and signed mutation equivalence agree
on the entire degenerate solution locus. -/
theorem degenerate_latticeEquivalent_iff_reachable {z w : Six}
    (hz : isSolution z) (hw : isSolution w)
    (hz3 : shiftedSerre z ^ 3 = 0) (hw3 : shiftedSerre w ^ 3 = 0) :
    LatticeEquivalent z w ↔ Reachable z w := by
  constructor
  · intro hzw
    obtain ⟨k, hk, hzk⟩ := degenerate_classification_surjective z hz hz3
    obtain ⟨l, hl, hwl⟩ := degenerate_classification_surjective w hw hw3
    have hkl := latticeEquivalent_trans
      (latticeEquivalent_symm (reachable_latticeEquivalent hzk))
      (latticeEquivalent_trans hzw (reachable_latticeEquivalent hwl))
    have hparam := degenerate_family_lattice_injective hk hl hkl
    subst l
    exact reachable_trans hzk (reachable_symm hwl)
  · exact reachable_latticeEquivalent

end SerreMarkov
