import SerreMarkov.ModularPingPong

/-!
# The five index-twelve classes in the actual projective modular group

The proved presentation isomorphism transports the finite coset census to the
actual center quotient `PSL₂(ℤ)`. All coset-action hypotheses stay explicit:
index twelve, no fixed points of `S` or `R`, and at most two cycles of `S*R`.
No geometric criterion for those hypotheses is assumed here.
-/

namespace SerreMarkov.ModularPSLCensus

open ModularPresentation ModularPingPong

noncomputable section

/-- The actual coset bijection induced by a group isomorphism and a pullback subgroup. -/
def pullbackCosetEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G') : (G ⧸ H.comap e.toMonoidHom) ≃ (G' ⧸ H) :=
  Quotient.congr e.toEquiv fun x y => by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap]
    change e (x⁻¹*y) ∈ H ↔ (e x)⁻¹*e y ∈ H
    rw [map_mul, map_inv]

@[simp] theorem pullbackCosetEquiv_mk {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G') (g : G) :
    pullbackCosetEquiv e H (QuotientGroup.mk g) = QuotientGroup.mk (e g) := rfl

theorem pullbackCosetEquiv_smul {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G') (g : G) (q : G ⧸ H.comap e.toMonoidHom) :
    pullbackCosetEquiv e H (g • q) = e g • pullbackCosetEquiv e H q := by
  induction q using Quotient.inductionOn' with
  | h a => change QuotientGroup.mk (e (g*a)) = (QuotientGroup.mk (e g*e a) : G' ⧸ H)
           rw [map_mul]

/-- The actual coset bijection induced by a group isomorphism and an image subgroup. -/
def imageCosetEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) : (G ⧸ H) ≃ (G' ⧸ H.map e.toMonoidHom) :=
  Quotient.congr e.toEquiv fun x y => by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_map_equiv]
    change x⁻¹*y ∈ H ↔ e.symm ((e x)⁻¹*e y) ∈ H
    rw [← map_inv, ← map_mul, e.symm_apply_apply]

@[simp] theorem imageCosetEquiv_mk {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (g : G) :
    imageCosetEquiv e H (QuotientGroup.mk g) = QuotientGroup.mk (e g) := rfl

theorem imageCosetEquiv_smul {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (g : G) (q : G ⧸ H) :
    imageCosetEquiv e H (g • q) = e g • imageCosetEquiv e H q := by
  induction q using Quotient.inductionOn' with
  | h a => change QuotientGroup.mk (e (g*a)) =
             (QuotientGroup.mk (e g*e a) : G' ⧸ H.map e.toMonoidHom)
           rw [map_mul]

def pullbackSubgroup (H : Subgroup PSL2Z) : Subgroup ModularCosets.AbstractGroup :=
  H.comap presentationPSLEquiv.toMonoidHom

def representativeSubgroup (r : Fin 5) : Subgroup PSL2Z :=
  (ModularCosets.representativeSubgroup r).map presentationPSLEquiv.toMonoidHom

theorem pullbackSubgroup_index (H : Subgroup PSL2Z) :
    (pullbackSubgroup H).index = H.index :=
  H.index_comap_of_surjective presentationPSLEquiv.surjective

theorem representativeSubgroup_index (r : Fin 5) : (representativeSubgroup r).index = 12 := by
  exact (Subgroup.index_map_equiv (ModularCosets.representativeSubgroup r)
    presentationPSLEquiv).trans (ModularCosets.representativeSubgroup_index r)

/-- The coset-cycle generator is exactly the image of the standard translation matrix. -/
theorem projectiveS_mul_R : projectiveS * projectiveR = project ModularGroup.T := by
  rw [projectiveS, projectiveR, ← map_mul, ← mul_assoc, ← pow_two, S_square,
    map_mul, project_neg_one, one_mul]

/-- At most two forward coset orbits of the actual parabolic `S*R`. -/
def AtMostTwoCosetCycles (H : Subgroup PSL2Z) : Prop :=
  ∃ x y : PSL2Z ⧸ H, ∀ z : PSL2Z ⧸ H,
    (∃ n : ℕ, (fun q : PSL2Z ⧸ H => projectiveS • (projectiveR • q))^[n] x = z) ∨
    (∃ n : ℕ, (fun q : PSL2Z ⧸ H => projectiveS • (projectiveR • q))^[n] y = z)

private theorem pullback_generator_free (H : Subgroup PSL2Z)
    (g : ModularCosets.AbstractGroup)
    (h : ∀ q : PSL2Z ⧸ H, presentationPSLEquiv g • q ≠ q) :
    ∀ q : ModularCosets.AbstractGroup ⧸ pullbackSubgroup H, g • q ≠ q := by
  intro q hq
  have he := congrArg (pullbackCosetEquiv presentationPSLEquiv H) hq
  rw [pullbackCosetEquiv_smul] at he
  exact h _ he

private theorem pullback_two_cycles (H : Subgroup PSL2Z) (h : AtMostTwoCosetCycles H) :
    ModularCosets.AtMostTwoCosetCycles (pullbackSubgroup H) := by
  let E := pullbackCosetEquiv presentationPSLEquiv H
  have hi : ∀ q, E (ModularCosets.s • (ModularCosets.t • q)) =
      projectiveS • (projectiveR • E q) := by
    intro q
    simp only [E, pullbackCosetEquiv_smul, presentationPSLEquiv_s, presentationPSLEquiv_t]
  obtain ⟨x,y,hxy⟩ := h
  refine ⟨E.symm x, E.symm y, ?_⟩
  intro z
  rcases hxy (E z) with ⟨n,hn⟩ | ⟨n,hn⟩
  · left
    refine ⟨n, E.injective ?_⟩
    exact (ModularCosets.equiv_iterates E
      (fun q => ModularCosets.s • (ModularCosets.t • q))
      (fun q : PSL2Z ⧸ H => projectiveS • (projectiveR • q)) hi n (E.symm x)).trans
      (by simpa only [E.apply_symm_apply] using hn)
  · right
    refine ⟨n, E.injective ?_⟩
    exact (ModularCosets.equiv_iterates E
      (fun q => ModularCosets.s • (ModularCosets.t • q))
      (fun q : PSL2Z ⧸ H => projectiveS • (projectiveR • q)) hi n (E.symm y)).trans
      (by simpa only [E.apply_symm_apply] using hn)

/-- Every transported representative genuinely satisfies the actual coset conditions. -/
theorem representativeSubgroup_admissible (r : Fin 5) :
    (representativeSubgroup r).index = 12 ∧
      (∀ q : PSL2Z ⧸ representativeSubgroup r, projectiveS • q ≠ q) ∧
      (∀ q : PSL2Z ⧸ representativeSubgroup r, projectiveR • q ≠ q) ∧
      AtMostTwoCosetCycles (representativeSubgroup r) := by
  obtain ⟨_,hs,ht,htwo⟩ := ModularCosets.representativeSubgroup_admissible r
  let E := imageCosetEquiv presentationPSLEquiv (ModularCosets.representativeSubgroup r)
  have hi : ∀ q, E (ModularCosets.s • (ModularCosets.t • q)) =
      projectiveS • (projectiveR • E q) := by
    intro q
    simp only [E, imageCosetEquiv_smul, presentationPSLEquiv_s, presentationPSLEquiv_t]
  refine ⟨representativeSubgroup_index r, ?_, ?_, ?_⟩
  · intro q hq
    apply hs (E.symm q)
    apply E.injective
    rw [imageCosetEquiv_smul, presentationPSLEquiv_s]
    change projectiveS • E (E.symm q) = E (E.symm q)
    simpa only [E.apply_symm_apply] using hq
  · intro q hq
    apply ht (E.symm q)
    apply E.injective
    rw [imageCosetEquiv_smul, presentationPSLEquiv_t]
    change projectiveR • E (E.symm q) = E (E.symm q)
    simpa only [E.apply_symm_apply] using hq
  · obtain ⟨x,y,hxy⟩ := htwo
    refine ⟨E x, E y, ?_⟩
    intro q
    rcases hxy (E.symm q) with ⟨n,hn⟩ | ⟨n,hn⟩
    · left
      refine ⟨n, ?_⟩
      exact (ModularCosets.equiv_iterates E
        (fun q => ModularCosets.s • (ModularCosets.t • q))
        (fun q => projectiveS • (projectiveR • q)) hi n x).symm.trans
        ((congrArg E hn).trans (E.apply_symm_apply q))
    · right
      refine ⟨n, ?_⟩
      exact (ModularCosets.equiv_iterates E
        (fun q => ModularCosets.s • (ModularCosets.t • q))
        (fun q => projectiveS • (projectiveR • q)) hi n y).symm.trans
        ((congrArg E hn).trans (E.apply_symm_apply q))

/-- Taking the image along an isomorphism commutes with actual subgroup conjugation. -/
theorem image_conjugate {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem pullback_conjugate (H : Subgroup PSL2Z) (r : Fin 5) (g : PSL2Z)
    (hg : H = (representativeSubgroup r).map (MulAut.conj g).toMonoidHom) :
    ∃ a : ModularCosets.AbstractGroup, pullbackSubgroup H =
      (ModularCosets.representativeSubgroup r).map (MulAut.conj a).toMonoidHom := by
  refine ⟨presentationPSLEquiv.symm g, ?_⟩
  apply Subgroup.map_injective (f := presentationPSLEquiv.toMonoidHom)
    presentationPSLEquiv.injective
  have hmap : (pullbackSubgroup H).map presentationPSLEquiv.toMonoidHom = H :=
    Subgroup.map_comap_eq_self_of_surjective (f := presentationPSLEquiv.toMonoidHom)
      presentationPSLEquiv.surjective H
  rw [hmap, image_conjugate presentationPSLEquiv, presentationPSLEquiv.apply_symm_apply]
  exact hg

/-- Every actual `PSL₂(ℤ)` subgroup with the stated coset conditions lies in a unique one
of the five actual conjugacy classes. -/
theorem subgroup_census_unique (H : Subgroup PSL2Z) (hindex : H.index = 12)
    (hs : ∀ q : PSL2Z ⧸ H, projectiveS • q ≠ q)
    (ht : ∀ q : PSL2Z ⧸ H, projectiveR • q ≠ q) (htwo : AtMostTwoCosetCycles H) :
    ∃! r : Fin 5, ∃ g : PSL2Z,
      H = (representativeSubgroup r).map (MulAut.conj g).toMonoidHom := by
  have hindex' : (pullbackSubgroup H).index = 12 :=
    (pullbackSubgroup_index H).trans hindex
  have hs' := pullback_generator_free H ModularCosets.s
    (by simpa only [presentationPSLEquiv_s] using hs)
  have ht' := pullback_generator_free H ModularCosets.t
    (by simpa only [presentationPSLEquiv_t] using ht)
  obtain ⟨r,⟨g,hg⟩,hunique⟩ := ModularCosets.abstract_subgroup_census_unique
    (pullbackSubgroup H) hindex' hs' ht' (pullback_two_cycles H htwo)
  refine ⟨r, ⟨presentationPSLEquiv g, ?_⟩, ?_⟩
  · have he := congrArg (Subgroup.map presentationPSLEquiv.toMonoidHom) hg
    have hmap : (pullbackSubgroup H).map presentationPSLEquiv.toMonoidHom = H :=
      Subgroup.map_comap_eq_self_of_surjective (f := presentationPSLEquiv.toMonoidHom)
        presentationPSLEquiv.surjective H
    rw [hmap, image_conjugate presentationPSLEquiv] at he
    exact he
  · intro r' hr'
    obtain ⟨g',hg'⟩ := hr'
    exact hunique r' (pullback_conjugate H r' g' hg')

/-- The five transported representatives are pairwise nonconjugate in the actual PSL group. -/
theorem representativeSubgroups_conjugate_iff (r r' : Fin 5) :
    (∃ g : PSL2Z, representativeSubgroup r =
      (representativeSubgroup r').map (MulAut.conj g).toMonoidHom) ↔ r = r' := by
  constructor
  · rintro ⟨g,hg⟩
    apply (ModularCosets.representativeSubgroups_conjugate_iff r r').mp
    refine ⟨presentationPSLEquiv.symm g, ?_⟩
    apply Subgroup.map_injective (f := presentationPSLEquiv.toMonoidHom)
      presentationPSLEquiv.injective
    rw [image_conjugate presentationPSLEquiv, presentationPSLEquiv.apply_symm_apply]
    exact hg
  · rintro rfl
    refine ⟨1, ?_⟩
    have he : (MulAut.conj (1 : PSL2Z)).toMonoidHom = MonoidHom.id PSL2Z := by
      ext g
      simp
    rw [he, Subgroup.map_id]

end
end SerreMarkov.ModularPSLCensus
