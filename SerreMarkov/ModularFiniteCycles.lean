import SerreMarkov.ModularPSLCensus
import Mathlib.Dynamics.PeriodicPts.Defs

/-! # Two forward coset cycles force finite index

This treats the existing forward-orbit predicate exactly as defined. For a
surjective map, coverage by two forward orbits makes both seeds periodic, so
the entire type is finite. No index value or geometric area is assumed. -/

namespace SerreMarkov.ModularFiniteCycles

open Function

theorem periodic_seeds_of_two_forward_orbits {α : Type*} (f : α → α)
    (hf : Surjective f) (x y : α)
    (hcover : ∀ z, (∃ n : ℕ, f^[n] x=z) ∨ (∃ n : ℕ, f^[n] y=z)) :
    (∃ nx : ℕ, 0 < nx ∧ IsPeriodicPt f nx x) ∧
      (∃ ny : ℕ, 0 < ny ∧ IsPeriodicPt f ny y) := by
  obtain ⟨u,hu⟩ := hf x
  obtain ⟨v,hv⟩ := hf y
  have step (a b : α) (n : ℕ) (hab : f^[n] a=b) : f^[n+1] a=f b := by
    rw [Function.iterate_succ_apply',hab]
  rcases hcover u with ⟨n,hn⟩ | ⟨n,hn⟩
  · have hx : IsPeriodicPt f (n+1) x := (step x u n hn).trans hu
    rcases hcover v with ⟨m,hm⟩ | ⟨m,hm⟩
    · have hxy : f^[m+1] x=y := (step x v m hm).trans hv
      have hy := hx.apply_iterate (m+1)
      rw [hxy] at hy
      exact ⟨⟨n+1,by omega,hx⟩,⟨n+1,by omega,hy⟩⟩
    · have hy : IsPeriodicPt f (m+1) y := (step y v m hm).trans hv
      exact ⟨⟨n+1,by omega,hx⟩,⟨m+1,by omega,hy⟩⟩
  · have hyx : f^[n+1] y=x := (step y u n hn).trans hu
    rcases hcover v with ⟨m,hm⟩ | ⟨m,hm⟩
    · have hxy : f^[m+1] x=y := (step x v m hm).trans hv
      have hx : IsPeriodicPt f ((n+1)+(m+1)) x := by
        change f^[(n+1)+(m+1)] x=x
        rw [Function.iterate_add_apply,hxy,hyx]
      have hy := hx.apply_iterate (m+1)
      rw [hxy] at hy
      exact ⟨⟨_,by omega,hx⟩,⟨_,by omega,hy⟩⟩
    · have hy : IsPeriodicPt f (m+1) y := (step y v m hm).trans hv
      have hx := hy.apply_iterate (n+1)
      rw [hyx] at hx
      exact ⟨⟨m+1,by omega,hx⟩,⟨m+1,by omega,hy⟩⟩

theorem finite_of_two_forward_orbits {α : Type*} (f : α → α)
    (hf : Surjective f) (x y : α)
    (hcover : ∀ z, (∃ n : ℕ, f^[n] x=z) ∨ (∃ n : ℕ, f^[n] y=z)) : Finite α := by
  obtain ⟨⟨nx,hnx,hx⟩,⟨ny,hny,hy⟩⟩ := periodic_seeds_of_two_forward_orbits f hf x y hcover
  let F : Sum (Fin nx) (Fin ny) → α := fun z =>
    match z with
    | .inl i => f^[i.val] x
    | .inr j => f^[j.val] y
  have hsurj : Surjective F := by
    intro z
    rcases hcover z with ⟨n,hn⟩ | ⟨n,hn⟩
    · refine ⟨Sum.inl ⟨n%nx,Nat.mod_lt _ hnx⟩,?_⟩
      exact (hx.iterate_mod_apply n).trans hn
    · refine ⟨Sum.inr ⟨n%ny,Nat.mod_lt _ hny⟩,?_⟩
      exact (hy.iterate_mod_apply n).trans hn
  exact Finite.of_surjective F hsurj

/-- The existing abstract modular forward-cycle predicate already implies
finite index; this does not assign that index a numerical value. -/
theorem abstract_two_coset_cycles_finiteIndex (H : Subgroup ModularCosets.AbstractGroup)
    (h : ModularCosets.AtMostTwoCosetCycles H) : H.FiniteIndex := by
  obtain ⟨x,y,hcover⟩ := h
  let f : ModularCosets.AbstractGroup ⧸ H → ModularCosets.AbstractGroup ⧸ H :=
    fun q => ModularCosets.s • (ModularCosets.t • q)
  have hf : Surjective f := by
    intro q
    refine ⟨ModularCosets.t⁻¹ • (ModularCosets.s⁻¹ • q),?_⟩
    simp [f]
  letI : Finite (ModularCosets.AbstractGroup ⧸ H) := finite_of_two_forward_orbits f hf x y hcover
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The actual projective modular group's identical predicate has the same
finite-index consequence. -/
theorem actual_two_coset_cycles_finiteIndex (H : Subgroup ModularPresentation.PSL2Z)
    (h : ModularPSLCensus.AtMostTwoCosetCycles H) : H.FiniteIndex := by
  obtain ⟨x,y,hcover⟩ := h
  let f : ModularPresentation.PSL2Z ⧸ H → ModularPresentation.PSL2Z ⧸ H :=
    fun q => ModularPresentation.projectiveS • (ModularPresentation.projectiveR • q)
  have hf : Surjective f := by
    intro q
    refine ⟨ModularPresentation.projectiveR⁻¹ • (ModularPresentation.projectiveS⁻¹ • q),?_⟩
    simp [f]
  letI : Finite (ModularPresentation.PSL2Z ⧸ H) := finite_of_two_forward_orbits f hf x y hcover
  exact Subgroup.finiteIndex_of_finite_quotient

end SerreMarkov.ModularFiniteCycles
