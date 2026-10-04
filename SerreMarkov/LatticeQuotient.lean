import SerreMarkov.Basis
import SerreMarkov.Unbounded
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SerreMarkov

open Matrix

/-- Isomorphism of integral Euler pairings, using an actual integral unit. -/
def LatticeEquivalent (z w : Six) : Prop :=
  ∃ B : Mat4ˣ, (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w

theorem latticeEquivalent_refl (z : Six) : LatticeEquivalent z z := by
  refine ⟨1, ?_⟩
  simp

theorem latticeEquivalent_symm {z w : Six} (h : LatticeEquivalent z w) :
    LatticeEquivalent w z := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B⁻¹, ?_⟩
  rw [← hB]
  calc
    (↑B⁻¹ : Mat4)ᵀ * ((↑B : Mat4)ᵀ * gram z * ↑B) * ↑B⁻¹ =
        ((↑B : Mat4) * ↑B⁻¹)ᵀ * gram z * ((↑B : Mat4) * ↑B⁻¹) := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = gram z := by simp

theorem latticeEquivalent_trans {z w v : Six}
    (hzw : LatticeEquivalent z w) (hwv : LatticeEquivalent w v) :
    LatticeEquivalent z v := by
  obtain ⟨B, hB⟩ := hzw
  obtain ⟨C, hC⟩ := hwv
  refine ⟨B*C, ?_⟩
  calc
    (↑(B*C) : Mat4)ᵀ * gram z * ↑(B*C) =
        (↑C : Mat4)ᵀ * ((↑B : Mat4)ᵀ * gram z * ↑B) * ↑C := by
      simp only [Units.val_mul, Matrix.transpose_mul]
      noncomm_ring
    _ = gram v := by rw [hB, hC]

def latticeSetoid : Setoid Six where
  r := LatticeEquivalent
  iseqv := ⟨latticeEquivalent_refl, latticeEquivalent_symm, latticeEquivalent_trans⟩

theorem latticeEquivalent_of_congruence {z w : Six} (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hB : Bᵀ * gram z * B = gram w) : LatticeEquivalent z w := by
  have hu : IsUnit B.det := by
    rcases hdet with h | h
    · rw [h]; exact isUnit_one
    · rw [h]; exact isUnit_neg_one
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hu
  refine ⟨u, ?_⟩
  simpa only [hu] using hB

theorem reachable_latticeEquivalent {z w : Six} (h : Reachable z w) :
    LatticeEquivalent z w := by
  obtain ⟨B, hdet, hB⟩ := reachable_integral_congruence h
  exact latticeEquivalent_of_congruence B hdet hB

/-- The forgetful map from signed mutation orbits to integral Euler lattices. -/
def forgetfulMap : Quotient reachabilitySetoid → Quotient latticeSetoid :=
  Quotient.map id (fun _ _ h => reachable_latticeEquivalent h)

theorem unbounded_forgetfulMap_fibers (n : ℕ) :
    ∃ L : Quotient latticeSetoid,
      ∃ f : Fin (n+1) → {o : Quotient reachabilitySetoid // forgetfulMap o = L},
        Function.Injective f := by
  let L := Quotient.mk latticeSetoid (Unbounded.reference n)
  have same (i : Fin (n+1)) :
      forgetfulMap (Quotient.mk reachabilitySetoid (Unbounded.representative n i)) = L := by
    apply Quotient.sound
    obtain ⟨B, hdet, hB⟩ := Unbounded.representative_isometric n i
    exact latticeEquivalent_symm (latticeEquivalent_of_congruence B (Or.inl hdet) hB)
  let f : Fin (n+1) → {o : Quotient reachabilitySetoid // forgetfulMap o = L} :=
    fun i => ⟨Quotient.mk reachabilitySetoid (Unbounded.representative n i), same i⟩
  refine ⟨L, f, ?_⟩
  intro i j hij
  exact Unbounded.orbit_map_injective n (congrArg Subtype.val hij)

abbrev Solution := {z : Six // isSolution z}

def solutionSetoid : Setoid Solution := Setoid.comap Subtype.val reachabilitySetoid

/-- The manuscript's forgetful map with its domain restricted to solutions. -/
def solutionForgetfulMap : Quotient solutionSetoid → Quotient latticeSetoid :=
  Quotient.map Subtype.val (fun _ _ h => reachable_latticeEquivalent h)

theorem unbounded_solutionForgetfulMap_fibers (n : ℕ) :
    ∃ L : Quotient latticeSetoid,
      ∃ f : Fin (n+1) → {o : Quotient solutionSetoid // solutionForgetfulMap o = L},
        Function.Injective f := by
  let L := Quotient.mk latticeSetoid (Unbounded.reference n)
  let reps (i : Fin (n+1)) : Solution :=
    ⟨Unbounded.representative n i, Unbounded.representative_solution n i⟩
  have same (i : Fin (n+1)) :
      solutionForgetfulMap (Quotient.mk solutionSetoid (reps i)) = L := by
    apply Quotient.sound
    obtain ⟨B, hdet, hB⟩ := Unbounded.representative_isometric n i
    exact latticeEquivalent_symm (latticeEquivalent_of_congruence B (Or.inl hdet) hB)
  let f : Fin (n+1) → {o : Quotient solutionSetoid // solutionForgetfulMap o = L} :=
    fun i => ⟨Quotient.mk solutionSetoid (reps i), same i⟩
  refine ⟨L, f, ?_⟩
  intro i j hij
  by_contra hne
  exact Unbounded.representatives_pairwise_not_reachable n i j hne
    (Quotient.exact (congrArg Subtype.val hij))

end SerreMarkov
