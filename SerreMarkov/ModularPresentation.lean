import SerreMarkov.ModularCosets
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Tactic

/-!
# The actual integral modular group and its standard generators

The Euclidean algorithm below proves generation of the full matrix group.
The canonical map from the abstract modular presentation to the actual
projective matrix group is then proved surjective, without an assumed
presentation or finite-index theorem.
-/

namespace SerreMarkov.ModularPresentation

open Matrix ModularGroup
open scoped MatrixGroups
attribute [local simp] Matrix.cons_val_two Matrix.vecHead Matrix.vecTail Matrix.one_apply

abbrev SL2Z := SL(2, ℤ)
abbrev PSL2Z := PSL(2, ℤ)

private theorem upper_triangular_mem (H : Subgroup SL2Z) (hS : S ∈ H) (hT : T ∈ H)
    (g : SL2Z) (hc : g 1 0 = 0) : g ∈ H := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    have h := g.property
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using h
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · have hg : g = T ^ (g 0 1) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha, hd, hc]
    rw [hg]
    exact H.zpow_mem hT _
  · have hg : g = S * S * T ^ (-g 0 1) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
          ModularGroup.coe_T_zpow, ha, hd, hc]
    rw [hg]
    exact H.mul_mem (H.mul_mem hS hS) (H.zpow_mem hT _)

/-- The ordinary integer Euclidean algorithm proves that `S,T` generate
every determinant-one integer matrix. -/
theorem SL2Z_generated_by_S_T (H : Subgroup SL2Z) (hS : S ∈ H) (hT : T ∈ H)
    (g : SL2Z) : g ∈ H := by
  suffices hn : ∀ n : ℕ, ∀ g : SL2Z, (g 1 0).natAbs = n → g ∈ H by
    exact hn _ g rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro g hn
      by_cases hc : g 1 0 = 0
      · exact upper_triangular_mem H hS hT g hc
      let q : ℤ := g 0 0 / g 1 0
      let g' : SL2Z := S * T ^ (-q) * g
      have hc' : g' 1 0 = g 0 0 % g 1 0 := by
        simp [g', q, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
          ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def]
        ring
      have hlt : (g' 1 0).natAbs < n := by
        rw [hc', ← hn]
        have h := Int.natAbs_lt_natAbs_of_nonneg_of_lt
          (Int.emod_nonneg (g 0 0) hc) (Int.emod_lt_abs (g 0 0) hc)
        simpa only [Int.natAbs_abs] using h
      have hg' : g' ∈ H := ih _ hlt g' rfl
      have hfac : S * T ^ (-q) ∈ H := H.mul_mem hS (H.zpow_mem hT _)
      have hcancel : g = (S * T ^ (-q))⁻¹ * g' := by simp [g', mul_assoc]
      rw [hcancel]
      exact H.mul_mem (H.inv_mem hfac) hg'

theorem SL2Z_closure_S_T : Subgroup.closure ({S, T} : Set SL2Z) = ⊤ := by
  apply top_unique
  intro g _
  apply SL2Z_generated_by_S_T
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

def project : SL2Z →* PSL2Z := QuotientGroup.mk' (Subgroup.center SL2Z)

def projectiveS : PSL2Z := project S
def projectiveR : PSL2Z := project (S*T)

theorem SL2Z_center_iff (g : SL2Z) :
    g ∈ Subgroup.center SL2Z ↔ g = 1 ∨ g = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  simp only [Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hg⟩
    rcases sq_eq_one_iff.mp hr with rfl | rfl
    · left
      apply Subtype.ext
      simpa using hg.symm
    · right
      apply Subtype.ext
      simpa [Matrix.scalar_apply] using hg.symm
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by simp⟩
    · exact ⟨-1, by norm_num, by ext i j; simp⟩

theorem project_neg_one : project (-1 : SL2Z) = 1 :=
  (QuotientGroup.eq_one_iff (-1 : SL2Z)).mpr ((SL2Z_center_iff _).mpr (Or.inr rfl))

theorem S_square : S ^ 2 = (-1 : SL2Z) := by
  apply Subtype.ext
  simpa only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one] using ModularGroup.S_mul_S_eq

theorem R_cube : (S*T)^3 = (-1 : SL2Z) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
      ModularGroup.coe_T, Matrix.mul_fin_two]

theorem projectiveS_square : projectiveS^2 = 1 := by
  rw [projectiveS, ← map_pow, S_square, project_neg_one]

theorem projectiveR_cube : projectiveR^3 = 1 := by
  rw [projectiveR, ← map_pow, R_cube, project_neg_one]

def presentationGenerators (b : Bool) : PSL2Z := if b then projectiveR else projectiveS

theorem presentation_relations :
    ∀ r ∈ ModularCosets.relations, FreeGroup.lift presentationGenerators r = 1 := by
  intro r hr
  simp only [ModularCosets.relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simpa [map_pow, presentationGenerators] using projectiveS_square
  · simpa [map_pow, presentationGenerators] using projectiveR_cube

def presentationHom : ModularCosets.AbstractGroup →* PSL2Z :=
  PresentedGroup.toGroup presentation_relations

@[simp] theorem presentationHom_s : presentationHom ModularCosets.s = projectiveS := by
  simp [presentationHom, ModularCosets.s, presentationGenerators]

@[simp] theorem presentationHom_t : presentationHom ModularCosets.t = projectiveR := by
  simp [presentationHom, ModularCosets.t, presentationGenerators]

/-- Surjectivity to the actual `SL₂(ℤ)` center quotient is a proved result,
not a hypothesized modular presentation. -/
theorem presentationHom_surjective : Function.Surjective presentationHom := by
  let H : Subgroup SL2Z := presentationHom.range.comap project
  have hS : S ∈ H := ⟨ModularCosets.s, presentationHom_s⟩
  have hT : T ∈ H := by
    refine ⟨ModularCosets.s⁻¹ * ModularCosets.t, ?_⟩
    simp only [map_mul, map_inv, presentationHom_s, presentationHom_t,
      projectiveS, projectiveR]
    simp
  intro g
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL2Z) g
  obtain ⟨a, ha⟩ := SL2Z_generated_by_S_T H hS hT A
  exact ⟨a, ha.trans hA⟩

end SerreMarkov.ModularPresentation
