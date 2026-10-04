import SerreMarkov.ReflectionHurwitz
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The integral reflection group is preserved by mutation

Reflections are represented as units of the integral matrix ring. A Hurwitz
move preserves their generated subgroup, and the actual basis change gives
its conjugation. No chamber or Coxeter-group result is assumed.
-/

namespace SerreMarkov
namespace ReflectionGroup

open Matrix

def unitHurwitzStep {G : Type*} [Group G] (g : Generator)
    (R : Fin 4 → G) : Fin 4 → G :=
  match g with
  | .m1 => fun j => if j = 0 then R 0 * R 1 * (R 0)⁻¹ else if j = 1 then R 0 else R j
  | .m2 => fun j => if j = 1 then R 1 * R 2 * (R 1)⁻¹ else if j = 2 then R 1 else R j
  | .m3 => fun j => if j = 2 then R 2 * R 3 * (R 2)⁻¹ else if j = 3 then R 2 else R j
  | .i1 => fun j => if j = 0 then R 1 else if j = 1 then (R 1)⁻¹ * R 0 * R 1 else R j
  | .i2 => fun j => if j = 1 then R 2 else if j = 2 then (R 2)⁻¹ * R 1 * R 2 else R j
  | .i3 => fun j => if j = 2 then R 3 else if j = 3 then (R 3)⁻¹ * R 2 * R 3 else R j
  | .s1 | .s2 | .s3 | .s4 => R

theorem unitHurwitzStep_inverse {G : Type*} [Group G] (g : Generator) (R : Fin 4 → G) :
    unitHurwitzStep (inverseGenerator g) (unitHurwitzStep g R) = R := by
  funext j
  cases g <;> fin_cases j <;> simp [unitHurwitzStep, inverseGenerator, mul_assoc]

private theorem unitHurwitzStep_mem_closure {G : Type*} [Group G]
    (g : Generator) (R : Fin 4 → G) (j : Fin 4) :
    unitHurwitzStep g R j ∈ Subgroup.closure (Set.range R) := by
  let H := Subgroup.closure (Set.range R)
  have hm (k : Fin 4) : R k ∈ H := Subgroup.subset_closure ⟨k, rfl⟩
  cases g <;> fin_cases j <;> simp only [unitHurwitzStep]
  all_goals first
  | exact hm _
  | exact H.mul_mem (H.mul_mem (hm _) (hm _)) (H.inv_mem (hm _))
  | exact H.mul_mem (H.mul_mem (H.inv_mem (hm _)) (hm _)) (hm _)

private theorem unitHurwitzStep_closure_le {G : Type*} [Group G]
    (g : Generator) (R : Fin 4 → G) :
    Subgroup.closure (Set.range (unitHurwitzStep g R)) ≤ Subgroup.closure (Set.range R) := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨j, rfl⟩
  exact unitHurwitzStep_mem_closure g R j

theorem unitHurwitzStep_closure {G : Type*} [Group G] (g : Generator) (R : Fin 4 → G) :
    Subgroup.closure (Set.range (unitHurwitzStep g R)) = Subgroup.closure (Set.range R) := by
  apply le_antisymm
  · exact unitHurwitzStep_closure_le g R
  · have h := unitHurwitzStep_closure_le (inverseGenerator g) (unitHurwitzStep g R)
    rwa [unitHurwitzStep_inverse] at h

def reflectionUnit (z : Six) (j : Fin 4) : Mat4ˣ :=
  ⟨basisReflection z j, basisReflection z j,
    basisReflection_involution z j, basisReflection_involution z j⟩

@[simp] theorem reflectionUnit_val (z : Six) (j : Fin 4) :
    (reflectionUnit z j : Mat4) = basisReflection z j := rfl

@[simp] theorem reflectionUnit_inv (z : Six) (j : Fin 4) :
    (reflectionUnit z j)⁻¹ = reflectionUnit z j := Units.ext rfl

def reflectionGroup (z : Six) : Subgroup Mat4ˣ :=
  Subgroup.closure (Set.range (reflectionUnit z))

private theorem det_isUnit_of_square (B : Mat4) (hs : B.det ^ 2 = 1) : IsUnit B.det :=
  isUnit_of_mul_eq_one _ _ (by simpa only [pow_two] using hs)

noncomputable def basisStepUnit (g : Generator) (z : Six) : Mat4ˣ :=
  ⟨basisStep g z, (basisStep g z)⁻¹,
    Matrix.mul_nonsing_inv _ (det_isUnit_of_square _ (basisStep_det_sq g z)),
    Matrix.nonsing_inv_mul _ (det_isUnit_of_square _ (basisStep_det_sq g z))⟩

noncomputable def basisWordUnit (z : Six) (word : List Generator) : Mat4ˣ :=
  ⟨basisWord z word, (basisWord z word)⁻¹,
    Matrix.mul_nonsing_inv _ (det_isUnit_of_square _ (basisWord_det_sq z word)),
    Matrix.nonsing_inv_mul _ (det_isUnit_of_square _ (basisWord_det_sq z word))⟩

@[simp] theorem basisStepUnit_val (g : Generator) (z : Six) :
    (basisStepUnit g z : Mat4) = basisStep g z := rfl

@[simp] theorem basisWordUnit_val (z : Six) (word : List Generator) :
    (basisWordUnit z word : Mat4) = basisWord z word := rfl

@[simp] theorem basisWordUnit_nil (z : Six) : basisWordUnit z [] = 1 := Units.ext rfl

theorem basisWordUnit_cons (z : Six) (g : Generator) (word : List Generator) :
    basisWordUnit z (g :: word) = basisStepUnit g z * basisWordUnit (step g z) word :=
  Units.ext rfl

private theorem unitHurwitzStep_reflection_val (g : Generator) (z : Six) (j : Fin 4) :
    (↑(unitHurwitzStep (G := Mat4ˣ) g (reflectionUnit z) j) : Mat4) =
      hurwitzTupleStep g (basisReflection z) j := by
  cases g <;> fin_cases j <;> simp [unitHurwitzStep, hurwitzTupleStep]

theorem basisStepUnit_reflection_hurwitz (g : Generator) (z : Six) (j : Fin 4) :
    basisStepUnit g z * reflectionUnit (step g z) j =
      unitHurwitzStep g (reflectionUnit z) j * basisStepUnit g z := by
  apply Units.ext
  simpa only [Units.val_mul, basisStepUnit_val, reflectionUnit_val,
    unitHurwitzStep_reflection_val] using basisStep_reflection_hurwitz g z j

theorem basisStepUnit_reflection_conjugate (g : Generator) (z : Six) (j : Fin 4) :
    MulAut.conj (basisStepUnit g z) (reflectionUnit (step g z) j) =
      unitHurwitzStep g (reflectionUnit z) j := by
  rw [MulAut.conj_apply, basisStepUnit_reflection_hurwitz]
  simp [mul_assoc]

theorem reflectionGroup_step_conjugate (g : Generator) (z : Six) :
    (reflectionGroup (step g z)).map (MulAut.conj (basisStepUnit g z)).toMonoidHom =
      reflectionGroup z := by
  unfold reflectionGroup
  rw [MonoidHom.map_closure]
  have himage : (MulAut.conj (basisStepUnit g z)).toMonoidHom ''
      Set.range (reflectionUnit (step g z)) =
        Set.range (unitHurwitzStep g (reflectionUnit z)) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext j
    exact basisStepUnit_reflection_conjugate g z j
  rw [himage, unitHurwitzStep_closure]

private theorem conj_mul_hom {G : Type*} [Group G] (B C : G) :
    (MulAut.conj (B * C)).toMonoidHom =
      (MulAut.conj B).toMonoidHom.comp (MulAut.conj C).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem reflectionGroup_word_conjugate (z : Six) (word : List Generator) :
    (reflectionGroup (applyWord z word)).map (MulAut.conj (basisWordUnit z word)).toMonoidHom =
      reflectionGroup z := by
  induction word generalizing z with
  | nil =>
    simp only [applyWord, basisWordUnit_nil, map_one]
    exact Subgroup.map_id _
  | cons g gs ih =>
    rw [applyWord, basisWordUnit_cons, conj_mul_hom, ← Subgroup.map_map, ih]
    exact reflectionGroup_step_conjugate g z

theorem reachable_reflectionGroup_isometric_conjugate {z z' : Six} (hr : Reachable z z') :
    ∃ B : Mat4ˣ, (B : Mat4).det ^ 2 = 1 ∧
      (B : Mat4)ᵀ * gram z * (B : Mat4) = gram z' ∧
      (reflectionGroup z').map (MulAut.conj B).toMonoidHom = reflectionGroup z := by
  obtain ⟨word, hw⟩ := hr
  refine ⟨basisWordUnit z word, ?_, ?_, ?_⟩
  · exact basisWord_det_sq z word
  · rw [← hw]
    exact basisWord_congruence z word
  · rw [← hw]
    exact reflectionGroup_word_conjugate z word

end ReflectionGroup
end SerreMarkov
