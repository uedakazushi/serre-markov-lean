import SerreMarkov.UniversalRoot
import SerreMarkov.IsometryNecessary
import SerreMarkov.ReflectionGroup

/-! # Integral three-root quotient of a family lattice

The quotient projection sends the two coincident middle roots to root `2`.
The two outer roots become roots `0,1`.  All formulas use integral matrices.
-/

namespace SerreMarkov.FamilyReflectionBridge

open Matrix UniversalRoot
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

def project : Matrix (Fin 3) (Fin 4) ℤ :=
  !![1,0,0,0; 0,0,0,1; 0,1,1,0]

def embed : Matrix (Fin 4) (Fin 3) ℤ :=
  !![1,0,0; 0,0,1; 0,0,0; 0,1,0]

def rootIndex (j : Fin 4) : Fin 3 := if j = 0 then 0 else if j = 3 then 1 else 2

def quotientMatrix (B : Mat4) : RootMatrix := project * B * embed

theorem project_embed : project * embed = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [project, embed, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem family_symmetric_quotient (x y : ℤ) :
    symmetricForm (family x y) = projectᵀ * rootGram x y * project := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricForm, gram, family, project, rootGram,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem project_reflection (x y : ℤ) (j : Fin 4) :
    project * basisReflection (family x y) j =
      rootReflectionMatrix x y (rootIndex j) * project := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals fin_cases i <;> fin_cases k <;>
    simp [project, basisReflection, symmetricForm, gram, family, rootIndex,
      rootReflectionMatrix, rootVectorReflection, rootSeed, rootGram,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem project_reflection_product (x y : ℤ) (word : List (Fin 4)) :
    project * (word.map (basisReflection (family x y))).prod =
      ((word.map (fun j => rootReflectionMatrix x y (rootIndex j))).prod) * project := by
  induction word with
  | nil => simp
  | cons j w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← Matrix.mul_assoc, project_reflection, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

private theorem adapted_inverse_mul_basis (y : ℤ) :
    adaptedBasisInverse y * adaptedBasis y = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [adaptedBasisInverse, adaptedBasis, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem actual_adapted_congruence (m y y' : ℤ) (B : Mat4)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) :
    let T := adaptedBasisInverse y * B * adaptedBasis y'
    Tᵀ * adaptedGram m y * T = adaptedGram m y' := by
  dsimp
  calc
    _ = (adaptedBasis y')ᵀ * Bᵀ *
        ((adaptedBasisInverse y)ᵀ * adaptedGram m y * adaptedBasisInverse y) *
        B * adaptedBasis y' := by
          simp only [Matrix.transpose_mul]
          noncomm_ring
    _ = (adaptedBasis y')ᵀ * (Bᵀ * gram (family (m-y) y) * B) *
        adaptedBasis y' := by
          have hmid : (adaptedBasisInverse y)ᵀ * adaptedGram m y * adaptedBasisInverse y =
              gram (family (m-y) y) := by
            rw [← adaptedBasis_congruence m y]
            calc
              _ = (adaptedBasis y * adaptedBasisInverse y)ᵀ *
                  gram (family (m-y) y) * (adaptedBasis y * adaptedBasisInverse y) := by
                    rw [Matrix.transpose_mul]
                    noncomm_ring
              _ = _ := by rw [adaptedBasis_mul_inverse]; simp
          rw [hmid]
          noncomm_ring
    _ = _ := by rw [hcong, adaptedBasis_congruence]

theorem family_isometry_actual_shape (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) :
    ∃ s r a g b h k : ℤ, s ^ 2 = 1 ∧
      B = adaptedBasis y *
        !![s,0,0,0; r,s,0,0; a,g,s,0; b,h,k,s] * adaptedBasisInverse y' := by
  let T := adaptedBasisInverse y * B * adaptedBasis y'
  have hTdet : T.det = B.det := by
    simp [T, Matrix.det_mul, adaptedBasisInverse_det, adaptedBasis_det]
  have hTcong := actual_adapted_congruence m y y' B hcong
  change Tᵀ * adaptedGram m y * T = adaptedGram m y' at hTcong
  have hTunit : T.det = 1 ∨ T.det = -1 := hTdet ▸ hdet
  obtain ⟨s,r,a,g,b,h,k,hs,hshape⟩ := adapted_isometry_lower_shape
    m y y' hm T hTunit (adaptedN_intertwine m y y' T hTunit hTcong)
  refine ⟨s,r,a,g,b,h,k,hs,?_⟩
  rw [← hshape]
  dsimp [T]
  symm
  calc
    _ = (adaptedBasis y * adaptedBasisInverse y) * B *
        (adaptedBasis y' * adaptedBasisInverse y') := by noncomm_ring
    _ = B := by rw [adaptedBasis_mul_inverse, adaptedBasis_mul_inverse]; simp

set_option maxHeartbeats 0 in
theorem project_adapted_lower (y y' s r a g b h k : ℤ) :
    project * (adaptedBasis y *
      !![s,0,0,0; r,s,0,0; a,g,s,0; b,h,k,s] * adaptedBasisInverse y') =
    !![s-g, a-r-s*y-y'*(g-s), a-r-s*y-y'*(g-s), g;
      -g, a-g*y', a-g*y', g+s; 0,s,s,0] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [project, adaptedBasis, adaptedBasisInverse, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

theorem family_quotient_shape (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) :
    ∃ s : ℤ, s ^ 2 = 1 ∧
      project * B = quotientMatrix B * project ∧
      (quotientMatrix B) 2 0 = 0 ∧ (quotientMatrix B) 2 1 = 0 ∧
      (quotientMatrix B) 2 2 = s ∧ (quotientMatrix B).det = s ^ 3 := by
  obtain ⟨s,r,a,g,b,h,k,hs,hB⟩ := family_isometry_actual_shape m y y' hm B hdet hcong
  have hPB := project_adapted_lower y y' s r a g b h k
  rw [← hB] at hPB
  have hQ : quotientMatrix B =
      !![s-g,g,a-r-s*y-y'*(g-s); -g,g+s,a-g*y'; 0,0,s] := by
    rw [quotientMatrix, hPB]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [embed, Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨s,hs,?_,?_,?_,?_,?_⟩
  · rw [hPB, hQ]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [project, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [hQ]
  · simp [hQ]
  · simp [hQ]
  · simp [hQ, Matrix.det_fin_three]
    ring

theorem family_quotient_congruence (m y y' : ℤ) (B : Mat4)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) :
    (quotientMatrix B)ᵀ * rootGram (m-y) y * quotientMatrix B = rootGram (m-y') y' := by
  have hsym : Bᵀ * symmetricForm (family (m-y) y) * B =
      symmetricForm (family (m-y') y') := by
    have ht := congrArg Matrix.transpose hcong
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at ht
    simp only [symmetricForm, Matrix.mul_add, Matrix.add_mul, hcong, ht]
  calc
    _ = embedᵀ * (Bᵀ * symmetricForm (family (m-y) y) * B) * embed := by
      rw [family_symmetric_quotient]
      simp only [quotientMatrix, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = embedᵀ * symmetricForm (family (m-y') y') * embed := by rw [hsym]
    _ = (project * embed)ᵀ * rootGram (m-y') y' * (project * embed) := by
      rw [family_symmetric_quotient]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [project_embed]; simp

end SerreMarkov.FamilyReflectionBridge
