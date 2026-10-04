import SerreMarkov.FamilyReflectionBridge
import SerreMarkov.RootWordGeometry
import SerreMarkov.ReflectionWords

namespace SerreMarkov.FamilyReflectionWords

open Matrix UniversalRoot FamilyReflectionBridge RootWordGeometry

theorem group_element_quotient_word (x y : ℤ) (U : Mat4ˣ)
    (hU : U ∈ ReflectionGroup.reflectionGroup (family x y)) :
    ∃ word : List (Fin 3), project * (U : Mat4) = rootWordMatrix x y word * project := by
  obtain ⟨w,hw⟩ := ReflectionWords.reflectionGroup_word_exists (family x y) U hU
  have hv := congrArg (fun A : Mat4ˣ => (A : Mat4)) hw
  dsimp only at hv
  rw [ReflectionWords.reflection_word_matrix] at hv
  refine ⟨(w.map rootIndex).reverse,?_⟩
  rw [← hv, project_reflection_product]
  simp only [rootWordMatrix, List.reverse_reverse, List.map_map, Function.comp_def]

theorem quotient_circle_reflection_word (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4ˣ)
    (hdet : (B : Mat4).det ^ 2 = 1)
    (hcong : (B : Mat4)ᵀ * gram (family (m-y) y) * (B : Mat4) = gram (family (m-y') y'))
    (hgroup : (ReflectionGroup.reflectionGroup (family (m-y') y')).map
      (MulAut.conj B).toMonoidHom = ReflectionGroup.reflectionGroup (family (m-y) y)) :
    let v := quotientMatrix (B : Mat4) *ᵥ rootSeed 2
    ∃ word : List (Fin 3), rootWordMatrix (m-y) y word = rootVectorReflection (m-y) y v := by
  let Q := quotientMatrix (B : Mat4)
  let rt := ReflectionGroup.reflectionUnit (family (m-y') y') 1
  let U : Mat4ˣ := MulAut.conj B rt
  have hrt : rt ∈ ReflectionGroup.reflectionGroup (family (m-y') y') :=
    Subgroup.subset_closure ⟨1,rfl⟩
  have hU : U ∈ ReflectionGroup.reflectionGroup (family (m-y) y) := by
    rw [← hgroup]
    exact Subgroup.mem_map.mpr ⟨rt,hrt,rfl⟩
  obtain ⟨word,hword⟩ := group_element_quotient_word (m-y) y U hU
  have hdet' : (B : Mat4).det = 1 ∨ (B : Mat4).det = -1 := sq_eq_one_iff.mp hdet
  obtain ⟨s,hs,hQB,hq20,hq21,hq22,hqdet⟩ := family_quotient_shape m y y' hm
    (B : Mat4) hdet' hcong
  have hQdet : Q.det ^ 2 = 1 := by
    change (quotientMatrix (B : Mat4)).det ^ 2 = 1
    rw [hqdet]
    calc
      (s ^ 3) ^ 2 = (s ^ 2) ^ 3 := by ring
      _ = 1 := by rw [hs]; norm_num
  have hQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q
    (isUnit_of_mul_eq_one Q.det Q.det (by simpa only [pow_two] using hQdet))
  have hUB : (U : Mat4) * (B : Mat4) =
      (B : Mat4) * basisReflection (family (m-y') y') 1 := by
    have h : U * B = B * rt := by simp [U, MulAut.conj_apply, mul_assoc]
    exact congrArg (fun A : Mat4ˣ => (A : Mat4)) h
  have hinter : rootWordMatrix (m-y) y word * Q = Q * rootReflectionMatrix (m-y') y' 2 := by
    calc
      _ = (rootWordMatrix (m-y) y word * project) * (B : Mat4) * embed := by
        simp only [Q, quotientMatrix, Matrix.mul_assoc]
      _ = project * ((U : Mat4) * (B : Mat4)) * embed := by
        rw [← hword]
        simp only [Matrix.mul_assoc]
      _ = (project * (B : Mat4)) * basisReflection (family (m-y') y') 1 * embed := by
        rw [hUB]
        simp only [Matrix.mul_assoc]
      _ = Q * (rootReflectionMatrix (m-y') y' (rootIndex 1) * project) * embed := by
        rw [hQB]
        change (Q * project) * basisReflection (family (m-y') y') 1 * embed = _
        rw [Matrix.mul_assoc Q project, project_reflection]
      _ = _ := by
        simp only [rootIndex, show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 3 by decide,
          if_false, Matrix.mul_assoc, project_embed, Matrix.mul_one]
  have hQcong := family_quotient_congruence m y y' (B : Mat4) hcong
  have ht := ReflectionRoots.reflection_transport (rootGram (m-y) y) (rootGram (m-y') y') Q hQcong
    (rootSeed 2)
  change Q * rootReflectionMatrix (m-y') y' 2 =
    rootVectorReflection (m-y) y (Q *ᵥ rootSeed 2) * Q at ht
  refine ⟨word,?_⟩
  change rootWordMatrix (m-y) y word = rootVectorReflection (m-y) y (Q *ᵥ rootSeed 2)
  have he := congrArg (fun A : RootMatrix => A * Q⁻¹) (hinter.trans ht)
  simpa only [Matrix.mul_assoc, hQinv, Matrix.mul_one] using he

theorem reachable_circle_root (m y y' : ℤ) (hm : 0 < m) (hx : 2 ≤ m-y) (hy : 2 ≤ y)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) :
    ∃ B : Mat4ˣ, ∃ sign : ℤ, ∃ vertical : List (Fin 3),
      (sign = 1 ∨ sign = -1) ∧ (∀ i ∈ vertical, i ≠ 2) ∧
      (quotientMatrix (B : Mat4) *ᵥ rootSeed 0) 2 = 0 ∧
      UniversalRoot.rootNorm (m-y) y (quotientMatrix (B : Mat4) *ᵥ rootSeed 0) = 2 ∧
      rootPairing (m-y) y (quotientMatrix (B : Mat4) *ᵥ rootSeed 0)
        (rootApply (m-y) y (sign • rootSeed 2) vertical) = -(m-y') := by
  obtain ⟨B,hdet,hcong,hgroup⟩ := ReflectionGroup.reachable_reflectionGroup_isometric_conjugate hr
  let Q := quotientMatrix (B : Mat4)
  let v := Q *ᵥ rootSeed 2
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hdet' : (B : Mat4).det = 1 ∨ (B : Mat4).det = -1 := sq_eq_one_iff.mp hdet
  obtain ⟨s,hs,hQB,hq20,hq21,hq22,hqdet⟩ := family_quotient_shape m y y' hm0
    (B : Mat4) hdet' hcong
  have hv2 : v 2 = 1 ∨ v 2 = -1 := by
    have hv : v 2 = s := by simp [v,Q,Matrix.mulVec,dotProduct,rootSeed,hq22]
    rw [hv]
    exact sq_eq_one_iff.mp hs
  have hQcong := family_quotient_congruence m y y' (B : Mat4) hcong
  have hvnorm : ReflectionRoots.rootNorm (rootGram (m-y) y) v = 2 := by
    rw [ReflectionRoots.rootNorm_transport (rootGram (m-y) y) (rootGram (m-y') y') Q hQcong]
    rw [← rootNorm_eq, rootSeed_norm]
  obtain ⟨w,hw⟩ := quotient_circle_reflection_word m y y' hm0 B hdet hcong hgroup
  change rootWordMatrix (m-y) y w = rootVectorReflection (m-y) y v at hw
  have hn : rootWordMatrix (m-y) y w ≠ 1 := by
    rw [hw]
    exact ReflectionRoots.reflection_ne_one (rootGram (m-y) y) v hvnorm
  have hsq : rootWordMatrix (m-y) y w * rootWordMatrix (m-y) y w = 1 := by
    rw [hw]
    exact ReflectionRoots.reflection_involution (rootGram (m-y) y) v hvnorm
  obtain ⟨p,j,hp⟩ := rootWordMatrix_orderTwo_root (m-y) y hx hy w hn hsq
  have hpnorm : ReflectionRoots.rootNorm (rootGram (m-y) y)
      (rootApply (m-y) y (rootSeed j) p) = 2 := by
    rw [← rootNorm_eq, rootApply_norm, rootSeed_norm]
  have he : v = rootApply (m-y) y (rootSeed j) p ∨ v = -rootApply (m-y) y (rootSeed j) p :=
    ReflectionRoots.integer_reflection_eq_imp_eq_or_neg (rootGram (m-y) y) v
      (rootApply (m-y) y (rootSeed j) p) hvnorm hpnorm (hw.symm.trans hp)
  have hp2 : (rootApply (m-y) y (rootSeed j) p) 2 = 1 ∨
      (rootApply (m-y) y (rootSeed j) p) 2 = -1 := by
    rcases he with he | he
    · simpa only [he] using hv2
    · have hi := congrFun he 2
      rcases hv2 with hv2 | hv2 <;> simp only [Pi.neg_apply] at hi <;> omega
  obtain ⟨hj,sign,vertical,hsgn,hvert,hvertEq⟩ :=
    UniversalReflection.circle_unit_vertical (m-y) y hx hy j p hp2
  have hvEq : ∃ sign' : ℤ, (sign' = 1 ∨ sign' = -1) ∧
      v = rootApply (m-y) y (sign' • rootSeed 2) vertical := by
    rcases he with he | he
    · exact ⟨sign,hsgn,he.trans hvertEq⟩
    · refine ⟨-sign,?_,?_⟩
      · rcases hsgn with hsgn | hsgn <;> simp [hsgn]
      · rw [he,hvertEq]
        rw [show (-sign) • rootSeed 2 = -(sign • rootSeed 2) by simp, rootApply_neg]
  obtain ⟨sign',hsgn',hvEq⟩ := hvEq
  refine ⟨B,sign',vertical,hsgn',hvert,?_,?_,?_⟩
  · simp [Q,Matrix.mulVec,dotProduct,rootSeed,hq20]
  · rw [rootNorm_eq]
    rw [ReflectionRoots.rootNorm_transport (rootGram (m-y) y) (rootGram (m-y') y') Q hQcong]
    rw [← rootNorm_eq, rootSeed_norm]
  · rw [← hvEq, rootPairing_eq_dotProduct]
    have hpair := congrArg (fun A : RootMatrix => A 0 2) hQcong
    simp [Q,v,rootSeed,Matrix.mulVec,Matrix.mul_apply,dotProduct,
      Fin.sum_univ_three,rootGram,Matrix.transpose_apply,Finset.mul_sum,mul_assoc] at hpair ⊢
    linear_combination hpair

end SerreMarkov.FamilyReflectionWords
