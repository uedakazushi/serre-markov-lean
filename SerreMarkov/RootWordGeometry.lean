import SerreMarkov.UniversalRoot
import SerreMarkov.UniversalWord
import SerreMarkov.ReflectionRoots
import SerreMarkov.UniversalReflection

namespace SerreMarkov.RootWordGeometry

open Matrix UniversalRoot
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

theorem rootPairing_eq_dotProduct (x y : ℤ) (u v : RootVector) :
    rootPairing x y u v = u ⬝ᵥ (rootGram x y *ᵥ v) := by
  simp [rootPairing, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem rootNorm_eq (x y : ℤ) (u : RootVector) :
    UniversalRoot.rootNorm x y u = ReflectionRoots.rootNorm (rootGram x y) u :=
  rootPairing_eq_dotProduct x y u u

theorem rootGram_symmetric (x y : ℤ) : (rootGram x y)ᵀ = rootGram x y := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rootGram]

@[simp] theorem rootSeed_norm (x y : ℤ) (j : Fin 3) :
    UniversalRoot.rootNorm x y (rootSeed j) = 2 := by
  fin_cases j <;> simp [UniversalRoot.rootNorm, rootPairing, rootSeed, rootGram,
    Fin.sum_univ_three]

theorem rootReflectionMatrix_involution (x y : ℤ) (j : Fin 3) :
    rootReflectionMatrix x y j * rootReflectionMatrix x y j = 1 := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals fin_cases i <;> fin_cases k <;>
    simp [rootReflectionMatrix, rootVectorReflection, rootSeed, rootGram,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply] <;> ring

theorem rootReflectionMatrix_isometry (x y : ℤ) (j : Fin 3) :
    (rootReflectionMatrix x y j)ᵀ * rootGram x y * rootReflectionMatrix x y j =
      rootGram x y := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals fin_cases i <;> fin_cases k <;>
    simp [rootReflectionMatrix, rootVectorReflection, rootSeed, rootGram,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply] <;> ring

@[simp] theorem rootWordMatrix_nil (x y : ℤ) : rootWordMatrix x y [] = 1 := rfl

theorem rootWordMatrix_append (x y : ℤ) (u v : List (Fin 3)) :
    rootWordMatrix x y (u ++ v) = rootWordMatrix x y v * rootWordMatrix x y u := by
  simp [rootWordMatrix, List.reverse_append, List.map_append, List.prod_append]

theorem rootWordMatrix_cons (x y : ℤ) (j : Fin 3) (w : List (Fin 3)) :
    rootWordMatrix x y (j :: w) = rootWordMatrix x y w * rootReflectionMatrix x y j := by
  simp [rootWordMatrix, List.reverse_cons, List.map_append, List.prod_append]

@[simp] theorem rootWordMatrix_singleton (x y : ℤ) (j : Fin 3) :
    rootWordMatrix x y [j] = rootReflectionMatrix x y j := by
  simp [rootWordMatrix_cons]

theorem rootWordMatrix_evaluateReverse (x y : ℤ) (w : List (Fin 3)) :
    rootWordMatrix x y w = UniversalWord.evaluateReverse (rootReflectionMatrix x y) w := by
  have he (u : List (Fin 3)) : UniversalWord.evaluate (rootReflectionMatrix x y) u =
      (u.map (rootReflectionMatrix x y)).prod := by
    induction u with
    | nil => rfl
    | cons a u ih => simp only [UniversalWord.evaluate_cons, List.map_cons, List.prod_cons, ih]
  exact (he w.reverse).symm

theorem rootWordMatrix_isometry (x y : ℤ) (w : List (Fin 3)) :
    (rootWordMatrix x y w)ᵀ * rootGram x y * rootWordMatrix x y w = rootGram x y := by
  induction w with
  | nil => simp
  | cons j w ih =>
      rw [rootWordMatrix_cons, Matrix.transpose_mul]
      calc
        _ = (rootReflectionMatrix x y j)ᵀ *
            ((rootWordMatrix x y w)ᵀ * rootGram x y * rootWordMatrix x y w) *
            rootReflectionMatrix x y j := by noncomm_ring
        _ = _ := by rw [ih, rootReflectionMatrix_isometry]

theorem rootWordMatrix_reverse_mul (x y : ℤ) (w : List (Fin 3)) :
    rootWordMatrix x y w.reverse * rootWordMatrix x y w = 1 := by
  induction w with
  | nil => simp
  | cons j w ih =>
      rw [List.reverse_cons, rootWordMatrix_append, rootWordMatrix_singleton, rootWordMatrix_cons]
      change (rootReflectionMatrix x y j * rootWordMatrix x y w.reverse) *
        (rootWordMatrix x y w * rootReflectionMatrix x y j) = 1
      calc
        _ = rootReflectionMatrix x y j *
            (rootWordMatrix x y w.reverse * rootWordMatrix x y w) *
            rootReflectionMatrix x y j := by noncomm_ring
        _ = _ := by rw [ih]; simp [rootReflectionMatrix_involution]

theorem rootWordMatrix_mul_reverse (x y : ℤ) (w : List (Fin 3)) :
    rootWordMatrix x y w * rootWordMatrix x y w.reverse = 1 := by
  simpa using rootWordMatrix_reverse_mul x y w.reverse

theorem rootWordMatrix_reduce (x y : ℤ) (w : List (Fin 3)) :
    rootWordMatrix x y (UniversalWord.reduce w) = rootWordMatrix x y w := by
  simp only [rootWordMatrix_evaluateReverse]
  exact UniversalWord.evaluateReverse_reduce (rootReflectionMatrix x y)
    (rootReflectionMatrix_involution x y) w

theorem rootApply_norm (x y : ℤ) (v : RootVector) (w : List (Fin 3)) :
    UniversalRoot.rootNorm x y (rootApply x y v w) = UniversalRoot.rootNorm x y v := by
  rw [rootNorm_eq, rootNorm_eq, ← rootWordMatrix_mulVec]
  exact ReflectionRoots.rootNorm_transport (rootGram x y) (rootGram x y)
    (rootWordMatrix x y w) (rootWordMatrix_isometry x y w) v

theorem rootWordMatrix_reflection_conjugate (x y : ℤ) (p : List (Fin 3)) (j : Fin 3) :
    rootWordMatrix x y p.reverse * rootReflectionMatrix x y j * rootWordMatrix x y p =
      rootVectorReflection x y (rootApply x y (rootSeed j) p.reverse) := by
  have ht := ReflectionRoots.reflection_transport (rootGram x y) (rootGram x y)
    (rootWordMatrix x y p.reverse) (rootWordMatrix_isometry x y p.reverse) (rootSeed j)
  change rootWordMatrix x y p.reverse * rootReflectionMatrix x y j =
    rootVectorReflection x y (rootWordMatrix x y p.reverse *ᵥ rootSeed j) *
      rootWordMatrix x y p.reverse at ht
  rw [ht, Matrix.mul_assoc, rootWordMatrix_reverse_mul, Matrix.mul_one,
    rootWordMatrix_mulVec]

theorem rootWordMatrix_orderTwo_root (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (w : List (Fin 3)) (hne : rootWordMatrix x y w ≠ 1)
    (hsquare : rootWordMatrix x y w * rootWordMatrix x y w = 1) :
    ∃ p : List (Fin 3), ∃ j : Fin 3,
      rootWordMatrix x y w = rootVectorReflection x y (rootApply x y (rootSeed j) p) := by
  have hf (v : List (Fin 3)) (hv : UniversalWord.Reduced v)
      (he : UniversalWord.evaluateReverse (rootReflectionMatrix x y) v = 1) : v = [] := by
    by_contra hn
    exact UniversalReflection.rootWordMatrix_faithful_reduced x y hx hy v hv hn
      (by simpa only [rootWordMatrix_evaluateReverse] using he)
  have hn' : UniversalWord.evaluateReverse (rootReflectionMatrix x y) w ≠ 1 := by
    simpa only [rootWordMatrix_evaluateReverse] using hne
  have hs' : UniversalWord.evaluateReverse (rootReflectionMatrix x y) w *
      UniversalWord.evaluateReverse (rootReflectionMatrix x y) w = 1 := by
    simpa only [rootWordMatrix_evaluateReverse] using hsquare
  obtain ⟨p,j,hp⟩ := UniversalWord.orderTwo_reverse_conjugate_of_faithful
    (rootReflectionMatrix x y) (rootReflectionMatrix_involution x y) hf w hn' hs'
  refine ⟨p.reverse,j,?_⟩
  rw [← rootWordMatrix_reduce, hp, rootWordMatrix_append, rootWordMatrix_append]
  rw [rootWordMatrix_singleton]
  change rootWordMatrix x y p.reverse * (rootReflectionMatrix x y j * rootWordMatrix x y p) = _
  rw [← Matrix.mul_assoc, rootWordMatrix_reflection_conjugate]

end SerreMarkov.RootWordGeometry
