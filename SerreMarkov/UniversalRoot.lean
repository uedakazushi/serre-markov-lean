import Mathlib.Tactic

/-! # Shared three-root reflection coordinates

Indices `0,1` are the two vertical roots and index `2` is the circle root.
Words in `rootApply` are read from left to right: the first letter acts first.
-/

namespace SerreMarkov.UniversalRoot

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

abbrev RootVector := Fin 3 → ℤ
abbrev RootMatrix := Matrix (Fin 3) (Fin 3) ℤ

def rootGram (x y : ℤ) : RootMatrix :=
  !![2, -2, -x; -2, 2, -y; -x, -y, 2]

def rootWeight (x y : ℤ) : RootMatrix :=
  !![0, 2, x; 2, 0, y; x, y, 0]

@[simp] theorem rootWeight_diag (x y : ℤ) (i : Fin 3) : rootWeight x y i i = 0 := by
  fin_cases i <;> simp [rootWeight]

theorem rootWeight_nonneg (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (i j : Fin 3) :
    0 ≤ rootWeight x y i j := by
  fin_cases i <;> fin_cases j <;> simp [rootWeight, hx, hy]

theorem rootWeight_offdiag_ge_two (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (i j : Fin 3) (hij : i ≠ j) : 2 ≤ rootWeight x y i j := by
  fin_cases i <;> fin_cases j <;> simp_all [rootWeight]

def rootSeed (j : Fin 3) : RootVector := fun k => if k = j then 1 else 0
abbrev rootBasis := rootSeed

def rootPairing (x y : ℤ) (u v : RootVector) : ℤ :=
  ∑ i, ∑ j, u i * rootGram x y i j * v j

def rootNorm (x y : ℤ) (u : RootVector) : ℤ := rootPairing x y u u

def rootVectorReflection (x y : ℤ) (u : RootVector) : RootMatrix :=
  1 - Matrix.vecMulVec u (rootGram x y *ᵥ u)

def rootReflectionMatrix (x y : ℤ) (i : Fin 3) : RootMatrix :=
  rootVectorReflection x y (rootSeed i)

def rootReflect (x y : ℤ) (i : Fin 3) (v : RootVector) : RootVector :=
  fun j => if j = i then -v i + ∑ k, rootWeight x y i k * v k else v j

def rootApply (x y : ℤ) (v : RootVector) (word : List (Fin 3)) : RootVector :=
  word.foldl (fun u i => rootReflect x y i u) v

def rootWordMatrix (x y : ℤ) (word : List (Fin 3)) : RootMatrix :=
  (word.reverse.map (rootReflectionMatrix x y)).prod

@[simp] theorem rootApply_nil (x y : ℤ) (v : RootVector) : rootApply x y v [] = v := rfl

@[simp] theorem rootApply_cons (x y : ℤ) (v : RootVector) (i : Fin 3)
    (word : List (Fin 3)) :
    rootApply x y v (i :: word) = rootApply x y (rootReflect x y i v) word := rfl

theorem rootApply_append (x y : ℤ) (v : RootVector) (w w' : List (Fin 3)) :
    rootApply x y v (w ++ w') = rootApply x y (rootApply x y v w) w' := by
  exact List.foldl_append

theorem rootReflect_mulVec (x y : ℤ) (i : Fin 3) (v : RootVector) :
    rootReflectionMatrix x y i *ᵥ v = rootReflect x y i v := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [rootReflectionMatrix, rootVectorReflection, rootSeed, rootReflect,
      rootGram, rootWeight, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.one_apply] <;> ring

@[simp] theorem rootReflect_involutive (x y : ℤ) (i : Fin 3) (v : RootVector) :
    rootReflect x y i (rootReflect x y i v) = v := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [rootReflect, rootWeight, Fin.sum_univ_three] <;> ring

theorem rootReflect_neg (x y : ℤ) (i : Fin 3) (v : RootVector) :
    rootReflect x y i (-v) = -rootReflect x y i v := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [rootReflect, rootWeight, Fin.sum_univ_three] <;> ring

theorem rootApply_neg (x y : ℤ) (v : RootVector) (word : List (Fin 3)) :
    rootApply x y (-v) word = -rootApply x y v word := by
  induction word generalizing v with
  | nil => rfl
  | cons i w ih => simp only [rootApply_cons, rootReflect_neg, ih]

theorem rootWordMatrix_mulVec (x y : ℤ) (word : List (Fin 3)) (v : RootVector) :
    rootWordMatrix x y word *ᵥ v = rootApply x y v word := by
  induction word generalizing v with
  | nil => simp [rootWordMatrix]
  | cons i w ih =>
      simp only [rootWordMatrix, List.reverse_cons, List.map_append, List.map_singleton,
        List.prod_append, List.prod_singleton]
      rw [← Matrix.mulVec_mulVec, rootReflect_mulVec]
      exact ih (rootReflect x y i v)

theorem rootGram_det (x y : ℤ) : (rootGram x y).det = -2 * (x + y) ^ 2 := by
  simp [rootGram, Matrix.det_fin_three]
  ring

end SerreMarkov.UniversalRoot
