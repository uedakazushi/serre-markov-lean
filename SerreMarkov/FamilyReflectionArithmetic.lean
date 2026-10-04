import SerreMarkov.UniversalRoot

/-! # The arithmetic of vertical reflection words

In the three-root quotient, the two vertical roots have pairing `-2`.
Each vertical reflection negates its pairing with the first vertical root
modulo `x+y`. A norm-two rank-zero vector has vertical-coordinate difference
`±1`. These are integer identities; no chamber or fundamental domain is used.
-/

namespace SerreMarkov.FamilyReflectionArithmetic

open UniversalRoot
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

theorem vertical_pair_sum (x y : ℤ) (v : RootVector) :
    rootPairing x y (rootSeed 0) v + rootPairing x y (rootSeed 1) v =
      -(x+y)*v 2 := by
  simp [rootPairing,rootSeed,rootGram,Fin.sum_univ_three]
  ring

theorem vertical_norm (x y : ℤ) (q : RootVector) (hq : q 2 = 0) :
    rootNorm x y q = 2*(q 0-q 1)^2 := by
  simp [rootNorm,rootPairing,rootGram,Fin.sum_univ_three,hq]
  ring

theorem vertical_norm_two_difference (x y : ℤ) (q : RootVector)
    (hq : q 2 = 0) (hn : rootNorm x y q = 2) :
    q 0-q 1 = 1 ∨ q 0-q 1 = -1 := by
  rw [vertical_norm x y q hq] at hn
  have hs : (q 0-q 1)^2 = (1:ℤ)^2 := by nlinarith only [hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hs

theorem vertical_root_pairing (x y : ℤ) (q v : RootVector) (hq : q 2 = 0) :
    rootPairing x y q v = (q 0-q 1)*rootPairing x y (rootSeed 0) v -
      (x+y)*q 1*v 2 := by
  simp [rootPairing,rootSeed,rootGram,Fin.sum_univ_three,hq]
  ring

theorem reflect_zero_pairing (x y : ℤ) (v : RootVector) :
    rootPairing x y (rootSeed 0) (rootReflect x y 0 v) =
      -rootPairing x y (rootSeed 0) v := by
  simp [rootPairing,rootSeed,rootGram,rootReflect,rootWeight,Fin.sum_univ_three]
  ring

theorem reflect_one_pairing (x y : ℤ) (v : RootVector) :
    rootPairing x y (rootSeed 0) (rootReflect x y 1 v) =
      rootPairing x y (rootSeed 0) v + 2*rootPairing x y (rootSeed 1) v := by
  simp [rootPairing,rootSeed,rootGram,rootReflect,rootWeight,Fin.sum_univ_three]
  ring

theorem vertical_reflection_signed_congruence (x y : ℤ) (v : RootVector)
    (i : Fin 3) (hi : i=0 ∨ i=1) :
    x+y ∣ rootPairing x y (rootSeed 0) (rootReflect x y i v) +
      rootPairing x y (rootSeed 0) v := by
  rcases hi with rfl | rfl
  · rw [reflect_zero_pairing]
    simp
  · rw [reflect_one_pairing]
    have he : rootPairing x y (rootSeed 0) v + 2*rootPairing x y (rootSeed 1) v +
        rootPairing x y (rootSeed 0) v = -(x+y)*(2*v 2) := by
      have hs := vertical_pair_sum x y v
      nlinarith only [hs]
    rw [he]
    exact dvd_mul_of_dvd_left (dvd_neg.mpr (dvd_refl (x+y))) _

/-- Arbitrary vertical words preserve this pairing up to a single sign
modulo the positive total. The identity does not require positivity. -/
theorem vertical_word_signed_congruence (x y : ℤ) (v : RootVector)
    (word : List (Fin 3)) (hw : ∀ i ∈ word, i=0 ∨ i=1) :
    ∃ s : ℤ, (s=1 ∨ s=-1) ∧
      x+y ∣ rootPairing x y (rootSeed 0) (rootApply x y v word) -
        s*rootPairing x y (rootSeed 0) v := by
  induction word generalizing v with
  | nil => exact ⟨1,Or.inl rfl,by simp⟩
  | cons i w ih =>
    have hi := hw i (by simp)
    obtain ⟨s,hs,hd⟩ := ih (rootReflect x y i v) (fun j hj => hw j (by simp [hj]))
    refine ⟨-s,?_,?_⟩
    · rcases hs with rfl | rfl <;> norm_num
    · rw [rootApply_cons]
      have hstep := vertical_reflection_signed_congruence x y v i hi
      convert dvd_add hd (dvd_mul_of_dvd_right hstep s) using 1 <;> ring

/-- Pairing with any norm-two rank-zero root introduces only another sign. -/
theorem vertical_root_signed_congruence (x y : ℤ) (q v : RootVector)
    (hq : q 2=0) (hn : rootNorm x y q=2) (s : ℤ) (hs : s=1 ∨ s=-1)
    (hd : x+y ∣ rootPairing x y (rootSeed 0) v-s*x) :
    ∃ t : ℤ, (t=1 ∨ t=-1) ∧ x+y ∣ rootPairing x y q v-t*x := by
  have hqdiff := vertical_norm_two_difference x y q hq hn
  refine ⟨(q 0-q 1)*s,?_,?_⟩
  · rcases hqdiff with hd | hd <;> rcases hs with hs | hs <;> rw [hd,hs] <;> norm_num
  · rw [vertical_root_pairing x y q v hq]
    convert dvd_sub (dvd_mul_of_dvd_right hd (q 0-q 1))
      (dvd_mul_of_dvd_left (dvd_mul_right (x+y) (q 1)) (v 2)) using 1 <;> ring

theorem vertical_word_circle_congruence (x y : ℤ) (q : RootVector)
    (hq : q 2=0) (hn : rootNorm x y q=2) (sgn : ℤ) (hs : sgn=1 ∨ sgn=-1)
    (word : List (Fin 3)) (hw : ∀ i ∈ word, i=0 ∨ i=1) :
    ∃ t : ℤ, (t=1 ∨ t=-1) ∧
      x+y ∣ rootPairing x y q (rootApply x y (sgn • rootSeed 2) word)-t*x := by
  obtain ⟨s,hsign,hd⟩ := vertical_word_signed_congruence x y (sgn • rootSeed 2) word hw
  have hseed : rootPairing x y (rootSeed 0) (sgn • rootSeed 2) = -sgn*x := by
    simp [rootPairing,rootSeed,rootGram,Fin.sum_univ_three]
    ring
  apply vertical_root_signed_congruence x y q _ hq hn (-s*sgn)
  · rcases hsign with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num
  · rw [hseed] at hd
    convert hd using 1 <;> ring

end SerreMarkov.FamilyReflectionArithmetic
