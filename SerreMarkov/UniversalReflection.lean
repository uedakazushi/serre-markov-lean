import SerreMarkov.UniversalRoot
import SerreMarkov.UniversalWord

/-! # Coefficient growth for the three universal reflection roots

Words are applied from left to right. Reducedness of `seed :: word` expresses
both adjacent distinctness and the condition that the first applied reflection
differs from the seed. The coefficient estimates are integral and contain no
chamber or geometric assumptions.
-/

namespace SerreMarkov.UniversalReflection

open UniversalRoot
open scoped BigOperators

/-- A nonnegative root has one strictly dominant positive coordinate. -/
structure Dominant (v : RootVector) (p : Fin 3) : Prop where
  nonnegative : ∀ j, 0 ≤ v j
  positive : 1 ≤ v p
  largest : ∀ j, j ≠ p → v j < v p

@[simp] theorem reflect_selected (x y : ℤ) (i : Fin 3) (v : RootVector) :
    rootReflect x y i v i = -v i + ∑ k, rootWeight x y i k * v k := by
  simp [rootReflect]

theorem reflect_unselected (x y : ℤ) (i j : Fin 3) (v : RootVector) (hji : j ≠ i) :
    rootReflect x y i v j = v j := by simp [rootReflect,hji]

theorem seed_dominant (k : Fin 3) : Dominant (rootSeed k) k := by
  constructor
  · intro j
    by_cases h : j = k <;> simp [rootSeed,h]
  · simp [rootSeed]
  · intro j hj
    simp [rootSeed,hj]

/-- A different reflection creates a new unique maximum, strictly larger
than the previous maximum, and preserves nonnegativity. -/
theorem reflection_growth (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {v : RootVector} {p i : Fin 3} (hd : Dominant v p) (hip : i ≠ p) :
    Dominant (rootReflect x y i v) i ∧ v p < rootReflect x y i v i := by
  have hnonneg (j : Fin 3) : 0 ≤ rootWeight x y i j * v j := by
    exact mul_nonneg (rootWeight_nonneg x y (by omega) (by omega) i j)
      (hd.nonnegative j)
  have hsum : rootWeight x y i p * v p ≤ ∑ j, rootWeight x y i j * v j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ p)
  have hprod : 2 * v p ≤ rootWeight x y i p * v p :=
    mul_le_mul_of_nonneg_right (rootWeight_offdiag_ge_two x y hx hy i p hip)
      (hd.nonnegative p)
  have hnew : v p < rootReflect x y i v i := by
    rw [reflect_selected]
    have hold := hd.largest i hip
    omega
  have hmax (j : Fin 3) : v j ≤ v p := by
    by_cases h : j = p
    · simp [h]
    · exact (hd.largest j h).le
  refine ⟨⟨?_,?_,?_⟩,hnew⟩
  · intro j
    by_cases h : j = i
    · subst j
      exact le_trans (hd.nonnegative p) hnew.le
    · rw [reflect_unselected x y i j v h]
      exact hd.nonnegative j
  · exact le_trans hd.positive hnew.le
  · intro j hj
    rw [reflect_unselected x y i j v hj]
    exact lt_of_le_of_lt (hmax j) hnew

theorem reflection_monotone (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {v : RootVector} {p i : Fin 3} (hd : Dominant v p) (hip : i ≠ p) :
    ∀ j, v j ≤ rootReflect x y i v j := by
  have hg := (reflection_growth x y hx hy hd hip).2
  intro j
  by_cases h : j = i
  · subst j
    exact le_trans (hd.largest i hip).le hg.le
  · rw [reflect_unselected x y i j v h]

/-- Every coordinate increases weakly along a reduced root word. -/
theorem word_monotone (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {v : RootVector} {p : Fin 3} (word : List (Fin 3))
    (hd : Dominant v p) (hred : (p :: word).IsChain (· ≠ ·)) :
    ∀ j, v j ≤ rootApply x y v word j := by
  induction word generalizing p v with
  | nil => simp
  | cons i word ih =>
    obtain ⟨hpi,htail⟩ := List.isChain_cons_cons.mp hred
    obtain ⟨hd',_⟩ := reflection_growth x y hx hy hd hpi.symm
    intro j
    calc
      v j ≤ rootReflect x y i v j := reflection_monotone x y hx hy hd hpi.symm j
      _ ≤ rootApply x y (rootReflect x y i v) word j := ih hd' htail j

theorem word_nonnegative (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {v : RootVector} {p : Fin 3} (word : List (Fin 3))
    (hd : Dominant v p) (hred : (p :: word).IsChain (· ≠ ·)) :
    ∀ j, 0 ≤ rootApply x y v word j := by
  intro j
  exact le_trans (hd.nonnegative j) (word_monotone x y hx hy word hd hred j)

/-- Once selected, a coordinate exceeds even the initial dominant value. -/
theorem selected_coefficient_growth (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    {v : RootVector} {p : Fin 3} (word : List (Fin 3))
    (hd : Dominant v p) (hred : (p :: word).IsChain (· ≠ ·))
    {j : Fin 3} (hj : j ∈ word) : v p < rootApply x y v word j := by
  induction word generalizing p v with
  | nil => simp at hj
  | cons i word ih =>
    obtain ⟨hpi,htail⟩ := List.isChain_cons_cons.mp hred
    obtain ⟨hd',hg⟩ := reflection_growth x y hx hy hd hpi.symm
    rw [rootApply_cons]
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact lt_of_lt_of_le hg (word_monotone x y hx hy word hd' htail i)
    · exact lt_trans hg (ih hd' htail hj)

theorem selected_coefficient_ge_two (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : (k :: word).IsChain (· ≠ ·))
    {j : Fin 3} (hj : j ∈ word) : 2 ≤ rootApply x y (rootSeed k) word j := by
  have hg := selected_coefficient_growth x y hx hy word (seed_dominant k) hred hj
  have hs : rootSeed k k = 1 := by simp [rootSeed]
  rw [hs] at hg
  omega

theorem unselected_coefficient (x y : ℤ) (v : RootVector) (word : List (Fin 3))
    (j : Fin 3) (hj : j ∉ word) : rootApply x y v word j = v j := by
  induction word generalizing v with
  | nil => rfl
  | cons i word ih =>
    have hji : j ≠ i := by intro h; apply hj; simp [h]
    have htail : j ∉ word := by intro h; exact hj (List.mem_cons_of_mem i h)
    rw [rootApply_cons, ih _ htail, reflect_unselected x y i j v hji]

/-- A coefficient can equal one only if it is the unchanged seed coordinate. -/
theorem coefficient_one_iff (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : (k :: word).IsChain (· ≠ ·))
    (j : Fin 3) :
    rootApply x y (rootSeed k) word j = 1 ↔ j = k ∧ j ∉ word := by
  constructor
  · intro h
    have hnot : j ∉ word := by
      intro hj
      have hg := selected_coefficient_ge_two x y hx hy k word hred hj
      omega
    refine ⟨?_,hnot⟩
    rw [unselected_coefficient x y (rootSeed k) word j hnot] at h
    by_contra hjk
    simp [rootSeed,hjk] at h
  · rintro ⟨hjk,hnot⟩
    rw [unselected_coefficient x y (rootSeed k) word j hnot]
    simp [rootSeed,hjk]

theorem circle_coefficient_one_iff (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : (k :: word).IsChain (· ≠ ·)) :
    rootApply x y (rootSeed k) word 2 = 1 ↔ k = 2 ∧ 2 ∉ word := by
  simpa only [eq_comm] using coefficient_one_iff x y hx hy k word hred 2

theorem circle_one_vertical_word (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : (k :: word).IsChain (· ≠ ·))
    (hc : rootApply x y (rootSeed k) word 2 = 1) :
    k = 2 ∧ ∀ i ∈ word, i = 0 ∨ i = 1 := by
  obtain ⟨hk,hnot⟩ := (circle_coefficient_one_iff x y hx hy k word hred).mp hc
  refine ⟨hk,?_⟩
  intro i hi
  have hne : i ≠ 2 := by intro h; subst i; exact hnot hi
  fin_cases i <;> simp_all

/-- Every nonempty reduced reflection word acts nontrivially; hence the
integral reflection representation is faithful on reduced words. -/
theorem rootWordMatrix_faithful_reduced (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (word : List (Fin 3)) (hred : UniversalWord.Reduced word) (hn : word ≠ []) :
    rootWordMatrix x y word ≠ 1 := by
  intro hm
  cases word with
  | nil => exact hn rfl
  | cons i word =>
    have hex : ∃ k : Fin 3, k ≠ i := by
      fin_cases i
      · exact ⟨1,by decide⟩
      · exact ⟨0,by decide⟩
      · exact ⟨0,by decide⟩
    obtain ⟨k,hki⟩ := hex
    have hchain : (k::i::word).IsChain (· ≠ ·) :=
      List.isChain_cons_cons.mpr ⟨hki,hred⟩
    have hg := selected_coefficient_ge_two x y hx hy k (i::word) hchain
      (j := i) (by simp)
    have heq : rootApply x y (rootSeed k) (i::word) = rootSeed k := by
      rw [← rootWordMatrix_mulVec,hm]
      simp
    rw [heq] at hg
    simp [rootSeed,hki.symm] at hg

theorem rootReflect_seed_self (x y : ℤ) (k : Fin 3) :
    rootReflect x y k (rootSeed k) = -rootSeed k := by
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [rootReflect, rootSeed, rootWeight]

/-- The circle coordinate is at least three as soon as that reflection has
been used, under the stronger off-diagonal bounds of the hyperbolic family. -/
theorem selected_circle_coefficient_ge_three (x y : ℤ) (hx : 3 ≤ x) (hy : 3 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : (k :: word).IsChain (· ≠ ·))
    (hc : (2 : Fin 3) ∈ word) : 3 ≤ rootApply x y (rootSeed k) word 2 := by
  cases word with
  | nil => simp at hc
  | cons i word =>
    obtain ⟨hki,htail⟩ := List.isChain_cons_cons.mp hred
    obtain ⟨hd,hg⟩ := reflection_growth x y (by omega) (by omega)
      (seed_dominant k) hki.symm
    rw [rootApply_cons]
    by_cases hi : i = 2
    · subst i
      have hnew : 3 ≤ rootReflect x y 2 (rootSeed k) 2 := by
        fin_cases k <;>
          simp_all [rootReflect, rootSeed, rootWeight]
      exact le_trans hnew (word_monotone x y (by omega) (by omega) word hd htail 2)
    · have hmem : (2 : Fin 3) ∈ word := (List.mem_cons.mp hc).resolve_left (Ne.symm hi)
      have ht := selected_coefficient_growth x y (by omega) (by omega)
        word hd htail hmem
      have hs : rootSeed k k = 1 := by simp [rootSeed]
      rw [hs] at hg
      omega

/-- Reduced words producing circle coefficient of absolute value one begin
at the circle root and use only vertical reflections, up to an overall sign. -/
theorem reduced_circle_abs_one (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3)) (hred : UniversalWord.Reduced word)
    (hc : |rootApply x y (rootSeed k) word 2| = 1) :
    k = 2 ∧ ∃ vertical : List (Fin 3),
      (∀ i ∈ vertical, i ≠ 2) ∧
      (rootApply x y (rootSeed k) word = rootApply x y (rootSeed 2) vertical ∨
       rootApply x y (rootSeed k) word = -rootApply x y (rootSeed 2) vertical) := by
  cases word with
  | nil =>
    have hk : k = 2 := by
      by_contra h
      simp [rootSeed,Ne.symm h] at hc
    refine ⟨hk,[],by simp,Or.inl ?_⟩
    simp [hk]
  | cons i word =>
    by_cases hik : i = k
    · subst i
      have heq : rootApply x y (rootSeed k) (k::word) =
          -rootApply x y (rootSeed k) word := by
        rw [rootApply_cons, rootReflect_seed_self, rootApply_neg]
      rw [heq] at hc
      have hn := word_nonnegative x y hx hy word (seed_dominant k) hred 2
      have hone : rootApply x y (rootSeed k) word 2 = 1 := by
        simpa only [Pi.neg_apply,abs_neg,abs_of_nonneg hn] using hc
      obtain ⟨hk,hnot⟩ := (circle_coefficient_one_iff x y hx hy k word hred).mp hone
      refine ⟨hk,word,?_,Or.inr ?_⟩
      · intro j hj hje
        subst j
        exact hnot hj
      · simpa only [hk] using heq
    · have hchain : (k::i::word).IsChain (· ≠ ·) :=
        List.isChain_cons_cons.mpr ⟨Ne.symm hik,hred⟩
      have hn := word_nonnegative x y hx hy (i::word) (seed_dominant k) hchain 2
      have hone : rootApply x y (rootSeed k) (i::word) 2 = 1 := by
        simpa only [abs_of_nonneg hn] using hc
      obtain ⟨hk,hnot⟩ :=
        (circle_coefficient_one_iff x y hx hy k (i::word) hchain).mp hone
      refine ⟨hk,i::word,?_,Or.inl ?_⟩
      · intro j hj hje
        subst j
        exact hnot hj
      · rw [hk]

theorem rootApply_reduce (x y : ℤ) (v : RootVector) (word : List (Fin 3)) :
    rootApply x y v (UniversalWord.reduce word) = rootApply x y v word := by
  exact UniversalWord.foldl_reduce (rootReflect x y)
    (fun i u => rootReflect_involutive x y i u) word v

theorem rootWordMatrix_reduce (x y : ℤ) (word : List (Fin 3)) :
    rootWordMatrix x y (UniversalWord.reduce word) = rootWordMatrix x y word := by
  ext i j
  have h := congrFun (rootApply_reduce x y (rootSeed j) word) i
  rw [← rootWordMatrix_mulVec, ← rootWordMatrix_mulVec] at h
  fin_cases j <;>
    simpa [Matrix.mulVec, dotProduct, rootSeed, Fin.sum_univ_three] using h

/-- Cancellation of adjacent equal generators completely detects the
kernel of the three-root reflection representation. -/
theorem rootWordMatrix_eq_one_iff (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (word : List (Fin 3)) :
    rootWordMatrix x y word = 1 ↔ UniversalWord.reduce word = [] := by
  constructor
  · intro h
    by_contra hn
    exact rootWordMatrix_faithful_reduced x y hx hy (UniversalWord.reduce word)
      (UniversalWord.reduce_reduced word) hn ((rootWordMatrix_reduce x y word).trans h)
  · intro h
    rw [← rootWordMatrix_reduce, h]
    simp [rootWordMatrix]

/-- Starting at the circle root, every selected coordinate is already at
least three. The estimate persists after any subsequent reduced letters. -/
theorem circle_seed_selected_coefficient_ge_three (x y : ℤ) (hx : 3 ≤ x) (hy : 3 ≤ y)
    (word : List (Fin 3)) (hred : ((2 : Fin 3) :: word).IsChain (· ≠ ·))
    {j : Fin 3} (hj : j ∈ word) : 3 ≤ rootApply x y (rootSeed 2) word j := by
  cases word with
  | nil => simp at hj
  | cons i word =>
    obtain ⟨hki,htail⟩ := List.isChain_cons_cons.mp hred
    obtain ⟨hd,_⟩ := reflection_growth x y (by omega) (by omega)
      (seed_dominant 2) hki.symm
    have hnew : 3 ≤ rootReflect x y i (rootSeed 2) i := by
      fin_cases i <;> simp_all [rootReflect, rootSeed, rootWeight]
    rw [rootApply_cons]
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact le_trans hnew (word_monotone x y (by omega) (by omega) word hd htail i)
    · have ht := selected_coefficient_growth x y (by omega) (by omega)
        word hd htail hj
      omega

/-- This statement applies to arbitrary reflection words: no reducedness
hypothesis or chamber choice is hidden in the circle-root conclusion. -/
theorem circle_abs_one_vertical (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3))
    (hc : |rootApply x y (rootSeed k) word 2| = 1) :
    k = 2 ∧ ∃ vertical : List (Fin 3),
      (∀ i ∈ vertical, i ≠ 2) ∧
      (rootApply x y (rootSeed k) word = rootApply x y (rootSeed 2) vertical ∨
       rootApply x y (rootSeed k) word = -rootApply x y (rootSeed 2) vertical) := by
  have hred := UniversalWord.reduce_reduced word
  have hc' : |rootApply x y (rootSeed k) (UniversalWord.reduce word) 2| = 1 := by
    rw [rootApply_reduce]
    exact hc
  simpa only [rootApply_reduce] using reduced_circle_abs_one x y hx hy k
    (UniversalWord.reduce word) hred hc'

/-- Equivalent scalar-sign formulation, useful when interpreting roots as
reflection vectors. The returned word uses just the two vertical generators. -/
theorem circle_unit_vertical (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (k : Fin 3) (word : List (Fin 3))
    (hc : rootApply x y (rootSeed k) word 2 = 1 ∨
      rootApply x y (rootSeed k) word 2 = -1) :
    k = 2 ∧ ∃ (sign : ℤ) (vertical : List (Fin 3)),
      (sign = 1 ∨ sign = -1) ∧ (∀ i ∈ vertical, i ≠ 2) ∧
      rootApply x y (rootSeed k) word = rootApply x y (sign • rootSeed 2) vertical := by
  have ha : |rootApply x y (rootSeed k) word 2| = 1 := by
    rcases hc with hc | hc <;> rw [hc] <;> norm_num
  obtain ⟨hk,vertical,hv,heq | heq⟩ := circle_abs_one_vertical x y hx hy k word ha
  · exact ⟨hk,1,vertical,Or.inl rfl,hv,by simpa using heq⟩
  · refine ⟨hk,-1,vertical,Or.inr rfl,hv,?_⟩
    simpa only [neg_one_smul,rootApply_neg] using heq

end SerreMarkov.UniversalReflection
