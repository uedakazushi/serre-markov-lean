import SerreMarkov.FamilyReflectionWords
import SerreMarkov.FamilyReflectionArithmetic
import SerreMarkov.CompositeFamily
import SerreMarkov.PrimeFamily
import SerreMarkov.Support

/-! # Uniqueness of every normalized negative family

The large-parameter case uses faithful three-involution words and integral
root coefficients. Parameters zero and one use their finite quotient orbits.
No hyperbolic chamber or orbifold classification is assumed.
-/

namespace SerreMarkov.FamilyUniqueness

open Matrix UniversalRoot FamilyReflectionBridge FamilyReflectionWords FamilyReflectionArithmetic

theorem large_family_signed_congruence (m y y' : ℤ) (hm : 0 < m)
    (hx : 2 ≤ m-y) (hy : 2 ≤ y)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) :
    m ∣ y-y' ∨ m ∣ y+y' := by
  obtain ⟨B,sign,vertical,hsgn,hvert,hq0,hnorm,hpair⟩ := reachable_circle_root m y y' hm hx hy hr
  have hvert' : ∀ i ∈ vertical, i = 0 ∨ i = 1 := by
    intro i hi
    have h := hvert i hi
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (h rfl)
  obtain ⟨t,ht,hd⟩ := vertical_word_circle_congruence (m-y) y
    (quotientMatrix (B : Mat4) *ᵥ rootSeed 0) hq0 hnorm sign hsgn vertical hvert'
  rw [hpair] at hd
  have htotal : m-y+y = m := by ring
  rw [htotal] at hd
  obtain ⟨k,hk⟩ := hd
  rcases ht with rfl | rfl
  · right
    refine ⟨k+2,?_⟩
    linear_combination hk
  · left
    refine ⟨-k,?_⟩
    linear_combination -hk

theorem normalized_large_family_unique (m y y' : ℤ) (hm : 0 < m)
    (hy : 2 ≤ y) (hy' : 0 ≤ y') (hb : 2*y ≤ m) (hb' : 2*y' ≤ m)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) : y = y' := by
  apply normalized_eq_of_difference_or_sum_dvd m y y' hm (by omega) hy' hb hb'
  exact large_family_signed_congruence m y y' hm (by omega) hy hr

theorem normalized_zero_family_unique (m y' : ℤ) (hm : 0 < m)
    (hy' : 0 ≤ y') (hb' : 2*y' ≤ m)
    (hr : Reachable (family m 0) (family (m-y') y')) : y' = 0 := by
  have hd : m ∣ y' := ((family_divisibility_invariant hr m).mp ⟨dvd_refl m,dvd_zero m⟩).2
  have he := normalized_eq_of_difference_or_sum_dvd m 0 y' hm (by omega) hy'
    (by omega) hb' (Or.inr (by simpa using hd))
  exact he.symm

theorem normalized_small_total_family_unique (m y y' : ℤ) (hm : 0 < m) (hm5 : m < 5)
    (hy : 0 < y) (hy' : 0 < y') (hb : 2*y ≤ m) (hb' : 2*y' ≤ m)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) : y = y' := by
  have hml : 1 ≤ m := by omega
  have hmh : m ≤ 4 := by omega
  interval_cases m
  · omega
  · omega
  · omega
  · obtain ⟨B,hdet,hcong⟩ := reachable_integral_congruence hr
    have hdiv := family_divisibility_of_isometry 4 y y' (by norm_num) B hdet hcong
    have hsq := square_of_integer_congruences 4 y y' hdiv
    have hyl : 1 ≤ y := by omega
    have hyh : y ≤ 2 := by omega
    have hy'l : 1 ≤ y' := by omega
    have hy'h : y' ≤ 2 := by omega
    interval_cases y <;> interval_cases y'
    all_goals first | rfl | (exfalso; revert hsq; decide)

theorem normalized_family_reachable_unique (m y y' : ℤ) (hm : 0 < m)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2*y ≤ m) (hb' : 2*y' ≤ m)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) : y = y' := by
  by_cases hy0 : y = 0
  · subst y
    simpa using (normalized_zero_family_unique m y' hm hy' hb' (by simpa using hr)).symm
  by_cases hy'0 : y' = 0
  · subst y'
    simpa using normalized_zero_family_unique m y hm hy hb (by simpa using reachable_symm hr)
  by_cases hm5 : 5 ≤ m
  · by_cases hy2 : 2 ≤ y
    · exact normalized_large_family_unique m y y' hm hy2 hy' hb hb' hr
    · have hy1 : y = 1 := by omega
      subst y
      let n : ℕ := m.toNat
      have hn : (n : ℤ) = m := Int.toNat_of_nonneg (by omega)
      have hn5 : 5 ≤ n := by omega
      have he := CompositeFamily.normalized_parameter1_family_unique n hn5 y' hy' (by omega)
        (by simpa only [hn] using hr)
      exact he.symm
  · exact normalized_small_total_family_unique m y y' hm (by omega) (by omega) (by omega) hb hb' hr

theorem normalized_family_reachable_iff (m y y' : ℤ) (hm : 0 < m)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2*y ≤ m) (hb' : 2*y' ≤ m) :
    Reachable (family (m-y) y) (family (m-y') y') ↔ y = y' := by
  constructor
  · exact normalized_family_reachable_unique m y y' hm hy hy' hb hb'
  · rintro rfl
    exact reachable_refl _

theorem normalized_positive_totals_reachable_unique (m m' y y' : ℤ)
    (hm : 0 < m) (hm' : 0 < m') (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hb : 2*y ≤ m) (hb' : 2*y' ≤ m')
    (hr : Reachable (family (m-y) y) (family (m'-y') y')) : m = m' ∧ y = y' := by
  obtain ⟨B,hdet,hcong⟩ := reachable_integral_congruence hr
  have he := family_positive_totals_eq_of_isometry m m' y y' hm hm' B hdet hcong
  subst m'
  exact ⟨rfl,normalized_family_reachable_unique m y y' hm hy hy' hb hb' hr⟩

theorem normalized_positive_totals_reachable_iff (m m' y y' : ℤ)
    (hm : 0 < m) (hm' : 0 < m') (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hb : 2*y ≤ m) (hb' : 2*y' ≤ m') :
    Reachable (family (m-y) y) (family (m'-y') y') ↔ m = m' ∧ y = y' := by
  constructor
  · exact normalized_positive_totals_reachable_unique m m' y y' hm hm' hy hy' hb hb'
  · rintro ⟨rfl,rfl⟩
    exact reachable_refl _

end SerreMarkov.FamilyUniqueness
