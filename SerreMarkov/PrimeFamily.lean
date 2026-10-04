import SerreMarkov.IsometryNecessary
import SerreMarkov.Basis

/-!
# Uniqueness of normalized family representatives with prime total

The lattice invariant already separates the normalized representatives when
`m` is prime. This includes `m = 2` and uses no reflection-group classification.
-/

namespace SerreMarkov

open Matrix

theorem normalized_eq_of_difference_or_sum_dvd (m y y' : ℤ)
    (hm : 0 < m) (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m)
    (hd : m ∣ y - y' ∨ m ∣ y + y') : y = y' := by
  rcases hd with hd | hd
  · obtain ⟨k, hk⟩ := hd
    have hlo : -m < y - y' := by omega
    have hhi : y - y' < m := by omega
    have hk0 : k = 0 := by
      by_contra hn
      have hcases : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hcases with hn | hp
      · have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm)
          (show k + 1 ≤ 0 by omega)
        nlinarith
      · have hmul := mul_nonneg (le_of_lt hm) (show 0 ≤ k - 1 by omega)
        nlinarith
    simp [hk0] at hk
    omega
  · obtain ⟨k, hk⟩ := hd
    have hlo : 0 ≤ y + y' := by omega
    have hhi : y + y' ≤ m := by omega
    have hks : k = 0 ∨ k = 1 := by
      by_contra hn
      have hcases : k < 0 ∨ 1 < k := by omega
      rcases hcases with hn | hp
      · have hmul := mul_neg_of_pos_of_neg hm hn
        nlinarith
      · have hmul := mul_pos hm (show 0 < k - 1 by omega)
        nlinarith
    rcases hks with hk0 | hk1
    · simp [hk0] at hk
      omega
    · simp [hk1] at hk
      omega

theorem prime_normalized_square_injective (m : ℕ) (hm : m.Prime) (y y' : ℤ)
    (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m)
    (hs : (y' : ZMod m) ^ 2 = (y : ZMod m) ^ 2) : y = y' := by
  letI : Fact m.Prime := ⟨hm⟩
  have hmi : (0 : ℤ) < m := by exact_mod_cast hm.pos
  apply normalized_eq_of_difference_or_sum_dvd m y y' hmi hy hy' hb hb'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with heq | hneg
  · exact Or.inl ((ZMod.intCast_eq_intCast_iff_dvd_sub y' y m).mp heq)
  · have hz : ((y + y' : ℤ) : ZMod m) = 0 := by
      push_cast
      rw [hneg]
      ring
    exact Or.inr ((ZMod.intCast_zmod_eq_zero_iff_dvd (y + y') m).mp hz)

theorem prime_normalized_family_isometry_unique (m : ℕ) (hm : m.Prime)
    (y y' : ℤ) (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) : y = y' := by
  have hmi : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne_zero
  have hs := square_of_integer_congruences m y y'
    (family_divisibility_of_isometry m y y' hmi B hdet hcong)
  exact prime_normalized_square_injective m hm y y' hy hy' hb hb' hs

theorem prime_normalized_family_reachable_unique (m : ℕ) (hm : m.Prime)
    (y y' : ℤ) (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m)
    (hr : Reachable (family (m-y) y) (family (m-y') y')) : y = y' := by
  obtain ⟨B, hdet, hcong⟩ := reachable_integral_congruence hr
  exact prime_normalized_family_isometry_unique m hm y y' hy hy' hb hb' B hdet hcong

theorem prime_normalized_family_reachable_iff (m : ℕ) (hm : m.Prime)
    (y y' : ℤ) (hy : 0 ≤ y) (hy' : 0 ≤ y') (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m) :
    Reachable (family (m-y) y) (family (m-y') y') ↔ y = y' := by
  constructor
  · exact prime_normalized_family_reachable_unique m hm y y' hy hy' hb hb'
  · rintro rfl
    exact reachable_refl _

theorem prime_normalized_family_unique_totals (m m' : ℕ) (hm : m.Prime)
    (hm' : 0 < m') (y y' : ℤ) (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hb : 2 * y ≤ m) (hb' : 2 * y' ≤ m')
    (hr : Reachable (family (m-y) y) (family (m'-y') y')) : m = m' ∧ y = y' := by
  obtain ⟨B, hdet, hcong⟩ := reachable_integral_congruence hr
  have hmi : (0 : ℤ) < m := by exact_mod_cast hm.pos
  have hm'i : (0 : ℤ) < m' := by exact_mod_cast hm'
  have heqi := family_positive_totals_eq_of_isometry m m' y y' hmi hm'i B hdet hcong
  have heq : m = m' := by exact_mod_cast heqi
  subst m'
  exact ⟨rfl, prime_normalized_family_reachable_unique m hm y y' hy hy' hb hb' hr⟩

end SerreMarkov
