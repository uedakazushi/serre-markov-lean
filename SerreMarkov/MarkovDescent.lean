import Mathlib.Tactic

/-!
# Positive descent for the Markov equation with constant four

The Vieta replacement of the largest coordinate strictly reduces it when all
three coordinates are at least three. This is a pure integer-arithmetic lemma.
-/

namespace SerreMarkov

private theorem markov_sorted_descent (a b d : ℤ)
    (ha : 3 ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (he : a ^ 2 + b ^ 2 + d ^ 2 - a * b * d = 4) :
    0 < a * b - d ∧ a * b - d < b := by
  have hd : 0 < d := by omega
  have hnorm : 0 < a ^ 2 + b ^ 2 - 4 := by
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3)]
  have hproduct : d * (a * b - d) = a ^ 2 + b ^ 2 - 4 := by
    nlinarith [he]
  have hpositive : 0 < a * b - d := by
    by_contra hn
    have hn' : a * b - d ≤ 0 := le_of_not_gt hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) hn'
    nlinarith [hproduct, hnorm]
  have habsq : a ^ 2 ≤ b ^ 2 := by
    have hp : 0 ≤ (b - a) * (b + a) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [hp]
  have hlarge : 0 ≤ (a - 3) * b ^ 2 :=
    mul_nonneg (by omega) (sq_nonneg b)
  have hnegative : a ^ 2 + (2 - a) * b ^ 2 - 4 < 0 := by
    nlinarith [habsq, hlarge]
  have hfactor : (d - b) * (a * b - d - b) =
      a ^ 2 + (2 - a) * b ^ 2 - 4 := by
    nlinarith [he]
  refine ⟨hpositive, ?_⟩
  by_contra hn
  have hn' : b ≤ a * b - d := le_of_not_gt hn
  have hp : 0 ≤ (d - b) * (a * b - d - b) :=
    mul_nonneg (by omega) (by omega)
  nlinarith [hp, hfactor, hnegative]

/-- Vieta replacement of a largest coordinate is positive and strictly smaller. -/
theorem markov_positive_descent (a b d : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hd : 3 ≤ d)
    (he : a ^ 2 + b ^ 2 + d ^ 2 - a * b * d = 4)
    (hmax : a ≤ d ∧ b ≤ d) :
    0 < a * b - d ∧ a * b - d < d := by
  rcases le_total a b with hab | hba
  · have h := markov_sorted_descent a b d ha hab hmax.2 he
    exact ⟨h.1, lt_of_lt_of_le h.2 hmax.2⟩
  · have he' : b ^ 2 + a ^ 2 + d ^ 2 - b * a * d = 4 := by nlinarith [he]
    have h := markov_sorted_descent b a d hb hba hmax.1 he'
    have hp : 0 < a * b - d := by simpa only [mul_comm b a] using h.1
    have hl : a * b - d < a := by simpa only [mul_comm b a] using h.2
    exact ⟨hp, lt_of_lt_of_le hl hmax.1⟩

private theorem markov_nonnegative_small_forces_two (a b d : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (he : a ^ 2 + b ^ 2 + d ^ 2 - a * b * d = 4) (hsmall : a < 3) :
    a = 2 ∨ b = 2 ∨ d = 2 := by
  have ha2 : a ≤ 2 := by omega
  interval_cases a
  · have hb2 : b ≤ 2 := by nlinarith [sq_nonneg d, sq_nonneg (b - 2)]
    have hd2 : d ≤ 2 := by nlinarith [sq_nonneg b, sq_nonneg (d - 2)]
    interval_cases b <;> interval_cases d <;> norm_num at he
    all_goals norm_num
  · have hb2 : b ≤ 2 := by
      nlinarith [sq_nonneg (2 * d - b), sq_nonneg (b - 2)]
    have hd2 : d ≤ 2 := by
      nlinarith [sq_nonneg (2 * b - d), sq_nonneg (d - 2)]
    interval_cases b <;> interval_cases d <;> norm_num at he
    all_goals norm_num
  · exact Or.inl rfl

/-- After making the first two coordinates nonnegative, every solution either
has a coordinate of absolute value two, is the exceptional signed small triple,
or has all three coordinates at least three. -/
theorem markov_sign_normalized_cases (a b d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : a ^ 2 + b ^ 2 + d ^ 2 - a * b * d = 4) :
    (a = 2 ∨ a = -2 ∨ b = 2 ∨ b = -2 ∨ d = 2 ∨ d = -2) ∨
    (a = 1 ∧ b = 1 ∧ d = -1) ∨ (3 ≤ a ∧ 3 ≤ b ∧ 3 ≤ d) := by
  by_cases htwo : a = 2 ∨ a = -2 ∨ b = 2 ∨ b = -2 ∨ d = 2 ∨ d = -2
  · exact Or.inl htwo
  have havoid : a ≠ 2 ∧ b ≠ 2 ∧ d ≠ 2 ∧ d ≠ -2 := by tauto
  by_cases hd : d < 0
  · have hp : a * b * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) (le_of_lt hd)
    have hs : a ^ 2 + b ^ 2 + d ^ 2 ≤ 4 := by nlinarith [he, hp]
    have ha2 : a ≤ 2 := by
      nlinarith [hs, sq_nonneg b, sq_nonneg d, sq_nonneg (a - 2)]
    have hb2 : b ≤ 2 := by
      nlinarith [hs, sq_nonneg a, sq_nonneg d, sq_nonneg (b - 2)]
    have hd2 : -2 ≤ d := by
      nlinarith [hs, sq_nonneg a, sq_nonneg b, sq_nonneg (d + 2)]
    have ha1 : a ≤ 1 := by omega
    have hb1 : b ≤ 1 := by omega
    have hd1 : d = -1 := by omega
    subst d
    right; left
    interval_cases a <;> interval_cases b <;> norm_num at he
    all_goals norm_num
  · have hd0 : 0 ≤ d := by omega
    have ha3 : 3 ≤ a := by
      by_contra hn
      have hc := markov_nonnegative_small_forces_two a b d ha hb hd0 he (by omega)
      rcases hc with h | h | h <;> omega
    have hb3 : 3 ≤ b := by
      by_contra hn
      have he' : b ^ 2 + a ^ 2 + d ^ 2 - b * a * d = 4 := by nlinarith [he]
      have hc := markov_nonnegative_small_forces_two b a d hb ha hd0 he' (by omega)
      rcases hc with h | h | h <;> omega
    have hd3 : 3 ≤ d := by
      by_contra hn
      have he' : d ^ 2 + a ^ 2 + b ^ 2 - d * a * b = 4 := by nlinarith [he]
      have hc := markov_nonnegative_small_forces_two d a b hd0 ha hb he' (by omega)
      rcases hc with h | h | h <;> omega
    exact Or.inr (Or.inr ⟨ha3, hb3, hd3⟩)

end SerreMarkov
