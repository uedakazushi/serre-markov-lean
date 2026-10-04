import Mathlib.Tactic

namespace SerreMarkov

/-- The content of the degenerate symmetric form determines its nonnegative
family parameter uniquely. -/
theorem degenerate_parameter_eq_of_content (k l : ℤ) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (h : Int.natAbs (4 - k ^ 2) = Int.natAbs (4 - l ^ 2)) : k = l := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with he | he
  · have hs : k ^ 2 = l ^ 2 := by linarith
    exact (sq_eq_sq₀ hk hl).mp hs
  · have hs : k ^ 2 + l ^ 2 = 8 := by linarith
    have hk2 : k ≤ 2 := by nlinarith [sq_nonneg l, sq_nonneg (k - 2)]
    have hl2 : l ≤ 2 := by nlinarith [sq_nonneg k, sq_nonneg (l - 2)]
    interval_cases k <;> interval_cases l <;> norm_num at hs
    all_goals rfl

end SerreMarkov
