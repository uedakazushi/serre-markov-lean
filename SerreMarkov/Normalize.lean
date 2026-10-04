import SerreMarkov.Mutations

/-!
# Normalization of the integer family

Every integer parameter pair of nonzero sum reaches the normalized interval
`x ≥ y ≥ 0`, preserving the absolute value of its sum. Reachability means a
finite word in the actual braid and sign generators, not a postulated orbit
relation. Integer division supplies the finite number of translations.
-/

namespace SerreMarkov

/-- A finite mutation word translates the second parameter by the fixed sum. -/
theorem family_shift_up (m y : ℤ) :
    Reachable (family (m-y) y) (family (m-(y+m)) (y+m)) := by
  have h := reachable_trans (family_reflection_reachable (m-y) y)
    (family_swap_reachable (m-y+2*y) (-y))
  have heq : family (-y) (m-y+2*y) = family (m-(y+m)) (y+m) := by
    congr 1 <;> ring
  rw [heq] at h
  exact h

/-- The opposite translation also comes from a finite mutation word. -/
theorem family_shift_down (m y : ℤ) :
    Reachable (family (m-y) y) (family (m-(y-m)) (y-m)) := by
  have h := reachable_trans (family_swap_reachable (m-y) y)
    (family_reflection_reachable y (m-y))
  have heq : family (y+2*(m-y)) (-(m-y)) = family (m-(y-m)) (y-m) := by
    congr 1 <;> ring
  rw [heq] at h
  exact h

theorem family_shift_nat_up (m y : ℤ) (n : ℕ) :
    Reachable (family (m-y) y) (family (m-(y+(n:ℤ)*m)) (y+(n:ℤ)*m)) := by
  induction n with
  | zero => simpa using reachable_refl (family (m-y) y)
  | succ n ih =>
    have h := reachable_trans ih (family_shift_up m (y+(n:ℤ)*m))
    have heq : family (m-((y+(n:ℤ)*m)+m)) ((y+(n:ℤ)*m)+m) =
        family (m-(y+((n+1:ℕ):ℤ)*m)) (y+((n+1:ℕ):ℤ)*m) := by
      push_cast
      congr 1 <;> ring
    rw [heq] at h
    exact h

theorem family_shift_nat_down (m y : ℤ) (n : ℕ) :
    Reachable (family (m-y) y) (family (m-(y-(n:ℤ)*m)) (y-(n:ℤ)*m)) := by
  induction n with
  | zero => simpa using reachable_refl (family (m-y) y)
  | succ n ih =>
    have h := reachable_trans ih (family_shift_down m (y-(n:ℤ)*m))
    have heq : family (m-((y-(n:ℤ)*m)-m)) ((y-(n:ℤ)*m)-m) =
        family (m-(y-((n+1:ℕ):ℤ)*m)) (y-((n+1:ℕ):ℤ)*m) := by
      push_cast
      congr 1 <;> ring
    rw [heq] at h
    exact h

/-- All integral multiples of the sum are realized by finite mutation words. -/
theorem family_shift_int (m y n : ℤ) :
    Reachable (family (m-y) y) (family (m-(y+n*m)) (y+n*m)) := by
  cases n with
  | ofNat n => exact family_shift_nat_up m y n
  | negSucc n =>
    have h := family_shift_nat_down m y (n+1)
    have heq : family (m-(y-((n+1:ℕ):ℤ)*m)) (y-((n+1:ℕ):ℤ)*m) =
        family (m-(y+(Int.negSucc n)*m)) (y+(Int.negSucc n)*m) := by
      simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
      congr 1 <;> ring
    rw [heq] at h
    exact h

/-- Division by a positive sum reduces to a complete interval of residues. -/
theorem family_reduce_mod (m y : ℤ) (_hm : 0 < m) :
    Reachable (family (m-y) y) (family (m-y%m) (y%m)) := by
  have h := family_shift_int m y (-(y/m))
  have hy : y+(-(y/m))*m = y%m := by
    have hdiv := Int.emod_add_mul_ediv y m
    nlinarith
  simpa only [hy] using h

/-- Normalization when the parameter sum is positive. -/
theorem family_normalize_positive (x y : ℤ) (hm : 0 < x+y) :
    ∃ x' y' : ℤ, Reachable (family x y) (family x' y') ∧
      y' ≤ x' ∧ 0 ≤ y' ∧ x'+y'=x+y := by
  let m := x+y
  let r := y%m
  have hmp : 0 < m := hm
  have hr0 : 0 ≤ r := Int.emod_nonneg y (ne_of_gt hmp)
  have hrm : r < m := Int.emod_lt_of_pos y hmp
  have hstart : family x y = family (m-y) y := by
    dsimp [m]
    congr 1
    ring
  have hreach : Reachable (family x y) (family (m-r) r) := by
    rw [hstart]
    exact family_reduce_mod m y hmp
  by_cases hhalf : 2*r ≤ m
  · refine ⟨m-r, r, hreach, ?_, hr0, ?_⟩
    · omega
    · dsimp [m]
      ring
  · refine ⟨r, m-r, reachable_trans hreach (family_swap_reachable (m-r) r),
      ?_, ?_, ?_⟩
    · omega
    · omega
    · dsimp [m]
      ring

/-- The manuscript's normalization theorem, with actual finite mutation words. -/
theorem family_normalize (x y : ℤ) (hm : x+y ≠ 0) :
    ∃ x' y' : ℤ, Reachable (family x y) (family x' y') ∧
      y' ≤ x' ∧ 0 ≤ y' ∧ x'+y'=|x+y| := by
  by_cases hp : 0 < x+y
  · obtain ⟨x', y', h, hxy, hy, hsum⟩ := family_normalize_positive x y hp
    exact ⟨x', y', h, hxy, hy, hsum.trans (abs_of_pos hp).symm⟩
  · have hn : x+y < 0 := by omega
    have hnp : 0 < -x + -y := by omega
    obtain ⟨x', y', h, hxy, hy, hsum⟩ := family_normalize_positive (-x) (-y) hnp
    refine ⟨x', y', reachable_trans (family_negation_reachable x y) h,
      hxy, hy, ?_⟩
    rw [abs_of_neg hn]
    omega

/-- A zero-sum pair normalizes by at most one simultaneous sign change. -/
theorem family_normalize_degenerate (x y : ℤ) (hm : x+y=0) :
    ∃ k : ℤ, 0 ≤ k ∧ Reachable (family x y) (family k (-k)) := by
  have hy : y = -x := by omega
  subst y
  by_cases hx : 0 ≤ x
  · exact ⟨x, hx, reachable_refl _⟩
  · refine ⟨-x, by omega, ?_⟩
    simpa using family_negation_reachable x (-x)

end SerreMarkov
