import SerreMarkov.PrimePowerNonzeroRoots

/-! # The complete local square-root count at odd prime powers

The zero and nonzero valuation branches are combined without any mutation
classification assumption. Exponent zero and the parameter zero are included.
-/

namespace SerreMarkov.LocalRootFormula

open FamilyFiberFinite

/-- The local arithmetic factor, including square-zero parameters. -/
def localRootCount (p E y : ℕ) : ℕ :=
  if y = 0 ∨ E ≤ 2*y.factorization p then p^(E/2) else 2*p^(y.factorization p)

/-- Dividing by the full prime-power factor leaves a unit factor. -/
theorem factorization_unit_decomposition (p y : ℕ) (hp : p.Prime) (hy : y ≠ 0) :
    y = p^(y.factorization p)*(y/p^(y.factorization p)) ∧
      ¬ p ∣ y/p^(y.factorization p) := by
  have hd : p^(y.factorization p) ∣ y :=
    (hp.pow_dvd_iff_le_factorization hy).mpr le_rfl
  have heq : y = p^(y.factorization p)*(y/p^(y.factorization p)) :=
    (Nat.mul_div_cancel' hd).symm
  refine ⟨heq, ?_⟩
  intro hu
  have hstrong : p^(y.factorization p+1) ∣ y := by
    calc
      p^(y.factorization p+1) = p^(y.factorization p)*p := pow_succ _ _
      _ ∣ p^(y.factorization p)*(y/p^(y.factorization p)) := Nat.mul_dvd_mul_left _ hu
      _ = y := heq.symm
  have hbad := (hp.pow_dvd_iff_le_factorization hy).mp hstrong
  omega

/-- Every square modulo an odd prime power has this exact local root count. -/
theorem primePower_square_roots_natCard (p E y : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card (Roots (p^E) ((y : ZMod (p^E))^2)) = localRootCount p E y := by
  unfold localRootCount
  by_cases hy : y = 0
  · subst y
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), true_or, if_true]
    exact primePower_squareZeroRoots_general_natCard p E hp
  · by_cases hv : E ≤ 2*y.factorization p
    · rw [if_pos (Or.inr hv)]
      exact primePower_square_roots_natCard_of_large_factorization p E y hp hy hv
    · rw [if_neg (not_or.mpr ⟨hy,hv⟩)]
      obtain ⟨heq,hu⟩ := factorization_unit_decomposition p y hp hy
      have hcount := PrimePowerNonzeroRoots.nonzero_primePower_roots_natCard
        p E (y.factorization p) (y/p^(y.factorization p)) hp hodd (by omega) hu
      have htarget : ((p^(y.factorization p)*(y/p^(y.factorization p)) : ℕ) : ZMod (p^E)) =
          (y : ZMod (p^E)) := congrArg (fun n : ℕ => (n : ZMod (p^E))) heq.symm
      simpa only [htarget] using hcount

/-- The local count with its two branches displayed explicitly. -/
theorem primePower_square_roots_formula (p E y : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card (Roots (p^E) ((y : ZMod (p^E))^2)) =
      if y = 0 ∨ E ≤ 2*y.factorization p then p^(E/2) else 2*p^(y.factorization p) :=
  primePower_square_roots_natCard p E y hp hodd

private theorem natAbs_square_cast (p E : ℕ) (y : ℤ) :
    (y.natAbs : ZMod (p^E))^2 = (y : ZMod (p^E))^2 := by
  simpa only [Int.cast_pow, Int.cast_natCast] using
    congrArg (fun a : ℤ => (a : ZMod (p^E))) (Int.natAbs_pow_two y)

/-- The local root count for an arbitrary integral parameter of either sign. -/
theorem primePower_integer_square_roots_natCard (p E : ℕ) (y : ℤ)
    (hp : p.Prime) (hodd : Odd p) :
    Nat.card (Roots (p^E) ((y : ZMod (p^E))^2)) = localRootCount p E y.natAbs := by
  rw [← natAbs_square_cast p E y]
  exact primePower_square_roots_natCard p E y.natAbs hp hodd

/-- The integer formula uses the prime exponent of `|y|`. -/
theorem primePower_integer_square_roots_formula (p E : ℕ) (y : ℤ)
    (hp : p.Prime) (hodd : Odd p) :
    Nat.card (Roots (p^E) ((y : ZMod (p^E))^2)) =
      if y = 0 ∨ E ≤ 2*y.natAbs.factorization p then p^(E/2)
      else 2*p^(y.natAbs.factorization p) := by
  rw [primePower_integer_square_roots_natCard p E y hp hodd]
  simp only [localRootCount, Int.natAbs_eq_zero]

/-- A `Fintype.card` form for finite-product applications. -/
theorem primePower_square_roots_card (p E y : ℕ) (hp : p.Prime) (hodd : Odd p)
    [NeZero (p^E)] :
    Fintype.card (Roots (p^E) ((y : ZMod (p^E))^2)) = localRootCount p E y := by
  rw [← Nat.card_eq_fintype_card]
  exact primePower_square_roots_natCard p E y hp hodd

/-- The finite-cardinality version of the integral local factor. -/
theorem primePower_integer_square_roots_card (p E : ℕ) (y : ℤ)
    (hp : p.Prime) (hodd : Odd p) [NeZero (p^E)] :
    Fintype.card (Roots (p^E) ((y : ZMod (p^E))^2)) = localRootCount p E y.natAbs := by
  rw [← Nat.card_eq_fintype_card]
  exact primePower_integer_square_roots_natCard p E y hp hodd

end SerreMarkov.LocalRootFormula
