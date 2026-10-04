import SerreMarkov.PrimePowerRoots

/-!
# Square-zero roots modulo every prime power

The exponent is arbitrary. The square-zero residues are precisely the
multiples of `p^ceil(E/2)`, and there are `p^floor(E/2)` of them. The explicit
bijection includes exponent zero and the prime two.
-/

namespace SerreMarkov

theorem prime_power_dvd_square (p E z : ℕ) (hp : p.Prime) :
    p^E ∣ z^2 ↔ p^((E+1)/2) ∣ z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hz),
      hp.pow_dvd_iff_le_factorization hz, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega

theorem primePower_floor_ceil_split (p E : ℕ) :
    p^E = p^((E+1)/2) * p^(E/2) := by
  rw [← pow_add, show (E+1)/2 + E/2 = E by omega]

theorem primePower_square_zero_iff_general (p E : ℕ) (hp : p.Prime)
    (z : ZMod (p^E)) : z^2 = 0 ↔ p^((E+1)/2) ∣ z.val := by
  letI : NeZero (p^E) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hc : ((z.val^2 : ℕ) : ZMod (p^E)) = z^2 := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.natCast_eq_zero_iff, prime_power_dvd_square p E z.val hp]

/-- A complete enumeration: multiply the index by the ceiling half-power. -/
noncomputable def primePowerSquareZeroGeneralEquiv (p E : ℕ) (hp : p.Prime) :
    Fin (p^(E/2)) ≃ {z : ZMod (p^E) // z^2 = 0} := by
  letI : NeZero (p^E) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hs : 0 < p^((E+1)/2) := pow_pos hp.pos _
  have hbound (i : Fin (p^(E/2))) : p^((E+1)/2)*i.val < p^E := by
    rw [primePower_floor_ceil_split p E]
    exact Nat.mul_lt_mul_of_pos_left i.isLt hs
  refine {
    toFun := fun i => ⟨((p^((E+1)/2)*i.val : ℕ) : ZMod (p^E)), ?_⟩
    invFun := fun z => ⟨z.val.val / p^((E+1)/2), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (primePower_square_zero_iff_general p E hp _).mpr
    rw [ZMod.val_natCast_of_lt (hbound i)]
    exact dvd_mul_right _ _
  · apply (Nat.div_lt_iff_lt_mul hs).mpr
    rw [mul_comm, ← primePower_floor_ceil_split p E]
    exact ZMod.val_lt z.val
  · intro i
    apply Fin.ext
    change (((p^((E+1)/2)*i.val : ℕ) : ZMod (p^E)).val / p^((E+1)/2)) = i.val
    rw [ZMod.val_natCast_of_lt (hbound i), Nat.mul_div_cancel_left _ hs]
  · intro z
    apply Subtype.ext
    change ((p^((E+1)/2)*(z.val.val / p^((E+1)/2)) : ℕ) : ZMod (p^E)) = z.val
    rw [Nat.mul_div_cancel'
      ((primePower_square_zero_iff_general p E hp z.val).mp z.property), ZMod.natCast_zmod_val]

theorem primePowerSquareZeroGeneralEquiv_apply (p E : ℕ) (hp : p.Prime)
    (i : Fin (p^(E/2))) :
    (primePowerSquareZeroGeneralEquiv p E hp i).val =
      ((p^((E+1)/2)*i.val : ℕ) : ZMod (p^E)) := rfl

theorem primePowerSquareZeroGeneralEquiv_symm_val (p E : ℕ) (hp : p.Prime)
    (z : {z : ZMod (p^E) // z^2 = 0}) :
    ((primePowerSquareZeroGeneralEquiv p E hp).symm z).val =
      z.val.val / p^((E+1)/2) := rfl

theorem primePower_squareZeroRoots_general_natCard (p E : ℕ) (hp : p.Prime) :
    Nat.card {z : ZMod (p^E) // z^2 = 0} = p^(E/2) := by
  rw [← Nat.card_congr (primePowerSquareZeroGeneralEquiv p E hp), Nat.card_fin]

theorem primePower_squareZeroRoots_general_card (p E : ℕ) (hp : p.Prime)
    [NeZero (p^E)] :
    Fintype.card {z : ZMod (p^E) // z^2 = 0} = p^(E/2) := by
  rw [← Fintype.card_congr (primePowerSquareZeroGeneralEquiv p E hp), Fintype.card_fin]

/-- The zero-square branch applies to any right-hand side already equal to zero. -/
theorem primePower_square_roots_natCard_of_square_zero (p E : ℕ) (hp : p.Prime)
    (y : ZMod (p^E)) (hy : y^2 = 0) :
    Nat.card {z : ZMod (p^E) // z^2 = y^2} = p^(E/2) := by
  rw [hy]
  exact primePower_squareZeroRoots_general_natCard p E hp

/-- For a nonzero natural parameter, the manuscript's local threshold is
exactly `E ≤ 2*v`, where `v` is its exponent in the prime factorization. -/
theorem primePower_nat_square_zero_iff_factorization (p E y : ℕ) (hp : p.Prime)
    (hy : y ≠ 0) :
    (y : ZMod (p^E))^2 = 0 ↔ E ≤ 2*y.factorization p := by
  letI : NeZero (p^E) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff,
    hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hy), Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]

theorem primePower_square_roots_natCard_of_large_factorization (p E y : ℕ) (hp : p.Prime)
    (hy : y ≠ 0) (hv : E ≤ 2*y.factorization p) :
    Nat.card {z : ZMod (p^E) // z^2 = (y : ZMod (p^E))^2} = p^(E/2) :=
  primePower_square_roots_natCard_of_square_zero p E hp _
    ((primePower_nat_square_zero_iff_factorization p E y hp hy).mpr hv)

/-- Any root of a square with a common prime-power factor has at least
that factor in its least representative. This does not require `p ∤ u`. -/
theorem root_representative_divisible (p E b u : ℕ) (hp : p.Prime)
    (hb : 2*b ≤ E) (z : ZMod (p^E))
    (hz : z^2 = ((p^b*u : ℕ) : ZMod (p^E))^2) : p^b ∣ z.val := by
  letI : NeZero (p^E) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hc : z.val^2 ≡ (p^b*u)^2 [MOD p^E] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hz
  have hmod : p^(2*b) ∣ p^E := pow_dvd_pow p hb
  have hs : p^(2*b) ∣ (p^b*u)^2 :=
    (prime_square_power_dvd_square p b _ hp).mpr (dvd_mul_right _ _)
  exact (prime_square_power_dvd_square p b _ hp).mp ((hc.dvd_iff hmod).mpr hs)

end SerreMarkov
