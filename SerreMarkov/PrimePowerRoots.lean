import SerreMarkov.Arithmetic
import Mathlib.Data.Fintype.Card

/-! # Exact finite square-zero root counts for prime square powers

These are finite congruence-root counts. No statement about the number of
mutation orbits is used or inferred.
-/

namespace SerreMarkov

/-- Rewrite the even prime power as a square. -/
theorem squarePower_eq_mul (p e : ℕ) : p^(2*e) = p^e*p^e := by
  rw [show 2*e=e+e by omega, pow_add]

/-- A residue is square-zero exactly when its least representative is
multiple of the half prime power. -/
theorem primePower_square_zero_iff (p e : ℕ) (hp : p.Prime)
    (z : ZMod (p^(2*e))) : z^2=0 ↔ p^e ∣ z.val := by
  letI : NeZero (p^(2*e)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hc : ((z.val^2 : ℕ) : ZMod (p^(2*e))) = z^2 := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.natCast_eq_zero_iff, prime_square_power_dvd_square p e z.val hp]

/-- Every square-zero residue is uniquely `p^e*i`, with `0≤i<p^e`. -/
noncomputable def primePowerSquareZeroEquiv (p e : ℕ) (hp : p.Prime) :
    Fin (p^e) ≃ {z : ZMod (p^(2*e)) // z^2=0} := by
  letI : NeZero (p^(2*e)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hq : 0 < p^e := pow_pos hp.pos _
  have hbound (i : Fin (p^e)) : p^e*i.val < p^(2*e) := by
    rw [squarePower_eq_mul]
    exact Nat.mul_lt_mul_of_pos_left i.isLt hq
  refine {
    toFun := fun i => ⟨((p^e*i.val : ℕ) : ZMod (p^(2*e))), ?_⟩
    invFun := fun z => ⟨z.val.val/(p^e), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (primePower_square_zero_iff p e hp _).mpr
    rw [ZMod.val_natCast_of_lt (hbound i)]
    exact dvd_mul_right _ _
  · apply (Nat.div_lt_iff_lt_mul hq).mpr
    rw [← squarePower_eq_mul]
    exact ZMod.val_lt z.val
  · intro i
    apply Fin.ext
    change (((p^e*i.val : ℕ) : ZMod (p^(2*e))).val/(p^e)) = i.val
    rw [ZMod.val_natCast_of_lt (hbound i), Nat.mul_div_cancel_left _ hq]
  · intro z
    apply Subtype.ext
    change ((p^e*(z.val.val/(p^e)) : ℕ) : ZMod (p^(2*e))) = z.val
    rw [Nat.mul_div_cancel' ((primePower_square_zero_iff p e hp z.val).mp z.property),
      ZMod.natCast_zmod_val]

theorem primePowerSquareZeroEquiv_apply (p e : ℕ) (hp : p.Prime) (i : Fin (p^e)) :
    (primePowerSquareZeroEquiv p e hp i).val =
      ((p^e*i.val : ℕ) : ZMod (p^(2*e))) := rfl

theorem primePowerSquareZeroEquiv_symm_val (p e : ℕ) (hp : p.Prime)
    (z : {z : ZMod (p^(2*e)) // z^2=0}) :
    ((primePowerSquareZeroEquiv p e hp).symm z).val = z.val.val/(p^e) := rfl

/-- There are exactly `p^e` square-zero roots, including the case `e=0`. -/
theorem primePower_squareZeroRoots_natCard (p e : ℕ) (hp : p.Prime) :
    Nat.card {z : ZMod (p^(2*e)) // z^2=0} = p^e := by
  rw [← Nat.card_congr (primePowerSquareZeroEquiv p e hp), Nat.card_fin]

theorem primePower_squareZeroRoots_card (p e : ℕ) (hp : p.Prime)
    [NeZero (p^(2*e))] :
    Fintype.card {z : ZMod (p^(2*e)) // z^2=0} = p^e := by
  rw [← Fintype.card_congr (primePowerSquareZeroEquiv p e hp), Fintype.card_fin]

end SerreMarkov
