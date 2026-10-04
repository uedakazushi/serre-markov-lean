import SerreMarkov.FamilyFiberFinite
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Prime.Lemmas

/-! # The two unit square roots at odd prime powers

For an odd prime `p` and an integer `y` not divisible by `p`, the roots of
`y²` modulo `p^e` (`e>0`) are exactly `y` and `-y`.  The equivalence below
uses the actual square-root subtype from `FamilyFiberFinite`.
-/

namespace SerreMarkov.UnitPrimePowerRoots

open FamilyFiberFinite
noncomputable section

private theorem prime_not_dvd_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ (p : ℤ) ∣ 2 := by
  intro hd
  have hd' : p ∣ 2 := Int.natCast_dvd_natCast.mp hd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd'
  subst p
  norm_num at hodd

private theorem prime_not_dvd_twice {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) : ¬ (p : ℤ) ∣ 2*y := by
  intro hd
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
  · exact prime_not_dvd_two hp hodd h
  · exact hy h

/-- At most one of the two linear factors can be divisible by an odd prime
that does not divide `y`; the whole prime power divides the other factor. -/
theorem primePower_dvd_difference_or_sum {p e : ℕ} (hp : p.Prime)
    (hodd : Odd p) (y a : ℤ) (hy : ¬ (p : ℤ) ∣ y)
    (hprod : (p : ℤ)^e ∣ (a-y)*(a+y)) :
    (p : ℤ)^e ∣ a-y ∨ (p : ℤ)^e ∣ a+y := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hd : (p : ℤ) ∣ a-y
  · have hnot : ¬ (p : ℤ) ∣ a+y := by
      intro hs
      have htwice : (p : ℤ) ∣ 2*y := by
        convert hs.sub hd using 1 <;> ring
      exact prime_not_dvd_twice hp hodd y hy htwice
    exact Or.inl (hpZ.pow_dvd_of_dvd_mul_right e hnot hprod)
  · exact Or.inr (hpZ.pow_dvd_of_dvd_mul_left e hd hprod)

/-- The defining quadratic congruence has exactly the two possible signs. -/
theorem square_eq_iff_sign {p e : ℕ} (hp : p.Prime) (hodd : Odd p)
    (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) (x : ZMod (p^e)) :
    x^2 = (y : ZMod (p^e))^2 ↔ x = y ∨ x = -y := by
  letI : NeZero (p^e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · intro hx
    let a : ℤ := x.val
    have ha : (a : ZMod (p^e)) = x := by
      simp only [a, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hcast : (((a-y)*(a+y) : ℤ) : ZMod (p^e)) = 0 := by
      push_cast
      rw [ha]
      calc
        (x-(y : ZMod (p^e)))*(x+y) = x^2-(y : ZMod (p^e))^2 := by ring
        _ = 0 := sub_eq_zero.mpr hx
    have hdiv : (p : ℤ)^e ∣ (a-y)*(a+y) := by
      simpa only [Nat.cast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((a-y)*(a+y)) (p^e)).mp hcast
    rcases primePower_dvd_difference_or_sum hp hodd y a hy hdiv with hm | hp'
    · left
      have hz : ((a-y : ℤ) : ZMod (p^e)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hm)
      simpa only [Int.cast_sub, ha, sub_eq_zero] using hz
    · right
      have hz : ((a+y : ℤ) : ZMod (p^e)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hp')
      have hsum : x+(y : ZMod (p^e)) = 0 := by simpa only [Int.cast_add, ha] using hz
      exact eq_neg_of_add_eq_zero_left hsum
  · rintro (rfl | rfl) <;> simp

/-- The two signs are distinct when the exponent is positive. -/
theorem unit_ne_neg {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e)
    (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    (y : ZMod (p^e)) ≠ -y := by
  intro h
  have hcast : ((2*y : ℤ) : ZMod (p^e)) = 0 := by
    push_cast
    have hs : (y : ZMod (p^e))+(y : ZMod (p^e)) = 0 := by nth_rw 1 [h]; simp
    simpa only [two_mul] using hs
  have hd : (p : ℤ)^e ∣ 2*y := by
    simpa only [Nat.cast_pow] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2*y) (p^e)).mp hcast
  exact prime_not_dvd_twice hp hodd y hy
    ((dvd_pow_self (p : ℤ) (Nat.ne_of_gt he)).trans hd)

/-- The sign index `false` is the original root and `true` its negation. -/
def signRoot (p e : ℕ) (y : ℤ) (b : Bool) :
    Roots (p^e) ((y : ZMod (p^e))^2) :=
  ⟨if b then -(y : ZMod (p^e)) else y, by cases b <;> simp⟩

/-- An explicit sign parametrization of every unit square root. -/
def unitRootsEquiv {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e)
    (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    Bool ≃ Roots (p^e) ((y : ZMod (p^e))^2) :=
  Equiv.ofBijective (signRoot p e y) ⟨by
    intro b c h
    have hv := congrArg Subtype.val h
    cases b <;> cases c <;> simp only [signRoot, Bool.false_eq_true,
      Bool.true_eq_false, Bool.cond_false, Bool.cond_true] at hv ⊢
    · exact False.elim (unit_ne_neg hp hodd he y hy hv)
    · exact False.elim (unit_ne_neg hp hodd he y hy hv.symm), by
    intro x
    rcases (square_eq_iff_sign hp hodd y hy x.val).mp x.property with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩⟩

@[simp] theorem unitRootsEquiv_false {p e : ℕ} (hp : p.Prime) (hodd : Odd p)
    (he : 0 < e) (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    (unitRootsEquiv hp hodd he y hy false).val = (y : ZMod (p^e)) := rfl

@[simp] theorem unitRootsEquiv_true {p e : ℕ} (hp : p.Prime) (hodd : Odd p)
    (he : 0 < e) (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    (unitRootsEquiv hp hodd he y hy true).val = -(y : ZMod (p^e)) := rfl

/-- The local unit factor in the odd-prime-power root-count product is `2`. -/
theorem unitRoots_natCard {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e)
    (y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    Nat.card (Roots (p^e) ((y : ZMod (p^e))^2)) = 2 := by
  rw [← Nat.card_congr (unitRootsEquiv hp hodd he y hy), Nat.card_eq_fintype_card,
    Fintype.card_bool]

end
end SerreMarkov.UnitPrimePowerRoots
