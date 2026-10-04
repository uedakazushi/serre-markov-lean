import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace SerreMarkov

/-- The two simultaneous congruences appearing in the lattice isometry criterion.
This definition alone makes no claim that a lattice isometry exists. -/
def CongruenceWitness {R : Type*} [CommRing R] (y y' : R) : Prop :=
  ∃ t : R, y' = y - 2 * t ∧ t * (t - y) = 0

/-- The congruence criterion reduces to equality of squares whenever 2 is a unit.
This algebraic implication is independent of the orbit classification. -/
theorem congruenceWitness_iff_square {R : Type*} [CommRing R]
    (h2 : IsUnit (2 : R)) (y y' : R) :
    CongruenceWitness y y' ↔ y' ^ 2 = y ^ 2 := by
  rcases h2 with ⟨u, hu⟩
  have hinv : (2 : R) * ↑(u⁻¹) = 1 := by
    rw [← hu]
    simp
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [ht]
    calc
      (y - 2 * t) ^ 2 = y ^ 2 + 4 * (t * (t - y)) := by ring
      _ = y ^ 2 := by rw [hz]; ring
  · intro hs
    let t : R := (y - y') * ↑(u⁻¹)
    have ht : (2 : R) * t = y - y' := by
      dsimp [t]
      calc
        2 * ((y - y') * ↑(u⁻¹)) = (y - y') * (2 * ↑(u⁻¹)) := by ring
        _ = y - y' := by rw [hinv]; ring
    refine ⟨t, ?_, ?_⟩
    · calc
        y' = y - (y - y') := by ring
        _ = y - 2 * t := by rw [ht]
    · have hz : (2 : R) * (2 * (t * (t - y))) = 0 := by
        calc
          2 * (2 * (t * (t - y))) = (2 * t) ^ 2 - 2 * (2 * t) * y := by ring
          _ = (y - y') ^ 2 - 2 * (y - y') * y := by rw [ht]
          _ = y' ^ 2 - y ^ 2 := by ring
          _ = 0 := by rw [hs]; ring
      have hc : (t * (t - y)) =
          ↑(u⁻¹) * (↑(u⁻¹) * (2 * (2 * (t * (t - y))))) := by
        have hi : (↑(u⁻¹) : R) * 2 = 1 := by rw [mul_comm]; exact hinv
        simp only [← mul_assoc, hi, one_mul]
      rw [hc, hz]
      simp

theorem odd_modulus_congruence_iff_square (m : ℕ) (hm : Odd m)
    (y y' : ZMod m) : CongruenceWitness y y' ↔ y' ^ 2 = y ^ 2 := by
  apply congruenceWitness_iff_square
  exact (ZMod.isUnit_iff_coprime 2 m).2 hm.coprime_two_left

theorem integer_congruences_of_odd_square (m : ℕ) (hm : Odd m) (y y' : ℤ)
    (hs : (y' : ZMod m)^2 = (y : ZMod m)^2) :
    ∃ t : ℤ, (m : ℤ) ∣ y-y'-2*t ∧ (m : ℤ) ∣ t*(t-y) := by
  have hmne : m ≠ 0 := by
    rintro rfl
    simp at hm
  letI : NeZero m := ⟨hmne⟩
  obtain ⟨t, ht, hz⟩ := (odd_modulus_congruence_iff_square m hm _ _).2 hs
  refine ⟨(t.val : ℤ), ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    rw [ht]
    ring
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz

/-- The manuscript's caution about even moduli is a checked counterexample. -/
theorem even_modulus_counterexample :
    (0 : ZMod 4) ^ 2 = (2 : ZMod 4) ^ 2 ∧
      ¬ CongruenceWitness (0 : ZMod 4) 2 := by
  unfold CongruenceWitness
  decide

/-- The zero-root divisibility statement underlying the prime-square-power
fiber formula. This is arithmetic alone and does not assume the classification. -/
theorem prime_square_power_dvd_square (p e z : ℕ) (hp : p.Prime) :
    p ^ (2*e) ∣ z ^ 2 ↔ p ^ e ∣ z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hz),
      hp.pow_dvd_iff_le_factorization hz, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    omega

end SerreMarkov
