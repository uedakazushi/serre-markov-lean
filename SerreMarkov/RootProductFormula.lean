import SerreMarkov.ChineseRoots
import SerreMarkov.LocalRootFormula
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Global products of modular square-root cardinalities

The finite product formula is proved by induction from the actual two-factor
CRT equivalence. Its prime-power specialization uses the proved factorization
of the positive modulus, rather than assuming a decomposition certificate.
-/

namespace SerreMarkov.RootProductFormula

open FamilyFiberFinite

theorem squareRoots_card_one (y : ℤ) :
    Nat.card (Roots 1 ((y : ZMod 1)^2)) = 1 := by
  letI : Nonempty (Roots 1 ((y : ZMod 1)^2)) := ⟨⟨(y : ZMod 1), rfl⟩⟩
  exact Nat.card_unique

/-- Pairwise coprime positive factors give the complete finite product
formula, including the empty product (modulus one). -/
theorem squareRoots_card_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hpos : ∀ i ∈ s, 0 < f i)
    (hcop : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j))) (y : ℤ) :
    Nat.card (Roots (∏ i ∈ s, f i) ((y : ZMod (∏ i ∈ s, f i))^2)) =
      ∏ i ∈ s, Nat.card (Roots (f i) ((y : ZMod (f i))^2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using squareRoots_card_one y
  | @insert a s ha ih =>
      have hposa : 0 < f a := hpos a (Finset.mem_insert_self a s)
      have hposs : ∀ i ∈ s, 0 < f i :=
        fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      have hcops : (s : Set ι).Pairwise (fun i j => Nat.Coprime (f i) (f j)) := by
        intro i hi j hj hij
        exact hcop (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
      have hcopas : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro j hj
        exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hj)
          (fun he => ha (he.symm ▸ hj))
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [ChineseRoots.squareRoots_card_mul (f a) (∏ i ∈ s, f i)
        hposa (Finset.prod_pos hposs) hcopas y, ih hposs hcops]

theorem factorization_modulus_product (m : ℕ) (hm : 0 < m) :
    (∏ p ∈ m.factorization.support, p ^ m.factorization p) = m := by
  exact Nat.factorization_prod_pow_eq_self hm.ne'

theorem factorization_prime_powers_pairwise (m : ℕ) :
    (m.factorization.support : Set ℕ).Pairwise
      (fun p q => Nat.Coprime (p ^ m.factorization p) (q ^ m.factorization q)) := by
  intro p hp q hq hpq
  exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) hpq

/-- Every positive modulus is reduced to its actual prime-power local
root-set cardinalities. No oddness assumption is needed for CRT. -/
theorem squareRoots_card_factorization (m : ℕ) (hm : 0 < m) (y : ℤ) :
    Nat.card (Roots m ((y : ZMod m)^2)) =
      ∏ p ∈ m.factorization.support,
        Nat.card (Roots (p ^ m.factorization p) ((y : ZMod (p ^ m.factorization p))^2)) := by
  have hpos : ∀ p ∈ m.factorization.support, 0 < p ^ m.factorization p := by
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have h := squareRoots_card_finset_prod m.factorization.support
    (fun p => p ^ m.factorization p) hpos (factorization_prime_powers_pairwise m) y
  rw [factorization_modulus_product m hm] at h
  exact h

theorem odd_prime_of_mem_factorization (m : ℕ) (hodd : Odd m)
    (p : ℕ) (hp : p ∈ m.factorization.support) : Odd p := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact hodd.not_two_dvd_nat (heven.two_dvd.trans (Nat.dvd_of_mem_primeFactors hp))

/-- The complete global count for an arbitrary integral parameter modulo a
positive odd modulus, with all prime-power factors evaluated. -/
theorem squareRoots_card_odd_product (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (Roots m ((y : ZMod m)^2)) =
      ∏ p ∈ m.factorization.support,
        LocalRootFormula.localRootCount p (m.factorization p) y.natAbs := by
  rw [squareRoots_card_factorization m hm y]
  apply Finset.prod_congr rfl
  intro p hp
  exact LocalRootFormula.primePower_integer_square_roots_natCard p (m.factorization p) y
    (Nat.prime_of_mem_primeFactors hp) (odd_prime_of_mem_factorization m hodd p hp)

/-- The local valuation branches are displayed in the global product. -/
theorem squareRoots_card_odd_formula (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (Roots m ((y : ZMod m)^2)) =
      ∏ p ∈ m.factorization.support,
        if y = 0 ∨ m.factorization p ≤ 2*y.natAbs.factorization p
        then p^(m.factorization p / 2) else 2*p^(y.natAbs.factorization p) := by
  simpa only [LocalRootFormula.localRootCount, Int.natAbs_eq_zero] using
    squareRoots_card_odd_product m hm hodd y

/-- Taking the sign quotient adds exactly the possible zero root. This
counts the actual normalized candidates in the same family lattice fiber. -/
theorem odd_lattice_candidate_product (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    2 * Fintype.card (Candidate m y) =
      (∏ p ∈ m.factorization.support,
        LocalRootFormula.localRootCount p (m.factorization p) y.natAbs) +
        if (y : ZMod m)^2 = 0 then 1 else 0 := by
  rw [odd_lattice_candidate_count m hodd y, squareRoots_card_odd_product m hm hodd y]

theorem odd_lattice_candidate_formula (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Fintype.card (Candidate m y) =
      ((∏ p ∈ m.factorization.support,
        if y = 0 ∨ m.factorization p ≤ 2*y.natAbs.factorization p
        then p^(m.factorization p / 2) else 2*p^(y.natAbs.factorization p)) +
        if (y : ZMod m)^2 = 0 then 1 else 0) / 2 := by
  have h := odd_lattice_candidate_product m hm hodd y
  simp only [LocalRootFormula.localRootCount, Int.natAbs_eq_zero] at h
  omega

/-- The same explicit formula counts the actual modular roots modulo sign. -/
theorem odd_root_sign_quotient_formula (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (Quotient (rootSignSetoid m ((y : ZMod m)^2))) =
      ((∏ p ∈ m.factorization.support,
        if y = 0 ∨ m.factorization p ≤ 2*y.natAbs.factorization p
        then p^(m.factorization p / 2) else 2*p^(y.natAbs.factorization p)) +
        if (y : ZMod m)^2 = 0 then 1 else 0) / 2 := by
  rw [← odd_candidate_card_eq_root_sign_quotient m hodd y]
  exact odd_lattice_candidate_formula m hm hodd y

end SerreMarkov.RootProductFormula
