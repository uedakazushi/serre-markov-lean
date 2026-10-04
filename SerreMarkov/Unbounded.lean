import SerreMarkov.Isometry
import SerreMarkov.Support

/-!
# Arbitrarily large families of distinct mutation orbits in one integral lattice

For every `e`, this file constructs `e+1` solutions whose Euler forms are
integrally isometric, but whose signed mutation orbits are pairwise distinct.
The proof uses the matching-support congruence obstruction and the constructive
isometry criterion only. No geometric classification theorem is used.
-/

namespace SerreMarkov
namespace Unbounded

set_option maxHeartbeats 1000000

/-- The fixed total parameter for the `e`-th construction. -/
def total (e : ℕ) : ℕ := 3 ^ (2 * e)

/-- The parameters have distinct three-adic divisibility; the final one is zero. -/
def parameter (e : ℕ) (j : Fin (e+1)) : ℕ :=
  if j.val = e then 0 else 3 ^ (e + j.val)

def reference (e : ℕ) : Six := family (total e) 0

def representative (e : ℕ) (j : Fin (e+1)) : Six :=
  family ((total e : ℤ) - parameter e j) (parameter e j)

theorem total_odd (e : ℕ) : Odd (total e) := by
  exact (show Odd (3 : ℕ) by decide).pow

theorem total_pos (e : ℕ) : 0 < total e := by
  exact pow_pos (by decide : (0 : ℕ) < 3) _

theorem parameter_square_divisible (e : ℕ) (j : Fin (e+1)) :
    total e ∣ parameter e j ^ 2 := by
  unfold total parameter
  split_ifs with hj
  · simp
  · rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)

/-- An integral determinant-one isometry to the common reference lattice. -/
theorem representative_isometric (e : ℕ) (j : Fin (e+1)) :
    ∃ B : Mat4, B.det = 1 ∧
      B.transpose * gram (reference e) * B = gram (representative e j) := by
  have hzero := (ZMod.natCast_eq_zero_iff (parameter e j ^ 2) (total e)).mpr
    (parameter_square_divisible e j)
  have hs : ((parameter e j : ℤ) : ZMod (total e)) ^ 2 =
      ((0 : ℤ) : ZMod (total e)) ^ 2 := by
    simpa using hzero
  simpa only [reference, representative, sub_zero] using
    family_isometry_of_odd_square (total e) (total_odd e) 0 (parameter e j) hs

/-- The modulus that distinguishes a smaller index from every larger index. -/
def separator (e : ℕ) (i : Fin (e+1)) : ℕ := 3 ^ (e + i.val + 1)

theorem separator_divides_total (e : ℕ) (i j : Fin (e+1)) (hij : i.val < j.val) :
    separator e i ∣ total e := by
  unfold separator total
  exact pow_dvd_pow 3 (by have hj := j.isLt; omega)

theorem separator_divides_larger (e : ℕ) (i j : Fin (e+1)) (hij : i.val < j.val) :
    separator e i ∣ parameter e j := by
  unfold parameter
  split_ifs with hj
  · exact dvd_zero _
  · unfold separator
    exact pow_dvd_pow 3 (by omega)

theorem separator_not_divides_smaller (e : ℕ) (i j : Fin (e+1))
    (hij : i.val < j.val) : ¬ separator e i ∣ parameter e i := by
  have hi : i.val ≠ e := by have hj := j.isLt; omega
  simp only [separator, parameter, hi, if_false]
  rw [Nat.pow_dvd_pow_iff_le_right (by decide : (1 : ℕ) < 3)]
  omega

/-- A larger index cannot mutate to a smaller index. -/
theorem larger_not_reachable_smaller (e : ℕ) (i j : Fin (e+1))
    (hij : i.val < j.val) : ¬ Reachable (representative e j) (representative e i) := by
  have hm : (separator e i : ℤ) ∣ (total e : ℤ) :=
    Int.natCast_dvd_natCast.mpr (separator_divides_total e i j hij)
  have hy : (separator e i : ℤ) ∣ (parameter e j : ℤ) :=
    Int.natCast_dvd_natCast.mpr (separator_divides_larger e i j hij)
  have hy' : ¬ (separator e i : ℤ) ∣ (parameter e i : ℤ) := by
    exact fun h => separator_not_divides_smaller e i j hij
      (Int.natCast_dvd_natCast.mp h)
  exact family_not_reachable_of_divisibility (separator e i)
    ((total e : ℤ) - parameter e j) (parameter e j)
    ((total e : ℤ) - parameter e i) (parameter e i)
    (dvd_sub hm hy) hy hy'

/-- Every pair of distinct indices gives distinct signed mutation orbits. -/
theorem representatives_pairwise_not_reachable (e : ℕ) (i j : Fin (e+1))
    (hij : i ≠ j) : ¬ Reachable (representative e i) (representative e j) := by
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · intro h
    exact larger_not_reachable_smaller e i j hlt (reachable_symm h)
  · exact larger_not_reachable_smaller e j i hgt

theorem reference_solution (e : ℕ) : isSolution (reference e) :=
  family_isSolution (total e) 0

theorem representative_solution (e : ℕ) (i : Fin (e+1)) :
    isSolution (representative e i) :=
  family_isSolution ((total e : ℤ) - parameter e i) (parameter e i)

/-- These examples all have nilpotence index exactly four. -/
theorem reference_regular (e : ℕ) :
    shiftedSerre (reference e) ^ 4 = 0 ∧ shiftedSerre (reference e) ^ 3 ≠ 0 := by
  constructor
  · exact family_fourth_power (total e) 0
  · intro h
    have hz := (family_cube_eq_zero_iff (total e) 0).mp h
    have hp : (0 : ℤ) < (total e : ℤ) := by exact_mod_cast total_pos e
    simp only [add_zero] at hz
    omega

theorem representative_regular (e : ℕ) (i : Fin (e+1)) :
    shiftedSerre (representative e i) ^ 4 = 0 ∧
    shiftedSerre (representative e i) ^ 3 ≠ 0 := by
  constructor
  · exact family_fourth_power ((total e : ℤ) - parameter e i) (parameter e i)
  · intro h
    have hz := (family_cube_eq_zero_iff
      ((total e : ℤ) - parameter e i) (parameter e i)).mp h
    have hp : (0 : ℤ) < (total e : ℤ) := by exact_mod_cast total_pos e
    omega

/-- There is no uniform bound on the number of signed mutation orbits of
exceptional bases of a rank-four integral Euler lattice: `n+1` explicit
representatives exist for every requested `n`. -/
theorem unbounded_isometry_fibers (n : ℕ) :
    ∃ base : Six, ∃ reps : Fin (n+1) → Six,
      isSolution base ∧
      (shiftedSerre base ^ 4 = 0 ∧ shiftedSerre base ^ 3 ≠ 0) ∧
      (∀ i, isSolution (reps i)) ∧
      (∀ i, shiftedSerre (reps i) ^ 4 = 0 ∧ shiftedSerre (reps i) ^ 3 ≠ 0) ∧
      (∀ i, ∃ B : Mat4, B.det = 1 ∧ B.transpose * gram base * B = gram (reps i)) ∧
      (∀ i j, i ≠ j → ¬ Reachable (reps i) (reps j)) :=
  ⟨reference n, representative n, reference_solution n, reference_regular n,
    representative_solution n, representative_regular n, representative_isometric n,
    representatives_pairwise_not_reachable n⟩

/-- The representative indices inject into the actual mutation quotient. -/
theorem orbit_map_injective (e : ℕ) :
    Function.Injective (fun i : Fin (e+1) =>
      Quotient.mk reachabilitySetoid (representative e i)) := by
  intro i j h
  by_contra hij
  exact representatives_pairwise_not_reachable e i j hij (Quotient.exact h)

end Unbounded
end SerreMarkov
