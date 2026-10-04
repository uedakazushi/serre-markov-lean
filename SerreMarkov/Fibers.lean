import SerreMarkov.Matrix
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# An explicit integral isometry with distinct mutation orbits

This file proves the concrete counterexample in Proposition 11.1 of the
manuscript. It does not depend on the global classification. The orbit
obstruction is an invariant in `ZMod 9`, proved by checking the ten generators
on the twelve signed perfect matchings. Every check produces a kernel proof.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace SerreMarkov
namespace Fibers

def source : Six := family 9 0
def target : Six := family 6 3

/-- The integral change of basis displayed in the manuscript. -/
def isometryMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 4, 4, -1;
     -2, -5, -6, -1;
     2, 6, 7, 1;
     1, -2, -2, 0]

/-- Six upper triangular coefficients after reduction modulo nine. -/
@[ext] structure Six9 where
  a : ZMod 9
  b : ZMod 9
  c : ZMod 9
  d : ZMod 9
  e : ZMod 9
  f : ZMod 9
  deriving DecidableEq

/-- Entrywise reduction of an integral Gram matrix. -/
def reduce9 (z : Six) : Six9 := ⟨z.a, z.b, z.c, z.d, z.e, z.f⟩

/-- The same polynomial generators over the residue ring. -/
def step9 : Generator → Six9 → Six9
  | .m1, z => ⟨z.a, z.a*z.b-z.d, z.a*z.c-z.e, z.b, z.c, z.f⟩
  | .i1, z => ⟨z.a, z.d, z.e, z.a*z.d-z.b, z.a*z.e-z.c, z.f⟩
  | .m2, z => ⟨z.a*z.d-z.b, z.a, z.c, z.d, z.d*z.e-z.f, z.e⟩
  | .i2, z => ⟨z.b, z.b*z.d-z.a, z.c, z.d, z.f, z.d*z.f-z.e⟩
  | .m3, z => ⟨z.a, z.f*z.b-z.c, z.b, z.f*z.d-z.e, z.d, z.f⟩
  | .i3, z => ⟨z.a, z.c, z.f*z.c-z.b, z.e, z.f*z.e-z.d, z.f⟩
  | .s1, z => ⟨-z.a, -z.b, -z.c, z.d, z.e, z.f⟩
  | .s2, z => ⟨-z.a, z.b, z.c, -z.d, -z.e, z.f⟩
  | .s3, z => ⟨z.a, -z.b, z.c, -z.d, z.e, -z.f⟩
  | .s4, z => ⟨z.a, z.b, -z.c, z.d, -z.e, -z.f⟩

/-- The three perfect matchings, with independent signs on their two edges. -/
def matchingStates : List Six9 :=
  [⟨2,0,0,0,0,2⟩, ⟨2,0,0,0,0,-2⟩,
   ⟨-2,0,0,0,0,2⟩, ⟨-2,0,0,0,0,-2⟩,
   ⟨0,2,0,0,2,0⟩, ⟨0,2,0,0,-2,0⟩,
   ⟨0,-2,0,0,2,0⟩, ⟨0,-2,0,0,-2,0⟩,
   ⟨0,0,2,2,0,0⟩, ⟨0,0,2,-2,0,0⟩,
   ⟨0,0,-2,2,0,0⟩, ⟨0,0,-2,-2,0,0⟩]

/-- Being a signed perfect matching is preserved by every generator. -/
theorem matchingStates_closed (g : Generator) (z : Six9)
    (hz : z ∈ matchingStates) : step9 g z ∈ matchingStates := by
  simp only [matchingStates, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  all_goals cases g <;> decide

/-- Reduction commutes with every mutation and sign change. -/
theorem reduce9_step (g : Generator) (z : Six) :
    reduce9 (step g z) = step9 g (reduce9 z) := by
  cases g <;> apply Six9.ext <;> simp [reduce9, step9, step, mu1, mu2, mu3,
    inv1, inv2, inv3, eps1, eps2, eps3, eps4]

/-- Every mutation word starting at a matching stays a matching modulo nine. -/
theorem applyWord_matching (w : List Generator) (z : Six)
    (hz : reduce9 z ∈ matchingStates) : reduce9 (applyWord z w) ∈ matchingStates := by
  induction w generalizing z with
  | nil => exact hz
  | cons g gs ih =>
    apply ih
    rw [reduce9_step]
    exact matchingStates_closed g (reduce9 z) hz

theorem source_is_matching : reduce9 source ∈ matchingStates := by decide

theorem target_not_matching : reduce9 target ∉ matchingStates := by decide

/-- The two displayed matrices lie in distinct signed mutation orbits. -/
theorem source_target_not_reachable : ¬ Reachable source target := by
  rintro ⟨w, hw⟩
  apply target_not_matching
  rw [← hw]
  exact applyWord_matching w source source_is_matching

/-- Both matrices satisfy the two Serre--Markov equations. -/
theorem source_isSolution : isSolution source := family_isSolution 9 0

theorem target_isSolution : isSolution target := family_isSolution 6 3

/-- The witness is unimodular with determinant one. -/
theorem isometryMatrix_det : isometryMatrix.det = 1 := by
  norm_num [isometryMatrix, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  all_goals decide

/-- The same witness preserves the nonsymmetric integral pairing. -/
theorem isometryMatrix_congruence :
    isometryMatrix.transpose * gram source * isometryMatrix = gram target := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isometryMatrix, gram, source, target, family, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ]

/-- The two examples have the nondegenerate nilpotence type used in the
Gorodentsev--Kuleshov rank-four setting. -/
theorem source_regular : shiftedSerre source ^ 4 = 0 ∧ shiftedSerre source ^ 3 ≠ 0 := by
  constructor
  · exact family_fourth_power 9 0
  · intro h
    have hz := (family_cube_eq_zero_iff 9 0).mp h
    norm_num at hz

theorem target_regular : shiftedSerre target ^ 4 = 0 ∧ shiftedSerre target ^ 3 ≠ 0 := by
  constructor
  · exact family_fourth_power 6 3
  · intro h
    have hz := (family_cube_eq_zero_iff 6 3).mp h
    norm_num at hz

/-- A direct, classification-independent certificate of failure of mutation
transitivity for unimodular rank-four integral bilinear forms. -/
theorem integral_isometry_distinct_mutation_orbits :
    isSolution source ∧ isSolution target ∧
    (∃ B : Matrix (Fin 4) (Fin 4) ℤ,
      B.det = 1 ∧ B.transpose * gram source * B = gram target) ∧
    ¬ Reachable source target :=
  ⟨source_isSolution, target_isSolution,
    ⟨isometryMatrix, isometryMatrix_det, isometryMatrix_congruence⟩,
    source_target_not_reachable⟩

/-- Complete concrete matrix certificate, including nondegenerate Serre type. -/
theorem regular_integral_isometry_distinct_mutation_orbits :
    shiftedSerre source ^ 4 = 0 ∧ shiftedSerre source ^ 3 ≠ 0 ∧
    shiftedSerre target ^ 4 = 0 ∧ shiftedSerre target ^ 3 ≠ 0 ∧
    (∃ B : Matrix (Fin 4) (Fin 4) ℤ,
      B.det = 1 ∧ B.transpose * gram source * B = gram target) ∧
    ¬ Reachable source target :=
  ⟨source_regular.1, source_regular.2, target_regular.1, target_regular.2,
    ⟨isometryMatrix, isometryMatrix_det, isometryMatrix_congruence⟩,
    source_target_not_reachable⟩

/-- The arithmetic step underlying the zero-square prime-power examples.
In fact no primality assumption is needed. -/
theorem square_divisibility (a z : ℤ) (e : ℕ) :
    a ^ (2 * e) ∣ z ^ 2 ↔ a ^ e ∣ z := by
  rw [Nat.mul_comm 2 e, pow_mul]
  exact Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)

/-- The square-congruence shortcut cannot be used for even moduli. -/
theorem even_square_criterion_fails :
    (0 : ZMod 4) ^ 2 = (2 : ZMod 4) ^ 2 ∧
    ¬ ∃ t : ZMod 4, (2 : ZMod 4) = 0 - 2 * t ∧ t * (t - 0) = 0 := by
  decide

end Fibers
end SerreMarkov
