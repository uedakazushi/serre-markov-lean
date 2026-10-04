import SerreMarkov.IsometryNecessary

/-! # A finite decision procedure for integral family isometry

The test checks the simultaneous congruences in `ZMod m`, also when `m` is even.
Its correctness concerns actual integral congruence matrices, rather than a
bounded matrix search. It does not decide mutation equivalence of arbitrary
solutions.
-/

namespace SerreMarkov

open Matrix

theorem integer_congruences_iff_mod_witness (m : ℕ) [NeZero m] (y y' : ℤ) :
    (∃ t : ℤ, (m : ℤ) ∣ y-y'-2*t ∧ (m : ℤ) ∣ t*(t-y)) ↔
      CongruenceWitness (y : ZMod m) (y' : ZMod m) := by
  constructor
  · exact congruenceWitness_of_integer_congruences m y y'
  · rintro ⟨t, ht, hz⟩
    refine ⟨(t.val : ℤ), ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
      push_cast
      rw [ZMod.natCast_zmod_val, ht]
      ring
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hz

def familyIsometryTest (m : ℕ) [NeZero m] (y y' : ℤ) : Bool :=
  decide (∃ t : ZMod m, (y' : ZMod m) = (y : ZMod m) - 2*t ∧
    t*(t-(y : ZMod m)) = 0)

/-- A terminating finite test decides existence of an integral unit congruence
between two family lattices of the same positive total. -/
theorem familyIsometryTest_correct (m : ℕ) [NeZero m] (y y' : ℤ) :
    familyIsometryTest m y y' = true ↔
      ∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
        Bᵀ * gram (family ((m : ℤ)-y) y) * B =
          gram (family ((m : ℤ)-y') y') := by
  rw [family_isometry_iff_divisibility _ _ _ (by exact_mod_cast (NeZero.ne m))]
  rw [integer_congruences_iff_mod_witness]
  simp only [familyIsometryTest, decide_eq_true_eq, CongruenceWitness]

theorem even_test_distinguishes_square_counterexample :
    familyIsometryTest 4 0 2 = false := by decide +kernel

theorem composite_same_lattice_test :
    familyIsometryTest 15 1 4 = true := by decide +kernel

end SerreMarkov
