import SerreMarkov.Mutations

/-!
# A local obstruction to one-step coordinate-height descent

This explicit solution lies in the orbit of `F(1,0)`, but every positive or
negative elementary mutation increases the sum of the absolute coordinates.
Thus a proof by strictly decreasing that height needs more than one mutation at
a time. This is an obstruction to that descent strategy, not to classification.
-/

namespace SerreMarkov

def coordinateHeight (z : Six) : ℕ :=
  z.a.natAbs + z.b.natAbs + z.c.natAbs + z.d.natAbs + z.e.natAbs + z.f.natAbs

def descentTrap : Six := ⟨-5, -2, -2, -5, 2, 2⟩

theorem descentTrap_isSolution : isSolution descentTrap := by
  norm_num [isSolution, q1, q2, descentTrap]

theorem descentTrap_word :
    applyWord (family 1 0)
      [.m1, .s4, .i2, .s3, .m3, .m3, .m3, .i2, .s4, .s3,
        .i1, .s4, .s3, .i1, .s3, .m2, .m3] = descentTrap := by decide

theorem descentTrap_reachable : Reachable (family 1 0) descentTrap :=
  ⟨[.m1, .s4, .i2, .s3, .m3, .m3, .m3, .i2, .s4, .s3,
    .i1, .s4, .s3, .i1, .s3, .m2, .m3], descentTrap_word⟩

theorem descentTrap_height : coordinateHeight descentTrap = 18 := by decide

theorem descentTrap_strict_mutation_increase :
    coordinateHeight descentTrap < coordinateHeight (mu1 descentTrap) ∧
    coordinateHeight descentTrap < coordinateHeight (inv1 descentTrap) ∧
    coordinateHeight descentTrap < coordinateHeight (mu2 descentTrap) ∧
    coordinateHeight descentTrap < coordinateHeight (inv2 descentTrap) ∧
    coordinateHeight descentTrap < coordinateHeight (mu3 descentTrap) ∧
    coordinateHeight descentTrap < coordinateHeight (inv3 descentTrap) := by decide

theorem descentTrap_one_step_minimum (g : Generator) :
    coordinateHeight descentTrap ≤ coordinateHeight (step g descentTrap) := by
  cases g <;> decide

theorem descentTrap_no_decreasing_generator :
    ¬∃ g : Generator, coordinateHeight (step g descentTrap) < coordinateHeight descentTrap := by
  rintro ⟨g, h⟩
  exact Nat.not_lt_of_ge (descentTrap_one_step_minimum g) h

/-! An infinite corridor illustrates how a bounded word can leave a local
minimum. The three-step certificate itself is valid for every nonnegative
parameter, without a finite search. -/

def descentCorridor (n : ℕ) : Six :=
  ⟨-((n : ℤ) + 4), -2, -2, -((n : ℤ) + 2), 0, 2⟩

theorem descentCorridor_isSolution (n : ℕ) : isSolution (descentCorridor n) := by
  constructor <;> simp [q1, q2, descentCorridor] <;> ring

theorem descentCorridor_three_steps (n : ℕ) :
    applyWord (descentCorridor n) [.i3, .i3, .i2] =
      ⟨-2, -(n : ℤ), -2, (n : ℤ) + 2, 2, 0⟩ := by
  ext <;> simp [applyWord, step, inv2, inv3, descentCorridor] <;> ring

theorem descentCorridor_height (n : ℕ) :
    coordinateHeight (descentCorridor n) = 2 * n + 12 := by
  simp [coordinateHeight, descentCorridor]
  omega

theorem descentCorridor_three_steps_height (n : ℕ) :
    coordinateHeight (applyWord (descentCorridor n) [.i3, .i3, .i2]) =
      2 * n + 8 := by
  rw [descentCorridor_three_steps]
  have h2 : ((n : ℤ) + 2).natAbs = n + 2 := by
    exact_mod_cast (Int.natAbs_of_nonneg (by omega : 0 ≤ (n : ℤ) + 2))
  simp [coordinateHeight, h2]
  omega

theorem descentCorridor_three_steps_decrease (n : ℕ) :
    coordinateHeight (applyWord (descentCorridor n) [.i3, .i3, .i2]) <
      coordinateHeight (descentCorridor n) := by
  rw [descentCorridor_three_steps_height, descentCorridor_height]
  omega

end SerreMarkov
