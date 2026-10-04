import SerreMarkov.Dihedral
import Mathlib.Data.Int.ModEq

/-!
# Finite dihedral labels

The integer Euclidean reduction descends modulo any integer modulus. This
completes the finite as well as the infinite case of the manuscript's dihedral
Hurwitz lemma. The same finite move word acts on the original residue labels.
-/

namespace SerreMarkov.Dihedral

def ModEq (m : ℤ) (q q' : Quad) : Prop :=
  Int.ModEq m q.n1 q'.n1 ∧ Int.ModEq m q.n2 q'.n2 ∧
    Int.ModEq m q.n3 q'.n3 ∧ Int.ModEq m q.n4 q'.n4

theorem step_modEq (m : ℤ) (g : Move) {q q' : Quad} (h : ModEq m q q') :
    ModEq m (step g q) (step g q') := by
  rcases h with ⟨h1, h2, h3, h4⟩
  cases g with
  | m1 => exact ⟨(h1.mul_left 2).sub h2, h1, h3, h4⟩
  | m2 => exact ⟨h1, (h2.mul_left 2).sub h3, h2, h4⟩
  | m3 => exact ⟨h1, h2, (h3.mul_left 2).sub h4, h3⟩
  | i1 => exact ⟨h2, (h2.mul_left 2).sub h1, h3, h4⟩
  | i2 => exact ⟨h1, h3, (h3.mul_left 2).sub h2, h4⟩
  | i3 => exact ⟨h1, h2, h4, (h4.mul_left 2).sub h3⟩

theorem applyWord_modEq (m : ℤ) (word : List Move) {q q' : Quad}
    (h : ModEq m q q') : ModEq m (applyWord q word) (applyWord q' word) := by
  induction word generalizing q q' with
  | nil => exact h
  | cons g gs ih => exact ih (step_modEq m g h)

/-- Finite dihedral reflections whose product is identity admit the same reduction. -/
theorem identity_product_hurwitz_mod (m : ℤ) (q : Quad)
    (hq : m ∣ q.n1-q.n2+q.n3-q.n4) :
    ∃ a g : ℤ, 0 ≤ g ∧ ∃ word : List Move,
      ModEq m (applyWord q word) ⟨a, a+g, a+g, a⟩ := by
  let q0 : Quad := ⟨q.n1, q.n2, q.n3, q.n1-q.n2+q.n3⟩
  have hlift : ModEq m q q0 := ⟨rfl, rfl, rfl, Int.modEq_of_dvd hq⟩
  have hq0 : q0.n1-q0.n2+q0.n3-q0.n4=0 := by
    dsimp [q0]
    omega
  obtain ⟨a, g, hg, word, hw⟩ := identity_product_hurwitz q0 hq0
  refine ⟨a, g, hg, word, ?_⟩
  have h := applyWord_modEq m word hlift
  rwa [hw] at h

end SerreMarkov.Dihedral
