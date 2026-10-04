import SerreMarkov.DegenerateClassification
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Singleton fibers over degenerate integral Euler lattices

These are fibers of the actual forgetful map on all integer solutions.
Isometry preserves the Serre cube, so every representative in such a fiber
is degenerate. The unconditional degenerate classification then identifies
its mutation orbit with the reference orbit.
-/

namespace SerreMarkov.DegenerateFibers

abbrev SolutionFiber (z : Six) :=
  {o : Quotient solutionSetoid //
    solutionForgetfulMap o = Quotient.mk latticeSetoid z}

def referenceFiber (z : Six) (hz : isSolution z) : SolutionFiber z :=
  ⟨Quotient.mk solutionSetoid ⟨z, hz⟩, rfl⟩

theorem degenerate_fiber_orbit_unique (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z ^ 3 = 0) (o : SolutionFiber z) :
    o.val = Quotient.mk solutionSetoid ⟨z, hz⟩ := by
  have h : ∀ q : Quotient solutionSetoid,
      solutionForgetfulMap q = Quotient.mk latticeSetoid z →
      q = Quotient.mk solutionSetoid ⟨z, hz⟩ := by
    intro q
    refine Quotient.inductionOn q ?_
    intro w heq
    have hl : LatticeEquivalent w.val z := Quotient.exact heq
    have hwc : shiftedSerre w.val ^ 3 = 0 :=
      (latticeEquivalent_shifted_power_zero hl 3).mpr hc
    apply Quotient.sound
    exact (degenerate_latticeEquivalent_iff_reachable w.property hz hwc hc).mp hl
  exact h o.val o.property

theorem degenerate_fiber_subsingleton (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z ^ 3 = 0) : Subsingleton (SolutionFiber z) := by
  constructor
  intro o p
  apply Subtype.ext
  exact (degenerate_fiber_orbit_unique z hz hc o).trans
    (degenerate_fiber_orbit_unique z hz hc p).symm

def degenerateFiberEquivUnit (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z ^ 3 = 0) : SolutionFiber z ≃ Unit where
  toFun := fun _ => Unit.unit
  invFun := fun _ => referenceFiber z hz
  left_inv := by
    intro o
    letI := degenerate_fiber_subsingleton z hz hc
    exact Subsingleton.elim _ _
  right_inv := by intro u; cases u; rfl

theorem degenerate_fiber_finite (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z ^ 3 = 0) : Finite (SolutionFiber z) :=
  Finite.of_equiv Unit (degenerateFiberEquivUnit z hz hc).symm

theorem degenerate_fiber_card (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z ^ 3 = 0) : Nat.card (SolutionFiber z) = 1 := by
  rw [Nat.card_congr (degenerateFiberEquivUnit z hz hc)]
  simp

end SerreMarkov.DegenerateFibers
