import SerreMarkov.NegativeFamilyOrbitFibers

/-! # Finiteness over every negative solution lattice

The source lattice may be an arbitrary negative solution, rather than an
already selected family lattice. Its proved normalized representative gives
an equality of actual lattice classes, and transports the complete finite
fiber theorem along that equality.
-/

namespace SerreMarkov.NegativeFiberFiniteGeneral
open FamilyOrbitFibers NegativeFamilyOrbitFibers

theorem negative_solution_fiber_finite (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    Finite {o : Quotient solutionSetoid //
      solutionForgetfulMap o=Quotient.mk latticeSetoid z} := by
  obtain ⟨p,hp,hr⟩ := NegativeClassificationFull.negative_normalized_existence z hz hneg
  have hsum : 0<p.1+p.2 := hp.2.2
  let m := (p.1+p.2).toNat
  have hm : 0<m := by dsimp [m]; omega
  have hcast : (m : ℤ)=p.1+p.2 := by dsimp [m]; omega
  have hclass : Quotient.mk latticeSetoid z=familyLatticeClass m p.2 := by
    change Quotient.mk latticeSetoid z=Quotient.mk latticeSetoid (family ((m : ℤ)-p.2) p.2)
    have hf : family ((m : ℤ)-p.2) p.2=family p.1 p.2 := by rw [hcast]; congr 1 <;> omega
    rw [hf]
    exact Quotient.sound (reachable_latticeEquivalent hr)
  rw [hclass]
  exact fullFiber_finite m hm p.2

end SerreMarkov.NegativeFiberFiniteGeneral
