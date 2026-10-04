import SerreMarkov.MinorContent
import SerreMarkov.DegenerateParameter

/-! # Separation of all normalized degenerate parameters

The second-minor divisor invariant distinguishes normalized parameters even
under arbitrary integral Euler-lattice isomorphisms. Mutation separation then
follows from the proved integral basis congruences.
-/

namespace SerreMarkov

theorem degenerate_family_lattice_injective {k l : ℤ}
    (hk : 0 ≤ k) (hl : 0 ≤ l)
    (h : LatticeEquivalent (family k (-k)) (family l (-l))) : k = l :=
  degenerate_parameter_eq_of_content k l hk hl (degenerate_family_minor_content h)

theorem degenerate_family_latticeEquivalent_iff {k l : ℤ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) :
    LatticeEquivalent (family k (-k)) (family l (-l)) ↔ k = l := by
  constructor
  · exact degenerate_family_lattice_injective hk hl
  · intro h
    subst l
    exact latticeEquivalent_refl _

theorem degenerate_family_reachable_iff {k l : ℤ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) :
    Reachable (family k (-k)) (family l (-l)) ↔ k = l := by
  constructor
  · intro h
    exact degenerate_family_lattice_injective hk hl (reachable_latticeEquivalent h)
  · intro h
    subst l
    exact reachable_refl _

end SerreMarkov
