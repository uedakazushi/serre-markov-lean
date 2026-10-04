import SerreMarkov.FamilyFiberFinite
import SerreMarkov.PrimePowerRoots
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact normalized family-candidate counts over odd prime square powers

For `m=p^(2e)`, the lattice of `family m 0` has exactly `(p^e+1)/2`
normalized family parameters isometric to it. This counts parameters within
the stated family; it does not identify the number of mutation orbits among
all integer solutions.
-/

namespace SerreMarkov.FamilyFiberFinite

theorem primePower_zero_square_candidate_twice_card (p e : ℕ) (hp : p.Prime)
    (hodd : Odd p) (y : ℤ) (hy : (y : ZMod (p^(2*e)))^2 = 0) :
    2 * Fintype.card (Candidate (p^(2*e)) y) = p^e + 1 := by
  have hcount := odd_lattice_candidate_count (p^(2*e)) hodd.pow y
  simpa only [hy, Roots, if_true, primePower_squareZeroRoots_natCard p e hp] using hcount

/-- This includes every source parameter whose square is zero modulo `m`. -/
theorem primePower_zero_square_candidate_card (p e : ℕ) (hp : p.Prime)
    (hodd : Odd p) (y : ℤ) (hy : (y : ZMod (p^(2*e)))^2 = 0) :
    Fintype.card (Candidate (p^(2*e)) y) = (p^e + 1) / 2 := by
  have h := primePower_zero_square_candidate_twice_card p e hp hodd y hy
  omega

/-- Exact count of normalized family parameters isometric to `family m 0`.
The boundary case `e=0`, hence `m=1`, is included. -/
theorem primePower_zero_lattice_candidate_card (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Fintype.card (Candidate (p^(2*e)) 0) = (p^e + 1) / 2 := by
  apply primePower_zero_square_candidate_card p e hp hodd 0
  simp

noncomputable def primePowerZeroCandidateEquivFin (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Candidate (p^(2*e)) 0 ≃ Fin ((p^e + 1) / 2) :=
  Fintype.equivFinOfCardEq (primePower_zero_lattice_candidate_card p e hp hodd)

end SerreMarkov.FamilyFiberFinite
