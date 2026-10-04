import SerreMarkov.FamilyOrbitFibers
import SerreMarkov.FamilyIntrinsic
import SerreMarkov.NegativeClassification

/-!
# Full negative fibers, conditional on local descent

Every result asserting completeness or an exact full-fiber cardinality in
this module has the unproved `NegativeDescent.LocalDescentProperty` as an
explicit hypothesis. The unconditional embeddings and restricted-fiber
counts remain in `FamilyOrbitFibers`.
-/

namespace SerreMarkov.ConditionalFamilyOrbitFibers

open FamilyFiberFinite FamilyOrbitFibers
noncomputable section

theorem solution_in_family_lattice_negative (m : ℕ) (hm : 0 < m) (y : ℤ)
    (z : Solution)
    (h : solutionForgetfulMap (Quotient.mk solutionSetoid z) = familyLatticeClass m y) :
    IntrinsicSigns.thirdMinorSum z.val < 0 := by
  have hi : LatticeEquivalent (family ((m : ℤ)-y) y) z.val :=
    latticeEquivalent_symm (Quotient.exact h)
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  exact ((latticeEquivalent_regular_signs (family_isSolution _ _)
    (FamilyIntrinsic.family_regular (m : ℤ) y hmz) hi).2).mp
    (FamilyIntrinsic.family_negative (m : ℤ) y hmz)

/-- The local descent hypothesis makes every orbit in the actual full
fiber admit a normalized family representative. -/
theorem fullFiber_mem_familyPart_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (y : ℤ) (o : FullFiber m y) :
    o ∈ Set.range (candidateFiberMap m y) := by
  obtain ⟨z, hz⟩ := Quotient.exists_rep o.val
  have hclass : solutionForgetfulMap (Quotient.mk solutionSetoid z) = familyLatticeClass m y := by
    rw [hz]
    exact o.property
  have hneg := solution_in_family_lattice_negative m hm y z hclass
  obtain ⟨p, hp, hr⟩ := NegativeClassification.negative_normalized_existence_of_local_descent
    hlocal z.val z.property hneg
  let m' : ℤ := p.1 + p.2
  have hm' : 0 < m' := hp.2.2
  have hr' : Reachable z.val (family (m'-p.2) p.2) := by simpa [m'] using hr
  have hi : LatticeEquivalent (family ((m : ℤ)-y) y) (family (m'-p.2) p.2) :=
    latticeEquivalent_trans (latticeEquivalent_symm (Quotient.exact hclass))
      (reachable_latticeEquivalent hr')
  obtain ⟨B, hB⟩ := hi
  have hdet : (B : Mat4).det = 1 ∨ (B : Mat4).det = -1 :=
    Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det (B : Mat4)).mp B.isUnit)
  have heq : (m : ℤ) = m' := family_positive_totals_eq_of_isometry
    (m : ℤ) m' y p.2 (by exact_mod_cast hm) hm' (B : Mat4) hdet hB
  have hpx : p.2 ≤ p.1 := hp.2.1
  have hb : 2*p.2 ≤ m := by dsimp [m'] at heq; omega
  let j : NormalizedParameter m := boundedParameterEquiv m ⟨p.2, hp.1, hb⟩
  have hj : (j.val : ℤ) = p.2 := Int.toNat_of_nonneg hp.1
  apply (mem_familyPart_iff m y o).mpr
  refine ⟨j, ?_⟩
  calc
    o.val = Quotient.mk solutionSetoid z := hz.symm
    _ = normalizedOrbit m j := by
      apply Quotient.sound
      change Reachable z.val (family ((m : ℤ)-j.val) j.val)
      rw [hj, heq]
      exact hr'

/-- Conditional identification with the restricted family part. -/
def fullFiberEquivFamilyPart_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (y : ℤ) : FullFiber m y ≃ FamilyPart m y where
  toFun o := ⟨o, fullFiber_mem_familyPart_of_local_descent hlocal m hm y o⟩
  invFun o := o.val
  left_inv _ := rfl
  right_inv _ := rfl

def fullFiberEquivCandidate_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (y : ℤ) : FullFiber m y ≃ Candidate m y :=
  (fullFiberEquivFamilyPart_of_local_descent hlocal m hm y).trans
    (familyPartEquivCandidate m hm y)

theorem fullFiber_finite_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (y : ℤ) : Finite (FullFiber m y) :=
  Finite.of_equiv (Candidate m y) (fullFiberEquivCandidate_of_local_descent hlocal m hm y).symm

theorem fullFiber_card_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (y : ℤ) :
    Nat.card (FullFiber m y) = Fintype.card (Candidate m y) := by
  rw [Nat.card_congr (fullFiberEquivCandidate_of_local_descent hlocal m hm y),
    Nat.card_eq_fintype_card]

def oddRootSignQuotientEquivFullFiber_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Quotient (rootSignSetoid m ((y : ZMod m)^2)) ≃ FullFiber m y :=
  (oddRootSignQuotientEquivCandidate m hodd y).trans
    (fullFiberEquivCandidate_of_local_descent hlocal m hm y).symm

theorem odd_fullFiber_twice_card_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    2 * Nat.card (FullFiber m y) = Nat.card (Roots m ((y : ZMod m)^2)) +
      if (y : ZMod m)^2 = 0 then 1 else 0 := by
  rw [fullFiber_card_of_local_descent hlocal m hm y]
  exact odd_lattice_candidate_count m hodd y

/-- The exact full-fiber product count is conditional on local descent. -/
theorem odd_fullFiber_card_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (FullFiber m y) = oddFamilyCount m y := by
  rw [fullFiber_card_of_local_descent hlocal m hm y, odd_candidate_card m hm hodd y]

theorem odd_fullFiber_explicit_card_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (FullFiber m y) =
      ((∏ p ∈ m.factorization.support,
        if y = 0 ∨ m.factorization p ≤ 2*y.natAbs.factorization p
        then p^(m.factorization p / 2) else 2*p^(y.natAbs.factorization p)) +
        if (y : ZMod m)^2 = 0 then 1 else 0) / 2 :=
  odd_fullFiber_card_of_local_descent hlocal m hm hodd y

def primePowerZeroFullFiberEquivFin_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    FullFiber (p^(2*e)) 0 ≃ Fin ((p^e+1)/2) :=
  (fullFiberEquivCandidate_of_local_descent hlocal (p^(2*e)) (pow_pos hp.pos _) 0).trans
    (primePowerZeroCandidateEquivFin p e hp hodd)

theorem primePower_zero_fullFiber_card_of_local_descent
    (hlocal : NegativeDescent.LocalDescentProperty)
    (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card (FullFiber (p^(2*e)) 0) = (p^e+1)/2 := by
  rw [Nat.card_congr (primePowerZeroFullFiberEquivFin_of_local_descent hlocal p e hp hodd),
    Nat.card_fin]

end
end SerreMarkov.ConditionalFamilyOrbitFibers
