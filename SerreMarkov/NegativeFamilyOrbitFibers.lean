import SerreMarkov.FamilyOrbitFiberCompletion
import SerreMarkov.NegativeClassificationFull

/-! # Unconditional exact negative solution-orbit fibers

The completed negative classification proves that every orbit in these actual
forgetful-map fibers has a normalized family representative. The finite models
and cardinalities below therefore count the entire fiber of integer solution
mutation orbits. No local-descent or classification hypothesis remains.
-/

namespace SerreMarkov.NegativeFamilyOrbitFibers

open FamilyFiberFinite FamilyOrbitFibers
noncomputable section

private theorem classification : FamilyOrbitFiberCompletion.NegativeClassificationProperty :=
  NegativeClassificationFull.negative_classification

/-- Every orbit in the full solution fiber lies in its normalized family part. -/
theorem fullFiber_mem_familyPart (m : ℕ) (hm : 0<m) (y : ℤ) (o : FullFiber m y) :
    o ∈ FamilyPart m y :=
  FamilyOrbitFiberCompletion.fullFiber_mem_familyPart_of_classification classification m hm y o

theorem fullFiber_familyPart_eq_univ (m : ℕ) (hm : 0<m) (y : ℤ) :
    FamilyPart m y=Set.univ :=
  Set.eq_univ_iff_forall.mpr (fullFiber_mem_familyPart m hm y)

theorem candidateFiberMap_surjective (m : ℕ) (hm : 0<m) (y : ℤ) :
    Function.Surjective (candidateFiberMap m y) :=
  FamilyOrbitFiberCompletion.candidateFiberMap_surjective_of_classification classification m hm y

def fullFiberEquivFamilyPart (m : ℕ) (hm : 0<m) (y : ℤ) :
    FullFiber m y ≃ FamilyPart m y :=
  FamilyOrbitFiberCompletion.fullFiberEquivFamilyPart_of_classification classification m hm y

/-- An exact finite parameterization of the actual full solution-orbit fiber. -/
def fullFiberEquivCandidate (m : ℕ) (hm : 0<m) (y : ℤ) :
    FullFiber m y ≃ Candidate m y :=
  FamilyOrbitFiberCompletion.fullFiberEquivCandidate_of_classification classification m hm y

theorem fullFiber_finite (m : ℕ) (hm : 0<m) (y : ℤ) : Finite (FullFiber m y) :=
  FamilyOrbitFiberCompletion.fullFiber_finite_of_classification classification m hm y

instance fullFiberFinite (m : ℕ) (y : ℤ) [NeZero m] : Finite (FullFiber m y) :=
  fullFiber_finite m (Nat.pos_of_ne_zero (NeZero.ne m)) y

theorem fullFiber_card (m : ℕ) (hm : 0<m) (y : ℤ) :
    Nat.card (FullFiber m y)=Fintype.card (Candidate m y) :=
  FamilyOrbitFiberCompletion.fullFiber_card_of_classification classification m hm y

/-- The full fiber is finite for every positive total, including even totals. -/
theorem fullFiber_card_le (m : ℕ) (hm : 0<m) (y : ℤ) :
    Nat.card (FullFiber m y)≤m/2+1 :=
  FamilyOrbitFiberCompletion.fullFiber_card_le_of_classification classification m hm y

/-- For odd totals, modular square roots modulo sign classify the full fiber. -/
def oddRootSignQuotientEquivFullFiber
    (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    Quotient (rootSignSetoid m ((y : ZMod m)^2)) ≃ FullFiber m y :=
  FamilyOrbitFiberCompletion.oddRootSignQuotientEquivFullFiber_of_classification
    classification m hm hodd y

theorem odd_fullFiber_twice_card (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    2*Nat.card (FullFiber m y)=Nat.card (Roots m ((y : ZMod m)^2))+
      if (y : ZMod m)^2=0 then 1 else 0 :=
  FamilyOrbitFiberCompletion.odd_fullFiber_twice_card_of_classification classification m hm hodd y

/-- The root-product formula counts the complete fiber, with no descent premise. -/
theorem odd_fullFiber_card (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    Nat.card (FullFiber m y)=oddFamilyCount m y :=
  FamilyOrbitFiberCompletion.odd_fullFiber_card_of_classification classification m hm hodd y

theorem odd_fullFiber_explicit_card (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    Nat.card (FullFiber m y)=
      ((∏ p ∈ m.factorization.support,
        if y=0 ∨ m.factorization p≤2*y.natAbs.factorization p
        then p^(m.factorization p/2) else 2*p^(y.natAbs.factorization p))+
        if (y : ZMod m)^2=0 then 1 else 0)/2 :=
  FamilyOrbitFiberCompletion.odd_fullFiber_explicit_card_of_classification
    classification m hm hodd y

def oddFullFiberEquivFin (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    FullFiber m y ≃ Fin (oddFamilyCount m y) :=
  FamilyOrbitFiberCompletion.oddFullFiberEquivFin_of_classification classification m hm hodd y

/-- This equivalence concerns all solution mutation orbits in the full fiber. -/
def primePowerZeroFullFiberEquivFin (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    FullFiber (p^(2*e)) 0 ≃ Fin ((p^e+1)/2) :=
  FamilyOrbitFiberCompletion.primePowerZeroFullFiberEquivFin_of_classification
    classification p e hp hodd

theorem primePower_zero_fullFiber_card (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card (FullFiber (p^(2*e)) 0)=(p^e+1)/2 :=
  FamilyOrbitFiberCompletion.primePower_zero_fullFiber_card_of_classification classification p e hp hodd

/-- The cardinality statement written directly as the actual forgetful-map fiber. -/
theorem odd_solution_forgetful_fiber_card
    (m : ℕ) (hm : 0<m) (hodd : Odd m) (y : ℤ) :
    Nat.card {o : Quotient solutionSetoid //
      solutionForgetfulMap o=Quotient.mk latticeSetoid (family ((m : ℤ)-y) y)}=
        oddFamilyCount m y :=
  odd_fullFiber_card m hm hodd y

theorem primePower_zero_solution_forgetful_fiber_card
    (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card {o : Quotient solutionSetoid //
      solutionForgetfulMap o=Quotient.mk latticeSetoid (family (p^(2*e)) 0)}=(p^e+1)/2 := by
  simpa [FullFiber,familyLatticeClass] using primePower_zero_fullFiber_card p e hp hodd

end
end SerreMarkov.NegativeFamilyOrbitFibers
