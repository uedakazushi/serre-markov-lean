import SerreMarkov.PositiveClassificationFull
import SerreMarkov.FullClassificationPipeline
import SerreMarkov.ClassificationDecision
import SerreMarkov.CanonicalLatticeDecision
import SerreMarkov.DegenerateJordan

/-! # The manuscript's full classification and finite forgetful fibers

The positive completeness argument of the assembly and executable search
modules is supplied here by the unconditional positive classification.
-/

namespace SerreMarkov.FullClassification
open CanonicalRepresentatives FullClassificationPipeline

theorem positive_completeness : PositiveCompleteness := by
  intro z hz hp
  exact (PositiveClassificationFull.positive_classification z hz hp).exists

/-- The disjoint negative, degenerate, and five sporadic representatives form
a complete and nonredundant list for every integer solution. -/
theorem full_classification (z : Six) (hz : isSolution z) :
    ∃! c : Canonical, Reachable z (representative c) :=
  canonical_classification_of_positive positive_completeness z hz

theorem canonical_orbit_map_bijective : Function.Bijective orbitMap :=
  ⟨orbitMap_injective,orbitMap_surjective_of_positive positive_completeness⟩

noncomputable def canonicalOrbitEquiv : Canonical ≃ Quotient solutionSetoid :=
  canonicalOrbitEquivOfPositive positive_completeness

theorem positive_latticeEquivalent_iff_reachable (z w : Six)
    (hz : isSolution z) (hw : isSolution w)
    (hpz : 0<IntrinsicSigns.thirdMinorSum z) (hpw : 0<IntrinsicSigns.thirdMinorSum w) :
    LatticeEquivalent z w ↔ Reachable z w :=
  positive_latticeEquivalent_iff_reachable_of_positive positive_completeness z w hz hw hpz hpw

theorem positive_fiber_subsingleton (z : Six) (hz : isSolution z)
    (hpz : 0<IntrinsicSigns.thirdMinorSum z) :
    Subsingleton (DegenerateFibers.SolutionFiber z) :=
  positive_fiber_subsingleton_of_positive positive_completeness z hz hpz

theorem positive_fiber_card (z : Six) (hz : isSolution z)
    (hpz : 0<IntrinsicSigns.thirdMinorSum z) :
    Nat.card (DegenerateFibers.SolutionFiber z)=1 :=
  positive_fiber_card_of_positive positive_completeness z hz hpz

theorem solution_fiber_finite (z : Six) (hz : isSolution z) :
    Finite (DegenerateFibers.SolutionFiber z) :=
  solution_fiber_finite_of_positive positive_completeness z hz

/-- Every fiber of the actual forgetful map on all solution orbits is finite,
including the empty fibers over lattice classes not represented by solutions. -/
theorem all_forgetful_fibers_finite (L : Quotient latticeSetoid) :
    Finite {o : Quotient solutionSetoid // solutionForgetfulMap o=L} :=
  all_forgetful_fibers_finite_of_positive positive_completeness L

theorem prime_square_power_fiber_card (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card {o : Quotient solutionSetoid //
      solutionForgetfulMap o=Quotient.mk latticeSetoid (family (p^(2*e)) 0)}=
        (p^e+1)/2 :=
  NegativeFamilyOrbitFibers.primePower_zero_solution_forgetful_fiber_card p e hp hodd

/-- Each individual fiber is finite, while their sizes have no common bound. -/
theorem finite_fibers_and_unbounded :
    (∀ L : Quotient latticeSetoid,
      Finite {o : Quotient solutionSetoid // solutionForgetfulMap o=L}) ∧
    (∀ n : ℕ, ∃ L : Quotient latticeSetoid,
      ∃ f : Fin (n+1) → {o : Quotient solutionSetoid // solutionForgetfulMap o=L},
        Function.Injective f) :=
  ⟨all_forgetful_fibers_finite,unbounded_solutionForgetfulMap_fibers⟩

/-- A terminating finite-word search returns the canonical representative
and an actual word reaching it. This definition is computable. -/
def classify (z : Solution) : List Generator×Canonical :=
  ClassificationDecision.classify positive_completeness z

theorem classify_word (z : Solution) :
    applyWord z.val (classify z).1=representative (classify z).2 :=
  ClassificationDecision.classify_word positive_completeness z

def mutationEquivalentTest (z w : Solution) : Bool :=
  ClassificationDecision.mutationEquivalentTest positive_completeness z w

theorem mutationEquivalentTest_correct (z w : Solution) :
    mutationEquivalentTest z w=true ↔ Reachable z.val w.val :=
  ClassificationDecision.mutationEquivalentTest_correct positive_completeness z w

def mutationEquivalenceDecidable (z w : Solution) : Decidable (Reachable z.val w.val) :=
  ClassificationDecision.mutationEquivalenceDecidable positive_completeness z w

def equivalenceWord (z w : Solution) : Option (List Generator) :=
  ClassificationDecision.equivalenceWord positive_completeness z w

theorem equivalenceWord_sound (z w : Solution) (word : List Generator)
    (h : equivalenceWord z w=some word) : applyWord z.val word=w.val :=
  ClassificationDecision.equivalenceWord_sound positive_completeness z w word h

theorem equivalenceWord_isSome_iff (z w : Solution) :
    (equivalenceWord z w).isSome=true ↔ Reachable z.val w.val :=
  ClassificationDecision.equivalenceWord_isSome_iff positive_completeness z w

/-- A terminating test for arbitrary solution Euler lattices. Even negative
totals retain the simultaneous congruences required by the isometry criterion. -/
def latticeEquivalentTest (z w : Solution) : Bool :=
  CanonicalLatticeDecision.latticeEquivalentTest positive_completeness z w

theorem latticeEquivalentTest_correct (z w : Solution) :
    latticeEquivalentTest z w=true ↔ LatticeEquivalent z.val w.val :=
  CanonicalLatticeDecision.latticeEquivalentTest_correct positive_completeness z w

def latticeEquivalenceDecidable (z w : Solution) : Decidable (LatticeEquivalent z.val w.val) :=
  CanonicalLatticeDecision.latticeEquivalenceDecidable positive_completeness z w

end SerreMarkov.FullClassification
