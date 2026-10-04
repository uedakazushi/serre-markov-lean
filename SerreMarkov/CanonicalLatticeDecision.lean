import SerreMarkov.ClassificationDecision
import SerreMarkov.ArithmeticDecision
import SerreMarkov.NegativeLatticeCriterion

/-!
# Executable lattice isometry tests for canonical and arbitrary solutions

Canonical positive and degenerate lattices are compared by their parameters.
Canonical negative lattices are compared by their positive total and a finite
congruence search, including even totals. The test for arbitrary solutions uses
the executable canonical search, with positive completeness explicit.
-/

namespace SerreMarkov.CanonicalLatticeDecision

open CanonicalRepresentatives NegativeClassification ClassificationDecision
open FullClassificationPipeline NegativeLatticeCriterion
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- An integer positive total supplies a nonzero finite modulus. -/
def positiveTotalTest (m : ℤ) (hm : 0<m) (y y' : ℤ) : Bool := by
  letI : NeZero m.toNat := ⟨by omega⟩
  exact familyIsometryTest m.toNat y y'

theorem positiveTotalTest_correct (m : ℤ) (hm : 0<m) (y y' : ℤ) :
    positiveTotalTest m hm y y'=true ↔
      ∃ t : ℤ,m ∣ y-y'-2*t ∧ m ∣ t*(t-y) := by
  letI : NeZero m.toNat := ⟨by omega⟩
  have hmcast : (m.toNat : ℤ)=m := Int.toNat_of_nonneg hm.le
  simpa only [positiveTotalTest,familyIsometryTest,decide_eq_true_eq,
    CongruenceWitness,hmcast] using
    (integer_congruences_iff_mod_witness m.toNat y y').symm

def negativeTest (p q : {p : ℤ×ℤ // NormalizedNegativePair p}) : Bool :=
  if p.val.1+p.val.2=q.val.1+q.val.2 then
    positiveTotalTest (p.val.1+p.val.2) p.property.2.2 p.val.2 q.val.2
  else false

theorem negativeTest_correct (p q : {p : ℤ×ℤ // NormalizedNegativePair p}) :
    negativeTest p q=true ↔ LatticeEquivalent (family p.val.1 p.val.2)
      (family q.val.1 q.val.2) := by
  rw [normalized_lattice_criterion _ _ p.val q.val p.property q.property
    (reachable_refl _) (reachable_refl _)]
  by_cases ht : p.val.1+p.val.2=q.val.1+q.val.2
  · simp only [negativeTest,ht,ite_true,true_and,positiveTotalTest_correct]
  · simp [negativeTest,ht]

/-- Comparison of all three kinds of actual canonical Euler lattices. -/
def canonicalLatticeTest : Canonical → Canonical → Bool
  | .degenerate k,.degenerate l => decide (k=l)
  | .negative p,.negative q => negativeTest p q
  | .positive r,.positive s => decide (r=s)
  | _,_ => false

theorem canonicalLatticeTest_correct (c d : Canonical) :
    canonicalLatticeTest c d=true ↔ LatticeEquivalent (representative c) (representative d) := by
  cases c <;> cases d
  · rename_i k l
    have h := (degenerate_family_latticeEquivalent_iff
      (Nat.cast_nonneg k) (Nat.cast_nonneg l)).symm
    simpa [canonicalLatticeTest,representative] using h
  all_goals try {
    simp only [canonicalLatticeTest,Bool.false_eq_true,false_iff]
    intro h
    have hk := latticeEquivalent_intrinsicKind (representative_isSolution _) h
    rw [representative_kind,representative_kind] at hk
    simp [kind] at hk }
  · exact negativeTest_correct _ _
  · rename_i r s
    simpa [canonicalLatticeTest,representative] using
      (PositiveExamples.representatives_latticeEquivalent_iff r s).symm

/-- Finite congruence comparison after the terminating canonical search. -/
def latticeEquivalentTest (hpos : PositiveCompleteness) (z w : Solution) : Bool :=
  canonicalLatticeTest (classify hpos z).2 (classify hpos w).2

theorem latticeEquivalentTest_correct (hpos : PositiveCompleteness) (z w : Solution) :
    latticeEquivalentTest hpos z w=true ↔ LatticeEquivalent z.val w.val := by
  rw [latticeEquivalentTest,canonicalLatticeTest_correct]
  have hz := reachable_latticeEquivalent (classify_reachable hpos z)
  have hw := reachable_latticeEquivalent (classify_reachable hpos w)
  constructor
  · intro h
    exact latticeEquivalent_trans hz (latticeEquivalent_trans h (latticeEquivalent_symm hw))
  · intro h
    exact latticeEquivalent_trans (latticeEquivalent_symm hz) (latticeEquivalent_trans h hw)

def latticeEquivalenceDecidable (hpos : PositiveCompleteness) (z w : Solution) :
    Decidable (LatticeEquivalent z.val w.val) :=
  decidable_of_iff (latticeEquivalentTest hpos z w=true)
    (latticeEquivalentTest_correct hpos z w)

/-- Composite totals can identify distinct canonical mutation parameters. -/
theorem composite_canonical_test :
    canonicalLatticeTest (.negative ⟨(14,1),by decide⟩)
      (.negative ⟨(11,4),by decide⟩)=true := by decide +kernel

/-- The even-total test uses simultaneous congruences, which distinguish
parameters with the same square modulo four. -/
theorem even_canonical_test :
    canonicalLatticeTest (.negative ⟨(4,0),by decide⟩)
      (.negative ⟨(2,2),by decide⟩)=false := by decide +kernel

theorem cross_kind_canonical_test :
    canonicalLatticeTest (.degenerate 17) (.positive 0)=false := rfl

end SerreMarkov.CanonicalLatticeDecision
