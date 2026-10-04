import SerreMarkov.FullClassification

/-! Run with `lake env lean scripts/decision_examples.lean`.
These examples use the final unconditional decision procedures.
-/
open SerreMarkov SerreMarkov.FullClassification

def demoFamily (x y : ℤ) : Solution :=
  ⟨family x y, family_isSolution x y⟩

def demoMoved : Solution :=
  ⟨step .m1 (family 9 4), step_preserves_solution .m1 _ (family_isSolution 9 4)⟩

#eval classify demoMoved
#eval classify (demoFamily 17 (-17))
#eval classify ⟨PositiveExamples.representative 0, PositiveExamples.representative_isSolution 0⟩

-- Same Euler lattice, distinct actual mutation orbits.
#eval mutationEquivalentTest (demoFamily 9 0) (demoFamily 6 3)
#eval latticeEquivalentTest (demoFamily 9 0) (demoFamily 6 3)

-- An actual word taking the mutated input back to its family representative.
#eval equivalenceWord demoMoved (demoFamily 9 4)
