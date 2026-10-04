import SerreMarkov.PositiveRepresentatives

/-! # Twenty-three bounded positive solutions with actual mutation witnesses

The table is untrusted generated data. Lean checks every listed word in its
kernel. This module does not assert an unbounded terminal-height theorem.
-/

namespace SerreMarkov.PositiveBoundedTable

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def tuple (i : Fin 23) : Six :=
  ![⟨3,5,5,5,10,7⟩,
    ⟨3,7,4,7,8,8⟩,
    ⟨3,7,6,6,7,3⟩,
    ⟨3,8,7,4,7,8⟩,
    ⟨3,10,5,5,5,7⟩,
    ⟨4,4,4,5,11,5⟩,
    ⟨4,6,4,4,6,4⟩,
    ⟨4,7,3,8,8,7⟩,
    ⟨4,8,8,3,7,7⟩,
    ⟨4,11,5,4,4,5⟩,
    ⟨5,4,5,4,11,4⟩,
    ⟨5,5,3,7,10,5⟩,
    ⟨5,5,7,3,10,5⟩,
    ⟨5,10,3,7,5,5⟩,
    ⟨5,10,7,3,5,5⟩,
    ⟨5,11,4,5,4,4⟩,
    ⟨6,7,3,3,7,6⟩,
    ⟨7,5,5,5,10,3⟩,
    ⟨7,7,8,3,8,4⟩,
    ⟨7,8,3,8,7,4⟩,
    ⟨7,10,5,5,5,3⟩,
    ⟨8,7,7,4,8,3⟩,
    ⟨8,8,4,7,7,3⟩] i

def representativeIndex (i : Fin 23) : Fin 5 :=
  ![2,3,4,3,2,1,0,3,3,1,1,2,2,2,2,1,4,2,3,3,2,3,3] i

def witnessWord (i : Fin 23) : List Generator :=
  ![[.m1,.m2,.m1,.i3],
    [.m1,.m2,.m1,.m2,.i2,.i3],
    [.i3,.i2,.i1,.s1],
    [.m2,.m1,.m2,.m1,.m2,.m3,.m2,.m1,.m2,.i2,.i3],
    [.m2,.m1,.i3],
    [.m1,.m2,.i3,.m1],
    [.i3,.m1],
    [.m1,.m2,.m1,.m2,.m3,.m2,.i2,.i3],
    [.m2,.m1,.m2,.m3,.m2,.m1,.m2,.i2,.i3],
    [.m2,.i3,.m1],
    [.i3,.m1],
    [.m1,.i3,.i2,.i3],
    [.i2,.i3],
    [.i3,.m1,.i3],
    [.i3],
    [.i3,.i3,.m1],
    [.s1],
    [.i2,.i3,.i2,.i3],
    [.i2,.i3],
    [.i3,.m1,.m2,.i2,.i3],
    [.i3,.i2,.i3,.i2,.i3],
    [.i2,.i3,.i2,.i3],
    [.i3,.m1,.m2,.m3,.m2,.i2,.i3]] i

/-- Every table row reaches its stated original manuscript representative
by the actual integer mutation and sign operations. -/
theorem witness_verified (i : Fin 23) :
    applyWord (tuple i) (witnessWord i) =
      PositiveExamples.representative (representativeIndex i) := by
  fin_cases i <;> decide +kernel

theorem tuple_reachable (i : Fin 23) :
    Reachable (tuple i) (PositiveExamples.representative (representativeIndex i)) :=
  ⟨witnessWord i, witness_verified i⟩

def table : List Six := List.ofFn tuple

end SerreMarkov.PositiveBoundedTable
