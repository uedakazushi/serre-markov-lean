import SerreMarkov.Mutations

namespace SerreMarkov

/-- The integral normal presentation determined by vanishing symmetric cofactors
and Pfaffian minus four. -/
def reducedDegenerate (a b d : ℤ) : Six := ⟨a,b,-d,d,b-a*d,-a⟩

end SerreMarkov
