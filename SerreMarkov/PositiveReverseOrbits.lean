import SerreMarkov.PositiveReversal
import SerreMarkov.PositiveReduction

/-! # Reversal preserves each of the five actual positive orbits

Reversal acts on mutation words by the proved generator automorphism.
The five reversed original representatives reach their original representative
using the already verified bounded table, with its row identities checked in
the kernel.
-/

namespace SerreMarkov.PositiveReverseOrbits
open PositiveAdjacentThrees PositiveReversal PositiveReduction

theorem reverse_reachable {z w : Six} (hr : Reachable z w) :
    Reachable (reverseSix z) (reverseSix w) := by
  obtain ⟨word,hword⟩ := hr
  refine ⟨word.map reverseGenerator,?_⟩
  rw [←reverseSix_applyWord,hword]

def reversedRepresentativeRow (r : Fin 5) : Fin 23 := ![6,15,20,22,2] r

theorem reverse_representativeRow (r : Fin 5) :
    reverseSix (PositiveBoundedTable.tuple (representativeRow r))=
      PositiveBoundedTable.tuple (reversedRepresentativeRow r) := by
  fin_cases r <;> decide +kernel

theorem reversedRepresentativeRow_index (r : Fin 5) :
    PositiveBoundedTable.representativeIndex (reversedRepresentativeRow r)=r := by
  fin_cases r <;> decide +kernel

theorem reversed_representative_reachable (r : Fin 5) :
    Reachable (reverseSix (PositiveExamples.representative r))
      (PositiveExamples.representative r) := by
  have hrow : Reachable (PositiveBoundedTable.tuple (representativeRow r))
      (PositiveExamples.representative r) := by
    simpa only [representativeRow_index] using PositiveBoundedTable.tuple_reachable (representativeRow r)
  have hr := reverse_reachable (reachable_symm hrow)
  rw [reverse_representativeRow] at hr
  have hlast : Reachable (PositiveBoundedTable.tuple (reversedRepresentativeRow r))
      (PositiveExamples.representative r) := by
    simpa only [reversedRepresentativeRow_index] using
      PositiveBoundedTable.tuple_reachable (reversedRepresentativeRow r)
  exact reachable_trans hr hlast

theorem reverse_sporadic_reachable_iff (z : Six) (r : Fin 5) :
    Reachable (reverseSix z) (PositiveExamples.representative r) ↔
      Reachable z (PositiveExamples.representative r) := by
  constructor
  · intro hr
    have h := reverse_reachable hr
    rw [reverseSix_involutive] at h
    exact reachable_trans h (reversed_representative_reachable r)
  · intro hr
    exact reachable_trans (reverse_reachable hr) (reversed_representative_reachable r)

end SerreMarkov.PositiveReverseOrbits
