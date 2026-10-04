import SerreMarkov.PositiveSortedTerminalSmall
import SerreMarkov.PositiveSortedFiveBoundary
import SerreMarkov.PositiveSortedFiveLarge
import SerreMarkov.PositiveSortedLarge
import SerreMarkov.PositiveRepresentativeInvariants

/-! # Unrestricted positive classification

Actual minimum-height chambers are sorted while retaining each of the five
orbit membership predicates. The sorted first edge is at most five. Edge
five is excluded, and the complete edge-three and edge-four proofs give the
unique original manuscript representative. No reduction hypothesis remains.
-/

namespace SerreMarkov.PositiveClassificationFull
open PositiveChamber PositiveShortWord PositiveSortedTerminal

theorem sorted_terminal_classification (z : Six) (hz : Chamber z)
    (ht : AllTerminal z) (hs : SortedOuter z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  have ha5 := PositiveSortedLarge.sorted_first_edge_le_five z hz hs ht
  by_cases ha4 : z.a≤4
  · exact PositiveSortedTerminalSmall.first_edge_le_four_sorted_classification
      z hz (ht 3) hs ha4
  · have ha : z.a=5 := by omega
    obtain ⟨hd,hf⟩ := PositiveSortedFiveBoundary.first_five_sorted_large_region
      z hz ha hs (ht 2)
    exact (PositiveSortedFiveLarge.a_five_sorted_large_impossible z hz ha hs.2.2.2
      hd hf (ht 3)).elim

/-- Every positive integer solution lies in exactly one of the five actual
signed mutation orbits, without an initial coefficient or height bound. -/
theorem positive_classification (z : Six) (hz : isSolution z)
    (hp : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) :=
  positive_classification_of_sorted_terminal
    (fun w hw ht hs => sorted_terminal_classification w hw ht hs) z hz hp

theorem positive_classification_with_invariants (z : Six) (hz : isSolution z)
    (hp : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) ∧
      ∀ R : IntrinsicFrame.Frame z,
        IntrinsicFrame.A R=PositiveRepresentativeInvariants.aValue r ∧
        R.flag.k=PositiveRepresentativeInvariants.kValue r := by
  obtain ⟨r,hr,hu⟩ := positive_classification z hz hp
  refine ⟨r,⟨hr,?_⟩,fun s hs => hu s hs.1⟩
  intro R
  have h := IntrinsicUnique.latticeEquivalent_frame_invariants R
    (PositiveRepresentativeInvariants.explicitFrame r) (reachable_latticeEquivalent hr)
  exact ⟨h.2.trans (PositiveRepresentativeInvariants.explicitFrame_A r),
    h.1.trans (PositiveRepresentativeInvariants.explicitFrame_k r)⟩

theorem positive_iff_sporadic_reachable (z : Six) (hz : isSolution z) :
    0<IntrinsicSigns.thirdMinorSum z ↔
      ∃ r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  constructor
  · intro hp
    exact (positive_classification z hz hp).exists
  · rintro ⟨r,hr⟩
    apply (intrinsicKind_positive_iff z hz).mp
    exact (reachable_intrinsicKind hz hr).trans
      (PositiveExamples.representative_intrinsicKind r)

/-- The integer cube content directly identifies the positive orbit. -/
theorem positive_reachable_iff_cube_content (z : Six) (hz : isSolution z)
    (hp : 0<IntrinsicSigns.thirdMinorSum z) (r : Fin 5) :
    Reachable z (PositiveExamples.representative r) ↔
      matrixContent (shiftedSerre z^3)=PositiveExamples.cubeContent r := by
  constructor
  · intro hr
    exact (latticeEquivalent_shifted_power_content (reachable_latticeEquivalent hr) 3).trans
      (PositiveExamples.representative_cube_content r)
  · intro hc
    obtain ⟨s,hs,_⟩ := positive_classification z hz hp
    have hscontent :=
      (latticeEquivalent_shifted_power_content (reachable_latticeEquivalent hs) 3).trans
        (PositiveExamples.representative_cube_content s)
    have hrs : s=r := PositiveExamples.cubeContent_injective (hscontent.symm.trans hc)
    subst s
    exact hs

end SerreMarkov.PositiveClassificationFull
