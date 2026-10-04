import SerreMarkov.PositiveShortWord
import SerreMarkov.PositiveReduction

/-! # A genuine minimum in every positive mutation orbit

The minimum is over actual reachable positive chambers, and exists by the
well-ordering of the natural full-coordinate height. It is terminal for every
finite braid word. This existence lemma does not supply a numerical bound on
the minimum; that is the separate arithmetic classification obligation.
-/

namespace SerreMarkov.PositiveMinimalOrbit
open NegativeDescent PositiveChamber PositiveShortWord

theorem positive_solution_reachable_minimal_chamber (z : Six) (hz : isSolution z)
    (hpos : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃ w : Six, Chamber w ∧ Reachable z w ∧
      ∀ v : Six, Chamber v → Reachable z v → l1 w≤l1 v := by
  classical
  let P : ℕ → Prop := fun n => ∃ w : Six, Chamber w ∧ Reachable z w ∧ l1 w=n
  have hex : ∃ n, P n := by
    obtain ⟨w,hr,hw,hp,hcoord,_⟩ :=
      PositiveHeightNormalization.positive_solution_height_normalization z hz
        (positive_solution_regular z hz hpos) hpos
    exact ⟨l1 w,w,⟨hw,hp,hcoord⟩,hr,rfl⟩
  obtain ⟨w,hw,hr,heq⟩ := Nat.find_spec hex
  refine ⟨w,hw,hr,?_⟩
  intro v hv hrv
  rw [heq]
  exact Nat.find_min' hex ⟨v,hv,hrv,rfl⟩

/-- Every positive orbit has an actual chamber terminal for all braid words,
without an a priori bound on their length. -/
theorem positive_solution_reachable_all_terminal (z : Six) (hz : isSolution z)
    (hpos : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃ w : Six, Chamber w ∧ Reachable z w ∧ ∀ n : ℕ, ShortTerminal w n := by
  obtain ⟨w,hw,hr,hmin⟩ := positive_solution_reachable_minimal_chamber z hz hpos
  refine ⟨w,hw,hr,?_⟩
  intro n word hword
  have hg : ∀ g ∈ word, IsBraid g := fun g hmem =>
    braidMoves_isBraid (((mem_braidWords_iff n word).mp hword).2 g hmem)
  exact hmin (applyWord w word) (applyWord_preserves_chamber w hw word hg)
    (reachable_trans hr ⟨word,rfl⟩)

/-- A classification of all finite-word terminal chambers suffices for the
unrestricted positive classification. The premise remains explicit here. -/
theorem positive_classification_of_terminal
    (hterminal : ∀ w : Six, Chamber w → (∀ n : ℕ, ShortTerminal w n) →
      ∃! r : Fin 5, Reachable w (PositiveExamples.representative r))
    (z : Six) (hz : isSolution z) (hpos : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨w,hw,hr,ht⟩ := positive_solution_reachable_all_terminal z hz hpos
  obtain ⟨r,hrr,hunique⟩ := hterminal w hw ht
  refine ⟨r,reachable_trans hr hrr,?_⟩
  intro s hrs
  exact hunique s (reachable_trans (reachable_symm hr) hrs)

end SerreMarkov.PositiveMinimalOrbit
