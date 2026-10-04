import SerreMarkov.PositiveMinimalOrbit
import SerreMarkov.PositiveReverseOrbits
import SerreMarkov.CyclicMutation

/-! # Ordered terminal chambers for the remaining universal positive reduction

An actual minimum-height chamber is terminal for every finite braid word.
Cyclic mutation and reversal produce a chamber with its first outer edge
minimal and its next edge no greater than the other neighbor. The reduction
preserves reachability to each of the five original representatives; it does
not assume reachability of an arbitrary tuple to its reversal.
-/

namespace SerreMarkov.PositiveSortedTerminal
open PositiveChamber PositiveShortWord PositiveAdjacentThrees PositiveReversal
open CyclicMutation PositiveReverseOrbits NegativeDescent

def AllTerminal (z : Six) : Prop := ∀ n : ℕ, ShortTerminal z n
def SortedOuter (z : Six) : Prop := z.a≤z.c ∧ z.a≤z.d ∧ z.a≤z.f ∧ z.d≤z.c

theorem cycleWord_braid (n : ℕ) : ∀ g ∈ cycleWord n, g ∈ braidMoves := by
  induction n with
  | zero => simp [cycleWord]
  | succ n ih =>
    intro g hg
    simp only [cycleWord,List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · simp at hg
      rcases hg with rfl | rfl | rfl <;> simp [braidMoves]

theorem cyclePower_chamber (z : Six) (hz : Chamber z) (n : ℕ) : Chamber (cyclePower z n) := by
  have hp : 0<IntrinsicSigns.thirdMinorSum (cyclePower z n) := by
    change 0<negativeMarker (cyclePower z n)
    rw [cyclePower_marker]
    exact hz.2.1
  exact ⟨cyclePower_solution z hz.1 n,hp,cyclePower_coordinates (fun x => 3≤x) z n hz.2.2⟩

theorem cyclePower_all_terminal (z : Six) (n : ℕ) (ht : AllTerminal z) :
    AllTerminal (cyclePower z n) := by
  intro k word hw
  have hpath : cycleWord n++word ∈ braidWords (cycleWord n++word).length := by
    apply (mem_braidWords_iff _ _).mpr
    refine ⟨le_refl _,?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact cycleWord_braid n g hg
    · exact ((mem_braidWords_iff k word).mp hw).2 g hg
  have h := ht _ _ hpath
  rw [applyWord_append,applyWord_cycleWord] at h
  simpa only [l1_cyclePower] using h

theorem cyclePower_sporadic_reachable_iff (z : Six) (n : ℕ) (r : Fin 5) :
    Reachable (cyclePower z n) (PositiveExamples.representative r) ↔
      Reachable z (PositiveExamples.representative r) := by
  constructor
  · intro h
    exact reachable_trans (reachable_cyclePower z n) h
  · intro h
    exact reachable_trans (reachable_symm (reachable_cyclePower z n)) h

private theorem first_edge_minimal (z : Six) :
    ∃ n : Fin 4, (cyclePower z n).a≤(cyclePower z n).c ∧
      (cyclePower z n).a≤(cyclePower z n).d ∧ (cyclePower z n).a≤(cyclePower z n).f := by
  by_cases ha : z.a≤z.c ∧ z.a≤z.d ∧ z.a≤z.f
  · exact ⟨0,ha⟩
  by_cases hd : z.d≤z.a ∧ z.d≤z.f ∧ z.d≤z.c
  · exact ⟨1,hd⟩
  by_cases hf : z.f≤z.d ∧ z.f≤z.c ∧ z.f≤z.a
  · exact ⟨2,hf⟩
  refine ⟨3,?_⟩
  change z.c≤z.f ∧ z.c≤z.a ∧ z.c≤z.d
  omega

/-- The sorted point has the same five orbit membership predicates as the
original arbitrary positive solution. The order assumptions are proved. -/
theorem positive_solution_sorted_terminal_reduction (z : Six) (hz : isSolution z)
    (hpos : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃ w : Six, Chamber w ∧ AllTerminal w ∧ SortedOuter w ∧
      ∀ r : Fin 5, Reachable w (PositiveExamples.representative r) ↔
        Reachable z (PositiveExamples.representative r) := by
  obtain ⟨v,hv,hr,ht⟩ := PositiveMinimalOrbit.positive_solution_reachable_all_terminal z hz hpos
  obtain ⟨n,hn⟩ := first_edge_minimal v
  let u := cyclePower v n
  have hu := cyclePower_chamber v hv n
  have hut := cyclePower_all_terminal v n ht
  have hclass (r : Fin 5) : Reachable u (PositiveExamples.representative r) ↔
      Reachable z (PositiveExamples.representative r) := by
    rw [cyclePower_sporadic_reachable_iff]
    constructor
    · intro h
      exact reachable_trans hr h
    · intro h
      exact reachable_trans (reachable_symm hr) h
  by_cases horder : u.d≤u.c
  · exact ⟨u,hu,hut,⟨hn.1,hn.2.1,hn.2.2,horder⟩,hclass⟩
  · let w := cyclePower (reverseSix u) 2
    have hw := cyclePower_chamber (reverseSix u) (reverseSix_chamber u hu) 2
    have hwt := cyclePower_all_terminal (reverseSix u) 2
      (fun k => reverseSix_shortTerminal u k (hut k))
    refine ⟨w,hw,hwt,?_,?_⟩
    · change u.a≤u.d ∧ u.a≤u.c ∧ u.a≤u.f ∧ u.c≤u.d
      change u.a≤u.c ∧ u.a≤u.d ∧ u.a≤u.f at hn
      omega
    · intro r
      rw [cyclePower_sporadic_reachable_iff,reverse_sporadic_reachable_iff]
      exact hclass r

/-- Closing the ordered terminal locus closes the unrestricted positive
classification. The arithmetic premise is kept explicit until proved. -/
theorem positive_classification_of_sorted_terminal
    (hcore : ∀ w : Six, Chamber w → AllTerminal w → SortedOuter w →
      ∃! r : Fin 5, Reachable w (PositiveExamples.representative r))
    (z : Six) (hz : isSolution z) (hpos : 0<IntrinsicSigns.thirdMinorSum z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨w,hw,ht,hs,horbits⟩ := positive_solution_sorted_terminal_reduction z hz hpos
  obtain ⟨r,hr,hunique⟩ := hcore w hw ht hs
  exact ⟨r,(horbits r).mp hr,fun s hs => hunique s ((horbits s).mpr hs)⟩

end SerreMarkov.PositiveSortedTerminal
