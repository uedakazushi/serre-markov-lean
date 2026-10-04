import SerreMarkov.BetaNormalization
import SerreMarkov.CensusComplete

/-! # The complete index-twelve census without a fixed beta labeling -/

namespace SerreMarkov.IndexTwelve

/-- Every admissible pair of an involution and a cubic permutation on twelve
vertices is simultaneously conjugate to exactly one table pair. -/
theorem arbitrary_beta_census_unique (a b : VertexMap)
    (ha : ∀ i, a (a i) = i) (hafree : ∀ i, a i ≠ i)
    (hb : ∀ i, b (b (b i)) = i) (hbfree : ∀ i, b i ≠ i)
    (ht : PairTransitive a b) (htwo : AtMostTwoCycles (fun i => a (b i))) :
    ∃! r : Fin 5, ∃ c : Equiv.Perm Vertex,
      (∀ i, c (a i) = representative r (c i)) ∧
      (∀ i, c (b i) = beta (c i)) := by
  obtain ⟨c, a', hcb, hca, ha', hafree', ht', htwo'⟩ :=
    beta_normalization_census_hypotheses a b ha hafree hb hbfree ht htwo
  obtain ⟨r, hr, huniq⟩ :=
    complete_index_twelve_census_unique a' ha' hafree' ht' htwo'
  obtain ⟨g, hg, hga, hgb⟩ := hr
  let d : Equiv.Perm Vertex := Equiv.ofBijective g hg
  refine ⟨r, ⟨c.trans d, ?_, ?_⟩, ?_⟩
  · intro i
    change g (c (a i)) = representative r (g (c i))
    rw [hca, hga]
  · intro i
    change g (c (b i)) = beta (g (c i))
    rw [hcb, hgb]
  · intro s hs
    obtain ⟨e, hea, heb⟩ := hs
    apply huniq s
    refine ⟨c.symm.trans e, (c.symm.trans e).bijective, ?_, ?_⟩
    · intro i
      change e (c.symm (a' i)) = representative s (e (c.symm i))
      have hinv : c.symm (a' i) = a (c.symm i) := by
        have h := congrArg c.symm (hca (c.symm i))
        simpa using h.symm
      rw [hinv, hea]
    · intro i
      change e (c.symm (beta i)) = beta (e (c.symm i))
      have hinv : c.symm (beta i) = b (c.symm i) := by
        have h := congrArg c.symm (hcb (c.symm i))
        simpa using h.symm
      rw [hinv, heb]

end SerreMarkov.IndexTwelve
