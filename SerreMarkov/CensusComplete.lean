import SerreMarkov.CensusCoverage10
import SerreMarkov.CycleBridge

/-!
# Complete five-class census

Every involution is covered by the generic partner-enumeration theorem.  The
untrusted row data are identified with that complete list by kernel reduction,
and every row's witness has separately been checked in the kernel.

Transitivity is actual reachability by words in alpha and beta.  The two-cusp
condition is coverage by two full cyclic orbits. No bounded word search or
unproved census assumption appears in the main theorem.
-/

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

namespace SerreMarkov.IndexTwelve

/-- The explicit certificate table covers exactly the recursively generated
list, in the same order. This equality is checked by Lean's kernel. -/
theorem census_projection_eq_enumeration :
    allCensusRows.map (fun row => vertexCode row.alpha) = allMatchingInvolutions := by
  rw [← censusPartnerBlocks_cover, ← matchingPartnerBlocks_cover, List.map_flatMap]
  apply List.flatMap_congr
  intro j hj
  have hj' : j < 11 := List.mem_range.mp hj
  interval_cases j
  · exact censusPartnerBlock00_projection
  · exact censusPartnerBlock01_projection
  · exact censusPartnerBlock02_projection
  · exact censusPartnerBlock03_projection
  · exact censusPartnerBlock04_projection
  · exact censusPartnerBlock05_projection
  · exact censusPartnerBlock06_projection
  · exact censusPartnerBlock07_projection
  · exact censusPartnerBlock08_projection
  · exact censusPartnerBlock09_projection
  · exact censusPartnerBlock10_projection

/-- The complete recursive candidate list has the stated 10,395 entries. -/
theorem allMatchingInvolutions_length : allMatchingInvolutions.length = 10395 := by
  calc
    allMatchingInvolutions.length =
        (allCensusRows.map (fun row => vertexCode row.alpha)).length := by
          rw [census_projection_eq_enumeration]
    _ = allCensusRows.length := List.length_map _
    _ = 10395 := allCensusRows_length

def disconnectedRow (row : CensusRow) : Bool :=
  match row.witness with
  | .disconnected _ => true
  | _ => false

def manyCyclesRow (row : CensusRow) : Bool :=
  match row.witness with
  | .manyCycles _ => true
  | _ => false

def conjugateRow (row : CensusRow) : Bool :=
  match row.witness with
  | .conjugate _ _ => true
  | _ => false

/-- Exact numbers of the three verified certificate kinds. -/
theorem census_witness_counts :
    allCensusRows.countP disconnectedRow = 675 ∧
    allCensusRows.countP manyCyclesRow = 5184 ∧
    allCensusRows.countP conjugateRow = 4536 := by
  decide +kernel

/-- The genuinely exhaustive census: every fixed-point-free involution alpha
whose pair with beta is transitive and whose cusp permutation has at most two
cyclic orbits is simultaneously conjugate to one of the five table pairs. -/
theorem complete_index_twelve_census (a : VertexMap)
    (hinv : ∀ i, a (a i) = i) (hnofix : ∀ i, a i ≠ i)
    (ht : TransitivePair a) (htwo : AtMostTwoCycles (cusp a)) :
    ∃ r : Fin 5, ConjugateFixedBeta a (representative r) := by
  have hm := allMatchingInvolutions_complete a hinv hnofix
  rw [← census_projection_eq_enumeration] at hm
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hm
  subst a
  exact witness_gives_classification (vertexCode row.alpha) row.witness
    (allCensusRows_checked row hrow) ht htwo

/-- Fixed-point counts of the first four powers of the cusp permutation. -/
def fixedSignature (a : VertexMap) (j : Fin 4) : Nat :=
  (Finset.univ.filter fun i : Vertex => ((cusp a)^[j.val + 1]) i = i).card

/-- Simultaneous conjugacy preserves the fixed-point signature. -/
theorem fixedSignature_conjugate {a b : VertexMap}
    (h : ConjugateFixedBeta a b) : fixedSignature a = fixedSignature b := by
  obtain ⟨g, hg, ha, hb⟩ := h
  have hp : ∀ i, g (cusp a i) = cusp b (g i) := by
    intro i
    simp only [cusp, ha, hb]
  have hpow : ∀ n i, g ((cusp a)^[n] i) = (cusp b)^[n] (g i) := by
    intro n
    induction n with
    | zero => intro i; rfl
    | succ n ih =>
        intro i
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hp, ih]
  funext j
  apply Finset.card_bijective g hg
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    rw [← hpow, hi]
  · intro hi
    apply hg.1
    rw [hpow, hi]

/-- The five representatives have pairwise different signatures. -/
theorem representative_signatures_injective :
    Function.Injective (fun r : Fin 5 => fixedSignature (representative r)) := by
  unfold Function.Injective
  decide

/-- No two of the five table pairs are simultaneously conjugate. -/
theorem representatives_distinct {r s : Fin 5}
    (h : ConjugateFixedBeta (representative r) (representative s)) : r = s :=
  representative_signatures_injective (fixedSignature_conjugate h)

/-- The exhaustive census gives a unique table representative. -/
theorem complete_index_twelve_census_unique (a : VertexMap)
    (hinv : ∀ i, a (a i) = i) (hnofix : ∀ i, a i ≠ i)
    (ht : TransitivePair a) (htwo : AtMostTwoCycles (cusp a)) :
    ∃! r : Fin 5, ConjugateFixedBeta a (representative r) := by
  obtain ⟨r, hr⟩ := complete_index_twelve_census a hinv hnofix ht htwo
  refine ⟨r, hr, ?_⟩
  intro s hs
  apply representative_signatures_injective
  exact (fixedSignature_conjugate hs).symm.trans (fixedSignature_conjugate hr)

/-- Each representative is an admissible fixed-point-free involution. -/
theorem representative_involutive (r : Fin 5) :
    ∀ i, representative r (representative r i) = i := by
  fin_cases r
  · exact alphaOneEleven_involutive
  · exact alphaTwoTen_involutive
  · exact alphaThreeNine_involutive
  · exact alphaFourEight_involutive
  · exact alphaSixSix_involutive

theorem representative_fixed_point_free (r : Fin 5) :
    ∀ i, representative r i ≠ i := by
  fin_cases r
  · exact alphaOneEleven_fixed_point_free
  · exact alphaTwoTen_fixed_point_free
  · exact alphaThreeNine_fixed_point_free
  · exact alphaFourEight_fixed_point_free
  · exact alphaSixSix_fixed_point_free

theorem representative_transitive (r : Fin 5) : TransitivePair (representative r) := by
  fin_cases r
  · exact alphaOneEleven_transitive
  · exact alphaTwoTen_transitive
  · exact alphaThreeNine_transitive
  · exact alphaFourEight_transitive
  · exact alphaSixSix_transitive

def representativeCycleLeft (r : Fin 5) : List Vertex :=
  match r.val with
  | 0 => alphaOneElevenCycleLeft
  | 1 => alphaTwoTenCycleLeft
  | 2 => alphaThreeNineCycleLeft
  | 3 => alphaFourEightCycleLeft
  | _ => alphaSixSixCycleLeft

def representativeCycleRight (r : Fin 5) : List Vertex :=
  match r.val with
  | 0 => alphaOneElevenCycleRight
  | 1 => alphaTwoTenCycleRight
  | 2 => alphaThreeNineCycleRight
  | 3 => alphaFourEightCycleRight
  | _ => alphaSixSixCycleRight

theorem representative_cycle_decomposition (r : Fin 5) :
    TwoCycleDecomposition (cusp (representative r))
      (representativeCycleLeft r) (representativeCycleRight r) := by
  fin_cases r
  · exact alphaOneEleven_cusp_decomposition
  · exact alphaTwoTen_cusp_decomposition
  · exact alphaThreeNine_cusp_decomposition
  · exact alphaFourEight_cusp_decomposition
  · exact alphaSixSix_cusp_decomposition

theorem representative_atMostTwoCycles (r : Fin 5) :
    AtMostTwoCycles (cusp (representative r)) :=
  twoCycleDecomposition_atMostTwoCycles _ _ _ (representative_cycle_decomposition r)

/-- The finite census in the original two-cycle-list formulation: its entire
input domain of involutions is covered and the table class is unique. -/
theorem complete_index_twelve_census_two_cycles (a : VertexMap)
    (hinv : ∀ i, a (a i) = i) (hnofix : ∀ i, a i ≠ i)
    (ht : TransitivePair a)
    (htwo : ∃ left right, TwoCycleDecomposition (cusp a) left right) :
    ∃! r : Fin 5, ConjugateFixedBeta a (representative r) := by
  obtain ⟨left, right, hcycles⟩ := htwo
  exact complete_index_twelve_census_unique a hinv hnofix ht
    (twoCycleDecomposition_atMostTwoCycles _ _ _ hcycles)

end SerreMarkov.IndexTwelve
