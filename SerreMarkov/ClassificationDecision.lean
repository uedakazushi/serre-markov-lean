import SerreMarkov.FullClassificationPipeline

/-!
# Executable search for the canonical mutation representative

Each finite search layer enumerates all ten mutations and their inverses.
The canonical parser performs only integer comparisons. `Nat.find` searches
these decidable layers; the explicit positive-completeness argument supplies
termination, and is erased from the compiled program. This is an exhaustive
decision algorithm, with no assertion of a practical complexity bound.
-/

namespace SerreMarkov.ClassificationDecision

open CanonicalRepresentatives NegativeClassification FullClassificationPipeline
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

deriving instance DecidableEq, Repr for Canonical

def parsePositive (z : Six) : Option Canonical :=
  if z=PositiveExamples.representative 0 then some (.positive 0) else
  if z=PositiveExamples.representative 1 then some (.positive 1) else
  if z=PositiveExamples.representative 2 then some (.positive 2) else
  if z=PositiveExamples.representative 3 then some (.positive 3) else
  if z=PositiveExamples.representative 4 then some (.positive 4) else none

theorem parsePositive_sound (z : Six) (c : Canonical) (h : parsePositive z=some c) :
    representative c=z := by
  unfold parsePositive at h
  split_ifs at h with h0 h1 h2 h3 h4
  all_goals cases h
  all_goals dsimp [representative]; symm; assumption

theorem parsePositive_complete (i : Fin 5) :
    parsePositive (PositiveExamples.representative i)=some (.positive i) := by
  fin_cases i <;> decide +kernel

instance normalizedNegativePairDecidable (p : ℤ×ℤ) : Decidable (NormalizedNegativePair p) :=
  inferInstanceAs (Decidable (0≤p.2 ∧ p.2≤p.1 ∧ 0<p.1+p.2))

/-- Recover the family parameters directly from the first and fifth entries,
then test the manuscript's canonical parameter region. -/
def parseCanonical (z : Six) : Option Canonical :=
  if hfamily : z=family (-z.a) (-z.e) then
    if hzero : 0≤-z.a ∧ z.e= -z.a then
      some (.degenerate (-z.a).toNat)
    else if hnormal : NormalizedNegativePair (-z.a,-z.e) then
      some (.negative ⟨(-z.a,-z.e),hnormal⟩)
    else none
  else parsePositive z

theorem parseCanonical_sound (z : Six) (c : Canonical) (h : parseCanonical z=some c) :
    representative c=z := by
  by_cases hfamily : z=family (-z.a) (-z.e)
  · by_cases hzero : 0≤-z.a ∧ z.e= -z.a
    · rw [parseCanonical,dif_pos hfamily,dif_pos hzero] at h
      cases h
      simp only [representative,Int.toNat_of_nonneg hzero.1]
      calc
        family (-z.a) (-(-z.a))=family (-z.a) (-z.e) := by congr 1; omega
        _=z := hfamily.symm
    · by_cases hnormal : NormalizedNegativePair (-z.a,-z.e)
      · rw [parseCanonical,dif_pos hfamily,dif_neg hzero,dif_pos hnormal] at h
        cases h
        exact hfamily.symm
      · rw [parseCanonical,dif_pos hfamily,dif_neg hzero,dif_neg hnormal] at h
        contradiction
  · rw [parseCanonical,dif_neg hfamily] at h
    exact parsePositive_sound z c h

private theorem family_not_positive (x y : ℤ) (i : Fin 5) :
    family x y≠PositiveExamples.representative i := by
  intro h
  have hc := congrArg Six.c h
  fin_cases i <;> norm_num [family,PositiveExamples.representative] at hc

theorem parseCanonical_complete (c : Canonical) :
    parseCanonical (representative c)=some c := by
  cases c with
  | degenerate k =>
      have hk : 0≤(k : ℤ) := Nat.cast_nonneg k
      simp [parseCanonical,representative,family,hk]
  | negative p =>
      have hnorm := p.property
      have hzero : ¬(0≤p.val.1 ∧ -p.val.2=p.val.1) := by
        have hp := p.property
        unfold NormalizedNegativePair at hp
        omega
      simp [parseCanonical,representative,family,hzero,hnorm]
  | positive i =>
      have hn : PositiveExamples.representative i≠
          family (-(PositiveExamples.representative i).a) (-(PositiveExamples.representative i).e) :=
        fun h => family_not_positive _ _ i h.symm
      simp only [representative,parseCanonical,hn,dif_neg]
      exact parsePositive_complete i

/-- Both braid directions and all four independent basis signs. -/
def allMoves : List Generator :=
  [.m1,.m2,.m3,.i1,.i2,.i3,.s1,.s2,.s3,.s4]

theorem mem_allMoves (g : Generator) : g∈allMoves := by
  cases g <;> simp [allMoves]

/-- All words of exactly n letters; the search proceeds through n=0,1,2,… . -/
def allWords : ℕ → List (List Generator)
  | 0 => [[]]
  | n+1 => allMoves.flatMap (fun g => (allWords n).map (g :: ·))

theorem word_mem_allWords (word : List Generator) : word∈allWords word.length := by
  induction word with
  | nil => simp [allWords]
  | cons g tail ih =>
      simp only [List.length_cons,allWords,List.mem_flatMap,List.mem_map]
      exact ⟨g,mem_allMoves g,tail,ih,rfl⟩

def inspectWord (z : Six) (word : List Generator) : Option (List Generator×Canonical) :=
  (parseCanonical (applyWord z word)).map (fun c => (word,c))

theorem inspectWord_sound (z : Six) (word u : List Generator) (c : Canonical)
    (h : inspectWord z word=some (u,c)) : applyWord z u=representative c := by
  simp only [inspectWord,Option.map_eq_some_iff] at h
  obtain ⟨d,hd,heq⟩ := h
  have hpair := Prod.mk.inj heq
  rw [←hpair.1,←hpair.2]
  exact (parseCanonical_sound _ _ hd).symm

def searchLayer (z : Six) (n : ℕ) : Option (List Generator×Canonical) :=
  (allWords n).findSome? (inspectWord z)

theorem searchLayer_sound (z : Six) (n : ℕ) (word : List Generator) (c : Canonical)
    (h : searchLayer z n=some (word,c)) : applyWord z word=representative c := by
  obtain ⟨u,_,hu⟩ := List.exists_of_findSome?_eq_some h
  exact inspectWord_sound z u word c hu

/-- A genuine finite mutation word guarantees that exhaustive search reaches
a nonempty decidable layer. The existence proof does not select runtime data. -/
theorem search_terminates (z : Six) (hex : ∃ c : Canonical,Reachable z (representative c)) :
    ∃ n : ℕ,(searchLayer z n).isSome := by
  obtain ⟨c,word,hw⟩ := hex
  refine ⟨word.length,List.findSome?_isSome_iff.mpr
    ⟨word,word_mem_allWords word,?_⟩⟩
  simp [inspectWord,hw,parseCanonical_complete]

/-- `Nat.find` here uses the computational Bool test for a finite search layer.
There is no use of classical proposition decision in this definition. -/
def searchDepth (z : Six) (hex : ∃ c : Canonical,Reachable z (representative c)) : ℕ :=
  Nat.find (search_terminates z hex)

theorem searchDepth_spec (z : Six) (hex : ∃ c : Canonical,Reachable z (representative c)) :
    (searchLayer z (searchDepth z hex)).isSome :=
  Nat.find_spec (search_terminates z hex)

def normalizeWithWitness (z : Six) (hex : ∃ c : Canonical,Reachable z (representative c)) :
    List Generator×Canonical :=
  (searchLayer z (searchDepth z hex)).get (searchDepth_spec z hex)

theorem normalizeWithWitness_word (z : Six)
    (hex : ∃ c : Canonical,Reachable z (representative c)) :
    applyWord z (normalizeWithWitness z hex).1=
      representative (normalizeWithWitness z hex).2 := by
  apply searchLayer_sound z (searchDepth z hex)
  exact (Option.some_get (searchDepth_spec z hex)).symm

theorem normalizeWithWitness_reachable (z : Six)
    (hex : ∃ c : Canonical,Reachable z (representative c)) :
    Reachable z (representative (normalizeWithWitness z hex).2) :=
  ⟨(normalizeWithWitness z hex).1,normalizeWithWitness_word z hex⟩

/-- Full canonical classification is the termination certificate. Only its
positive-completeness hypothesis remains explicit in this executable helper. -/
def classify (hpos : PositiveCompleteness) (z : Solution) : List Generator×Canonical :=
  normalizeWithWitness z.val
    (canonical_classification_of_positive hpos z.val z.property).exists

theorem classify_word (hpos : PositiveCompleteness) (z : Solution) :
    applyWord z.val (classify hpos z).1=representative (classify hpos z).2 :=
  normalizeWithWitness_word _ _

theorem classify_reachable (hpos : PositiveCompleteness) (z : Solution) :
    Reachable z.val (representative (classify hpos z).2) :=
  ⟨(classify hpos z).1,classify_word hpos z⟩

theorem classify_target_eq_iff_reachable (hpos : PositiveCompleteness) (z w : Solution) :
    (classify hpos z).2=(classify hpos w).2 ↔ Reachable z.val w.val := by
  constructor
  · intro heq
    have hz := classify_reachable hpos z
    have hw := classify_reachable hpos w
    rw [heq] at hz
    exact reachable_trans hz (reachable_symm hw)
  · intro hr
    exact canonical_target_unique z.val _ _ (classify_reachable hpos z)
      (reachable_trans hr (classify_reachable hpos w))

/-- Comparing computed canonical targets decides the full mutation relation. -/
def mutationEquivalentTest (hpos : PositiveCompleteness) (z w : Solution) : Bool :=
  decide ((classify hpos z).2=(classify hpos w).2)

theorem mutationEquivalentTest_correct (hpos : PositiveCompleteness) (z w : Solution) :
    mutationEquivalentTest hpos z w=true ↔ Reachable z.val w.val := by
  simp only [mutationEquivalentTest,decide_eq_true_eq,classify_target_eq_iff_reachable]

/-- The executable equality test can also be used as a `Decidable` instance,
with correctness supplied by canonical uniqueness. -/
def mutationEquivalenceDecidable (hpos : PositiveCompleteness) (z w : Solution) :
    Decidable (Reachable z.val w.val) :=
  decidable_of_iff ((classify hpos z).2=(classify hpos w).2)
    (classify_target_eq_iff_reachable hpos z w)

/-- If the inputs are equivalent, concatenate the computed normalization
word with the inverse normalization word of the second input. -/
def equivalenceWord (hpos : PositiveCompleteness) (z w : Solution) : Option (List Generator) :=
  if (classify hpos z).2=(classify hpos w).2 then
    some ((classify hpos z).1 ++ (classify hpos w).1.reverse.map inverseGenerator)
  else none

theorem equivalenceWord_sound (hpos : PositiveCompleteness) (z w : Solution)
    (word : List Generator) (h : equivalenceWord hpos z w=some word) :
    applyWord z.val word=w.val := by
  unfold equivalenceWord at h
  split_ifs at h with heq
  · cases h
    rw [applyWord_append,classify_word hpos z,heq,←classify_word hpos w,applyWord_inverse]

theorem equivalenceWord_isSome_iff (hpos : PositiveCompleteness) (z w : Solution) :
    (equivalenceWord hpos z w).isSome ↔ Reachable z.val w.val := by
  rw [←classify_target_eq_iff_reachable hpos z w]
  by_cases heq : (classify hpos z).2=(classify hpos w).2 <;>
    simp [equivalenceWord,heq]

end SerreMarkov.ClassificationDecision
