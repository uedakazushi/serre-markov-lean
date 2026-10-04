import SerreMarkov.PositiveBoundedChecks

/-!
# The complete bounded positive classification

Every actual solution in the chamber with all six coordinates at least three
and their sum at most thirty-seven is one of twenty-three explicit tuples.
Actual mutation words place each tuple in exactly one of the five manuscript
orbits. This is a bounded classification and does not assume or prove an
unbounded terminal-height bound, properness, degree, or a hyperbolic index.
-/

namespace SerreMarkov.PositiveBounded

theorem bounded_mem_table (z : Six) (hz : Bounded z) : z ∈ PositiveBoundedTable.table := by
  have h := bounded_mem_allSolutions z hz
  rw [solutions_split] at h
  obtain ⟨a,ha,h⟩ := List.mem_flatMap.mp h
  obtain ⟨b,hb,h⟩ := List.mem_flatMap.mp h
  have ha20 : a < 20 := List.mem_range.mp ha
  have hb' : b < 19-a+1 := List.mem_range.mp hb
  have hsum : a+b ≤ 19 := by omega
  have hb20 : b < 20 := by omega
  exact blockCheck_correct a b (all_blocks_checked ⟨a,ha20⟩ ⟨b,hb20⟩ hsum) z h

theorem table_bounded (i : Fin 23) : Bounded (PositiveBoundedTable.tuple i) := by
  fin_cases i <;> decide +kernel

theorem table_injective : Function.Injective PositiveBoundedTable.tuple := by decide +kernel

/-- The entire bounded solution subtype consists of the twenty-three rows;
this is exhaustive in the stated region, not only a verification of examples. -/
theorem bounded_iff_table (z : Six) :
    Bounded z ↔ ∃ i : Fin 23, PositiveBoundedTable.tuple i = z := by
  constructor
  · intro hz
    have hm := bounded_mem_table z hz
    exact List.mem_ofFn.mp hm
  · rintro ⟨i,rfl⟩
    exact table_bounded i

theorem bounded_solution_card : Nat.card {z : Six // Bounded z} = 23 := by
  let f : Fin 23 → {z : Six // Bounded z} := fun i => ⟨PositiveBoundedTable.tuple i,table_bounded i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact table_injective (congrArg Subtype.val hij)
    · intro z
      obtain ⟨i,hi⟩ := (bounded_iff_table z.val).mp z.property
      exact ⟨i,Subtype.ext hi⟩
  calc
    _ = Nat.card (Fin 23) := Nat.card_congr (Equiv.ofBijective f hf).symm
    _ = 23 := by simp

/-- Exactly one original sporadic representative is reachable from every
solution in the stated bounded positive chamber. -/
theorem bounded_classification_unique (z : Six) (hz : Bounded z) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨i,hi⟩ := (bounded_iff_table z).mp hz
  have hr : Reachable z (PositiveExamples.representative (PositiveBoundedTable.representativeIndex i)) :=
    hi ▸ PositiveBoundedTable.tuple_reachable i
  refine ⟨PositiveBoundedTable.representativeIndex i,hr,?_⟩
  intro r hr'
  exact (PositiveExamples.representatives_reachable_iff _ _).mp
    (reachable_trans (reachable_symm hr') hr)

theorem positive_bounded_classification (z : Six) (hz : isSolution z)
    (hpos : 0 < IntrinsicSigns.thirdMinorSum z)
    (hcoords : 3 ≤ z.a ∧ 3 ≤ z.b ∧ 3 ≤ z.c ∧ 3 ≤ z.d ∧ 3 ≤ z.e ∧ 3 ≤ z.f)
    (hbound : z.a+z.b+z.c+z.d+z.e+z.f ≤ 37) :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hcoords
  exact bounded_classification_unique z ⟨hz,ha,hb,hc,hd,he,hf,hpos,hbound⟩

/-- The bounded result transports along an actual mutation word. The only
extra input is a reachable point in the stated bounded chamber. -/
theorem reachable_bounded_classification_unique (z z' : Six)
    (hz' : Bounded z') (hreach : Reachable z z') :
    ∃! r : Fin 5, Reachable z (PositiveExamples.representative r) := by
  obtain ⟨r,hr,hunique⟩ := bounded_classification_unique z' hz'
  refine ⟨r,reachable_trans hreach hr,?_⟩
  intro s hs
  exact hunique s (reachable_trans (reachable_symm hreach) hs)

end SerreMarkov.PositiveBounded
