import SerreMarkov.NegativeSmallReduction

/-! # Reduction to the three adjacent small-edge branches

Each of the six original pairings can be moved to the first adjacent position
by an explicit braid word of length at most four. The preceding unconditional
small-edge reduction and an actual basis sign change then reduce every negative
solution to `a=0`, `a=1`, or `a=2`.
-/

namespace SerreMarkov.NegativeAdjacentReduction

open NegativeSmallReduction

inductive Edge where
  | a | b | c | d | e | f
  deriving DecidableEq

def edgeValue (z : Six) : Edge → ℤ
  | .a => z.a
  | .b => z.b
  | .c => z.c
  | .d => z.d
  | .e => z.e
  | .f => z.f

def edgeWord : Edge → List Generator
  | .a => []
  | .b => [.i2]
  | .c => [.i3,.i2]
  | .d => [.i1,.i2]
  | .e => [.i1,.i3,.i2]
  | .f => [.i2,.i1,.i3,.i2]

/-- The first coordinate is exactly the specified original edge. -/
theorem edgeWord_first_coordinate (z : Six) (i : Edge) :
    (applyWord z (edgeWord i)).a = edgeValue z i := by
  cases i <;> rfl

theorem edgeWord_length (i : Edge) : (edgeWord i).length ≤ 4 := by
  cases i <;> decide

theorem smallEdge_has_index (z : Six) (h : SmallEdge z) : ∃ i : Edge, |edgeValue z i| ≤ 2 := by
  rcases h with h | h | h | h | h | h
  · exact ⟨.a,h⟩
  · exact ⟨.b,h⟩
  · exact ⟨.c,h⟩
  · exact ⟨.d,h⟩
  · exact ⟨.e,h⟩
  · exact ⟨.f,h⟩

/-- Actual mutation paths preserve the negative intrinsic sign. -/
theorem reachable_negative {z w : Six} (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hr : Reachable z w) :
    IntrinsicSigns.thirdMinorSum w < 0 := by
  have hw : isSolution w := reachable_preserves_solution hr hz
  have hk : intrinsicKind z = .negative := (intrinsicKind_negative_iff z hz).mpr hneg
  have hkw : intrinsicKind w = .negative := by
    rw [← reachable_intrinsicKind hz hr]
    exact hk
  exact (intrinsicKind_negative_iff w hw).mp hkw

/-- Any of the six small-edge boundary cases reaches the first-edge boundary. -/
theorem smallEdge_reachable_first_edge (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hsmall : SmallEdge z) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧ |w.a| ≤ 2 := by
  obtain ⟨i,hi⟩ := smallEdge_has_index z hsmall
  let w := applyWord z (edgeWord i)
  have hr : Reachable z w := ⟨edgeWord i,rfl⟩
  refine ⟨w,hr,reachable_preserves_solution hr hz,reachable_negative hz hneg hr,?_⟩
  change |(applyWord z (edgeWord i)).a| ≤ 2
  rw [edgeWord_first_coordinate]
  exact hi

/-- Every negative solution reaches an adjacent pairing of absolute value at most two. -/
theorem negative_reachable_first_edge (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧ |w.a| ≤ 2 := by
  obtain ⟨s,hrs,hs,hsneg,hssmall⟩ := negative_reachable_small_edge z hz hneg
  obtain ⟨w,hrw,hw,hwn,hwsmall⟩ := smallEdge_reachable_first_edge s hs hsneg hssmall
  exact ⟨w,reachable_trans hrs hrw,hw,hwn,hwsmall⟩

/-- A basis sign change makes the small first pairing nonnegative. -/
theorem negative_reachable_nonnegative_first_edge (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧
      0 ≤ w.a ∧ w.a ≤ 2 := by
  obtain ⟨w,hr,hw,hwn,hwa⟩ := negative_reachable_first_edge z hz hneg
  have habs := abs_le.mp hwa
  by_cases ha : w.a < 0
  · have hs : Reachable w (eps2 w) := ⟨[.s2],rfl⟩
    refine ⟨eps2 w,reachable_trans hr hs,reachable_preserves_solution hs hw,
      reachable_negative hw hwn hs,?_,?_⟩
    · change 0 ≤ -w.a
      omega
    · change -w.a ≤ 2
      omega
  · exact ⟨w,hr,hw,hwn,by omega,habs.2⟩

/-- The complete negative locus is unconditionally reduced to three integer branches. -/
theorem negative_reachable_first_edge_cases (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w < 0 ∧
      (w.a = 0 ∨ w.a = 1 ∨ w.a = 2) := by
  obtain ⟨w,hr,hw,hwn,ha0,ha2⟩ := negative_reachable_nonnegative_first_edge z hz hneg
  exact ⟨w,hr,hw,hwn,by omega⟩

/-- The reduction consists of a genuine finite word in the ten authorized generators. -/
theorem negative_finite_word_first_edge_cases (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ word : List Generator, isSolution (applyWord z word) ∧
      IntrinsicSigns.thirdMinorSum (applyWord z word) < 0 ∧
      ((applyWord z word).a = 0 ∨ (applyWord z word).a = 1 ∨ (applyWord z word).a = 2) := by
  obtain ⟨w,⟨word,hw⟩,hs,hn,hcases⟩ := negative_reachable_first_edge_cases z hz hneg
  exact ⟨word,by simpa only [hw] using hs,by simpa only [hw] using hn,
    by simpa only [hw] using hcases⟩

end SerreMarkov.NegativeAdjacentReduction
