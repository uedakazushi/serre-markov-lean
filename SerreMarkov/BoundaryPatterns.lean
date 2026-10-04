import SerreMarkov.Mutations

/-! # Exhaustive coordinate patterns for the remaining arithmetic boundary

These are disjunctions of genuine integer coordinate conditions, not
classification assumptions. The partition holds for every integer six-tuple.
-/

namespace SerreMarkov.BoundaryPatterns

def HasZero (z : Six) : Prop := z.a=0 ∨ z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0
def HasUnit (z : Six) : Prop := |z.a|=1 ∨ |z.b|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.e|=1 ∨ |z.f|=1
def AtLeastTwo (z : Six) : Prop :=
  2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|
def SingleUnitTwo (z : Six) : Prop :=
  (|z.a|=1 ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.b|=1 ∧ 2≤|z.a| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.c|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.d|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.e| ∧ 2≤|z.f|) ∨
  (|z.e|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.f|) ∨
  (|z.f|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e|)
def AdjacentUnitPair (z : Six) : Prop :=
  (|z.a|=1 ∧ |z.d|=1) ∨ (|z.d|=1 ∧ |z.f|=1) ∨
  (|z.f|=1 ∧ |z.c|=1) ∨ (|z.c|=1 ∧ |z.a|=1)
def DiagonalAdjacentUnitPair (z : Six) : Prop :=
  (|z.b|=1 ∨ |z.e|=1) ∧ (|z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1)
def OppositeUnitPair (z : Six) : Prop := (|z.a|=1 ∧ |z.f|=1) ∨ (|z.c|=1 ∧ |z.d|=1)
def CrossingUnitPair (z : Six) : Prop := |z.b|=1 ∧ |z.e|=1
def DoubleUnit (z : Six) : Prop := AdjacentUnitPair z ∨ DiagonalAdjacentUnitPair z ∨
  OppositeUnitPair z ∨ CrossingUnitPair z

private theorem abs_atLeastTwo (x : ℤ) (hx : x≠0) (hu : |x|≠1) : 2≤|x| := by
  have hp := le_abs_self x
  have hn := neg_le_abs x
  omega

set_option maxHeartbeats 500000 in
theorem coordinate_pattern_partition (z : Six) :
    HasZero z ∨ AtLeastTwo z ∨ SingleUnitTwo z ∨ DoubleUnit z := by
  by_cases hzero : HasZero z
  · exact Or.inl hzero
  right
  simp only [HasZero,not_or] at hzero
  obtain ⟨ha0,hb0,hc0,hd0,he0,hf0⟩ := hzero
  by_cases hdouble : DoubleUnit z
  · exact Or.inr (Or.inr hdouble)
  by_cases hunit : HasUnit z
  · right
    left
    unfold HasUnit at hunit
    rcases hunit with ha | hb | hc | hd | he | hf
    · have hrest : |z.b|≠1 ∧ |z.c|≠1 ∧ |z.d|≠1 ∧ |z.e|≠1 ∧ |z.f|≠1 := by
        exact ⟨fun hb => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inl ha⟩)), fun hc => hdouble (Or.inl (Or.inr (Or.inr (Or.inr ⟨hc,ha⟩)))), fun hd => hdouble (Or.inl (Or.inl ⟨ha,hd⟩)), fun he => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inl ha⟩)), fun hf => hdouble (Or.inr (Or.inr (Or.inl (Or.inl ⟨ha,hf⟩))))⟩
      obtain ⟨hbu,hcu,hdu,heu,hfu⟩ := hrest
      have h : |z.a|=1 ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f| :=
        ⟨ha,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.e he0 heu,abs_atLeastTwo z.f hf0 hfu⟩
      exact Or.inl h
    · have hrest : |z.a|≠1 ∧ |z.c|≠1 ∧ |z.d|≠1 ∧ |z.e|≠1 ∧ |z.f|≠1 := by
        exact ⟨fun ha => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inl ha⟩)), fun hc => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inl hc)⟩)), fun hd => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inr (Or.inl hd))⟩)), fun he => hdouble (Or.inr (Or.inr (Or.inr ⟨hb,he⟩))), fun hf => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inr (Or.inr hf))⟩))⟩
      obtain ⟨hau,hcu,hdu,heu,hfu⟩ := hrest
      have h : |z.b|=1 ∧ 2≤|z.a| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f| :=
        ⟨hb,abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.e he0 heu,abs_atLeastTwo z.f hf0 hfu⟩
      exact Or.inr (Or.inl h)
    · have hrest : |z.a|≠1 ∧ |z.b|≠1 ∧ |z.d|≠1 ∧ |z.e|≠1 ∧ |z.f|≠1 := by
        exact ⟨fun ha => hdouble (Or.inl (Or.inr (Or.inr (Or.inr ⟨hc,ha⟩)))), fun hb => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inl hc)⟩)), fun hd => hdouble (Or.inr (Or.inr (Or.inl (Or.inr ⟨hc,hd⟩)))), fun he => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inl hc)⟩)), fun hf => hdouble (Or.inl (Or.inr (Or.inr (Or.inl ⟨hf,hc⟩))))⟩
      obtain ⟨hau,hbu,hdu,heu,hfu⟩ := hrest
      have h : |z.c|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.d| ∧ 2≤|z.e| ∧ 2≤|z.f| :=
        ⟨hc,abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.e he0 heu,abs_atLeastTwo z.f hf0 hfu⟩
      exact Or.inr (Or.inr (Or.inl h))
    · have hrest : |z.a|≠1 ∧ |z.b|≠1 ∧ |z.c|≠1 ∧ |z.e|≠1 ∧ |z.f|≠1 := by
        exact ⟨fun ha => hdouble (Or.inl (Or.inl ⟨ha,hd⟩)), fun hb => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inr (Or.inl hd))⟩)), fun hc => hdouble (Or.inr (Or.inr (Or.inl (Or.inr ⟨hc,hd⟩)))), fun he => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inr (Or.inl hd))⟩)), fun hf => hdouble (Or.inl (Or.inr (Or.inl ⟨hd,hf⟩)))⟩
      obtain ⟨hau,hbu,hcu,heu,hfu⟩ := hrest
      have h : |z.d|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.e| ∧ 2≤|z.f| :=
        ⟨hd,abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.e he0 heu,abs_atLeastTwo z.f hf0 hfu⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hrest : |z.a|≠1 ∧ |z.b|≠1 ∧ |z.c|≠1 ∧ |z.d|≠1 ∧ |z.f|≠1 := by
        exact ⟨fun ha => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inl ha⟩)), fun hb => hdouble (Or.inr (Or.inr (Or.inr ⟨hb,he⟩))), fun hc => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inl hc)⟩)), fun hd => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inr (Or.inl hd))⟩)), fun hf => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inr (Or.inr hf))⟩))⟩
      obtain ⟨hau,hbu,hcu,hdu,hfu⟩ := hrest
      have h : |z.e|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.f| :=
        ⟨he,abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.f hf0 hfu⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · have hrest : |z.a|≠1 ∧ |z.b|≠1 ∧ |z.c|≠1 ∧ |z.d|≠1 ∧ |z.e|≠1 := by
        exact ⟨fun ha => hdouble (Or.inr (Or.inr (Or.inl (Or.inl ⟨ha,hf⟩)))), fun hb => hdouble (Or.inr (Or.inl ⟨Or.inl hb, Or.inr (Or.inr (Or.inr hf))⟩)), fun hc => hdouble (Or.inl (Or.inr (Or.inr (Or.inl ⟨hf,hc⟩)))), fun hd => hdouble (Or.inl (Or.inr (Or.inl ⟨hd,hf⟩))), fun he => hdouble (Or.inr (Or.inl ⟨Or.inr he, Or.inr (Or.inr (Or.inr hf))⟩))⟩
      obtain ⟨hau,hbu,hcu,hdu,heu⟩ := hrest
      have h : |z.f|=1 ∧ 2≤|z.a| ∧ 2≤|z.b| ∧ 2≤|z.c| ∧ 2≤|z.d| ∧ 2≤|z.e| :=
        ⟨hf,abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.e he0 heu⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))
  · left
    simp only [HasUnit,not_or] at hunit
    obtain ⟨hau,hbu,hcu,hdu,heu,hfu⟩ := hunit
    exact ⟨abs_atLeastTwo z.a ha0 hau,abs_atLeastTwo z.b hb0 hbu,abs_atLeastTwo z.c hc0 hcu,abs_atLeastTwo z.d hd0 hdu,abs_atLeastTwo z.e he0 heu,abs_atLeastTwo z.f hf0 hfu⟩

theorem unit_nonzero_patterns (z : Six) (hzero : ¬HasZero z) (hunit : HasUnit z) :
    SingleUnitTwo z ∨ DoubleUnit z := by
  rcases coordinate_pattern_partition z with h | h | h | h
  · exact False.elim (hzero h)
  · unfold AtLeastTwo at h
    unfold HasUnit at hunit
    omega
  · exact Or.inl h
  · exact Or.inr h

end SerreMarkov.BoundaryPatterns
