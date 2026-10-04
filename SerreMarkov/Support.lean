import SerreMarkov.Mutations

/-!
# A divisibility invariant of mutation orbits

Modulo any integer, the property that the nonzero upper triangular entries are
supported on one perfect matching is preserved by every mutation and sign
change. On the family `F(x,y)`, this property is exactly simultaneous divisibility
of `x` and `y`. No geometric classification theorem is used.
-/

namespace SerreMarkov

def MatchingSupport (m : ℤ) (z : Six) : Prop :=
  (m ∣ z.b ∧ m ∣ z.c ∧ m ∣ z.d ∧ m ∣ z.e) ∨
  (m ∣ z.a ∧ m ∣ z.c ∧ m ∣ z.d ∧ m ∣ z.f) ∨
  (m ∣ z.a ∧ m ∣ z.b ∧ m ∣ z.e ∧ m ∣ z.f)

private theorem mul_sub_dvd_left {m a b c : ℤ} (ha : m ∣ a) (hc : m ∣ c) :
    m ∣ a * b - c := dvd_sub (dvd_mul_of_dvd_left ha b) hc

private theorem mul_sub_dvd_right {m a b c : ℤ} (hb : m ∣ b) (hc : m ∣ c) :
    m ∣ a * b - c := dvd_sub (dvd_mul_of_dvd_right hb a) hc

theorem matchingSupport_mu1 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (mu1 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inl ⟨mul_sub_dvd_right hb hd, mul_sub_dvd_right hc he, hb, hc⟩
  · exact Or.inr (Or.inr ⟨ha, mul_sub_dvd_left ha hd, hc, hf⟩)
  · exact Or.inr (Or.inl ⟨ha, mul_sub_dvd_left ha he, hb, hf⟩)

theorem matchingSupport_inv1 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (inv1 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inl ⟨hd, he, mul_sub_dvd_right hd hb, mul_sub_dvd_right he hc⟩
  · exact Or.inr (Or.inr ⟨ha, hd, mul_sub_dvd_left ha hc, hf⟩)
  · exact Or.inr (Or.inl ⟨ha, he, mul_sub_dvd_left ha hb, hf⟩)

theorem matchingSupport_mu2 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (mu2 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inr (Or.inl ⟨mul_sub_dvd_right hd hb, hc, hd, he⟩)
  · exact Or.inl ⟨ha, hc, hd, mul_sub_dvd_left hd hf⟩
  · exact Or.inr (Or.inr ⟨mul_sub_dvd_left ha hb, ha, mul_sub_dvd_right he hf, he⟩)

theorem matchingSupport_inv2 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (inv2 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inr (Or.inl ⟨hb, hc, hd, mul_sub_dvd_left hd he⟩)
  · exact Or.inl ⟨mul_sub_dvd_right hd ha, hc, hd, hf⟩
  · exact Or.inr (Or.inr ⟨hb, mul_sub_dvd_left hb ha, hf, mul_sub_dvd_right hf he⟩)

theorem matchingSupport_mu3 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (mu3 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inl ⟨mul_sub_dvd_right hb hc, hb, mul_sub_dvd_right hd he, hd⟩
  · exact Or.inr (Or.inr ⟨ha, mul_sub_dvd_left hf hc, hd, hf⟩)
  · exact Or.inr (Or.inl ⟨ha, hb, mul_sub_dvd_left hf he, hf⟩)

theorem matchingSupport_inv3 {m : ℤ} (z : Six) (h : MatchingSupport m z) :
    MatchingSupport m (inv3 z) := by
  rcases h with ⟨hb, hc, hd, he⟩ | ⟨ha, hc, hd, hf⟩ | ⟨ha, hb, he, hf⟩
  · exact Or.inl ⟨hc, mul_sub_dvd_right hc hb, he, mul_sub_dvd_right he hd⟩
  · exact Or.inr (Or.inr ⟨ha, hc, mul_sub_dvd_left hf hd, hf⟩)
  · exact Or.inr (Or.inl ⟨ha, mul_sub_dvd_left hf hb, he, hf⟩)

theorem matchingSupport_eps1_iff (m : ℤ) (z : Six) :
    MatchingSupport m (eps1 z) ↔ MatchingSupport m z := by
  simp [MatchingSupport, eps1]
theorem matchingSupport_eps2_iff (m : ℤ) (z : Six) :
    MatchingSupport m (eps2 z) ↔ MatchingSupport m z := by
  simp [MatchingSupport, eps2]
theorem matchingSupport_eps3_iff (m : ℤ) (z : Six) :
    MatchingSupport m (eps3 z) ↔ MatchingSupport m z := by
  simp [MatchingSupport, eps3]
theorem matchingSupport_eps4_iff (m : ℤ) (z : Six) :
    MatchingSupport m (eps4 z) ↔ MatchingSupport m z := by
  simp [MatchingSupport, eps4]

theorem matchingSupport_step {m : ℤ} (g : Generator) (z : Six)
    (h : MatchingSupport m z) : MatchingSupport m (step g z) := by
  cases g with
  | m1 => exact matchingSupport_mu1 z h
  | m2 => exact matchingSupport_mu2 z h
  | m3 => exact matchingSupport_mu3 z h
  | i1 => exact matchingSupport_inv1 z h
  | i2 => exact matchingSupport_inv2 z h
  | i3 => exact matchingSupport_inv3 z h
  | s1 => exact (matchingSupport_eps1_iff m z).mpr h
  | s2 => exact (matchingSupport_eps2_iff m z).mpr h
  | s3 => exact (matchingSupport_eps3_iff m z).mpr h
  | s4 => exact (matchingSupport_eps4_iff m z).mpr h

theorem matchingSupport_word {m : ℤ} (word : List Generator) (z : Six)
    (h : MatchingSupport m z) : MatchingSupport m (applyWord z word) := by
  induction word generalizing z with
  | nil => exact h
  | cons g gs ih => exact ih (step g z) (matchingSupport_step g z h)

theorem matchingSupport_reachable {m : ℤ} {z z' : Six}
    (h : Reachable z z') (hz : MatchingSupport m z) : MatchingSupport m z' := by
  rcases h with ⟨word, hw⟩
  rw [← hw]
  exact matchingSupport_word word z hz

theorem matchingSupport_reachable_iff {m : ℤ} {z z' : Six}
    (h : Reachable z z') : MatchingSupport m z ↔ MatchingSupport m z' :=
  ⟨matchingSupport_reachable h, matchingSupport_reachable (reachable_symm h)⟩

theorem family_matchingSupport_iff (m x y : ℤ) :
    MatchingSupport m (family x y) ↔ m ∣ x ∧ m ∣ y := by
  simp only [MatchingSupport, family, dvd_neg]
  constructor
  · rintro (⟨hx, _, _, hy⟩ | ⟨hx, _, _, hy⟩ | ⟨hx, _, hy, _⟩)
    all_goals exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact Or.inr (Or.inr ⟨hx, hx, hy, hy⟩)

theorem family_divisibility_invariant {x y x' y' : ℤ}
    (h : Reachable (family x y) (family x' y')) (m : ℤ) :
    (m ∣ x ∧ m ∣ y) ↔ (m ∣ x' ∧ m ∣ y') := by
  rw [← family_matchingSupport_iff, ← family_matchingSupport_iff]
  exact matchingSupport_reachable_iff h

theorem family_not_reachable_of_divisibility (m x y x' y' : ℤ)
    (hx : m ∣ x) (hy : m ∣ y) (hy' : ¬m ∣ y') :
    ¬Reachable (family x y) (family x' y') := by
  intro h
  exact hy' ((family_divisibility_invariant h m).mp ⟨hx, hy⟩).2

theorem family_not_reachable_of_parameter_divisibility (d m y y' : ℤ)
    (hm : d ∣ m) (hy : d ∣ y) (hy' : ¬d ∣ y') :
    ¬Reachable (family (m - y) y) (family (m - y') y') :=
  family_not_reachable_of_divisibility d (m - y) y (m - y') y' (dvd_sub hm hy) hy hy'

theorem family_m_zero_not_reachable (m y : ℤ) (h : ¬m ∣ y) :
    ¬Reachable (family m 0) (family (m - y) y) :=
  family_not_reachable_of_divisibility m m 0 (m - y) y (dvd_refl m) (dvd_zero m) h

end SerreMarkov
