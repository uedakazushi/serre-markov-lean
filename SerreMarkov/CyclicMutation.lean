import SerreMarkov.NegativeDescent

/-! # A height-preserving cyclic permutation by actual mutations

Three forward braids cancel their polynomial correction terms exactly.
Their iterations transport each of the four adjacent edges to the first edge.
-/

namespace SerreMarkov.CyclicMutation

open NegativeDescent

def cycle (z : Six) : Six := ⟨z.d,z.e,z.a,z.f,z.b,z.c⟩

def cyclePower (z : Six) : ℕ → Six
  | 0 => z
  | n+1 => cycle (cyclePower z n)

def cycleWord : ℕ → List Generator
  | 0 => []
  | n+1 => cycleWord n ++ [.m1,.m2,.m3]

theorem applyWord_cycle (z : Six) : applyWord z [.m1,.m2,.m3] = cycle z := by
  ext <;> simp [applyWord,step,mu1,mu2,mu3,cycle] <;> ring

theorem applyWord_cycleWord (z : Six) (n : ℕ) :
    applyWord z (cycleWord n) = cyclePower z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cycleWord,applyWord_append,ih,applyWord_cycle]; rfl

theorem reachable_cycle (z : Six) : Reachable z (cycle z) :=
  ⟨[.m1,.m2,.m3],applyWord_cycle z⟩

theorem reachable_cyclePower (z : Six) (n : ℕ) : Reachable z (cyclePower z n) :=
  ⟨cycleWord n,applyWord_cycleWord z n⟩

@[simp] theorem l1_cycle (z : Six) : l1 (cycle z)=l1 z := by dsimp [l1,cycle]; omega

@[simp] theorem l1_cyclePower (z : Six) (n : ℕ) : l1 (cyclePower z n)=l1 z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [cyclePower,l1_cycle] using ih

theorem cyclePower_solution (z : Six) (hz : isSolution z) (n : ℕ) :
    isSolution (cyclePower z n) := reachable_preserves_solution (reachable_cyclePower z n) hz

@[simp] theorem cycle_marker (z : Six) : negativeMarker (cycle z)=negativeMarker z := by
  dsimp [negativeMarker,cycle]; ring

@[simp] theorem cyclePower_marker (z : Six) (n : ℕ) :
    negativeMarker (cyclePower z n)=negativeMarker z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [cyclePower,cycle_marker] using ih

theorem cyclePower_negative (z : Six) (hneg : IntrinsicSigns.thirdMinorSum z < 0) (n : ℕ) :
    IntrinsicSigns.thirdMinorSum (cyclePower z n) < 0 := by
  change negativeMarker (cyclePower z n) < 0
  rw [cyclePower_marker]
  exact hneg

@[simp] theorem cyclePower_first_one (z : Six) : (cyclePower z 1).a=z.d := rfl
@[simp] theorem cyclePower_first_two (z : Six) : (cyclePower z 2).a=z.f := rfl
@[simp] theorem cyclePower_first_three (z : Six) : (cyclePower z 3).a=z.c := rfl
@[simp] theorem cyclePower_four (z : Six) : cyclePower z 4=z := by cases z; rfl

theorem cyclePower_coordinates (P : ℤ → Prop) (z : Six) (n : ℕ)
    (hp : P z.a ∧ P z.b ∧ P z.c ∧ P z.d ∧ P z.e ∧ P z.f) :
    P (cyclePower z n).a ∧ P (cyclePower z n).b ∧ P (cyclePower z n).c ∧
      P (cyclePower z n).d ∧ P (cyclePower z n).e ∧ P (cyclePower z n).f := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := ih
    exact ⟨hd,he,ha,hf,hb,hc⟩

theorem word_descent_transfer (z : Six) (n : ℕ) (word : List Generator)
    (h : l1 (applyWord (cyclePower z n) word) < l1 (cyclePower z n)) :
    l1 (applyWord z (cycleWord n ++ word)) < l1 z := by
  rw [applyWord_append,applyWord_cycleWord]
  simpa only [l1_cyclePower] using h

theorem exists_word_descent_transfer (z : Six) (n : ℕ)
    (h : ∃ word : List Generator,
      l1 (applyWord (cyclePower z n) word) < l1 (cyclePower z n)) :
    ∃ word : List Generator, l1 (applyWord z word) < l1 z := by
  obtain ⟨word,hw⟩ := h
  exact ⟨cycleWord n ++ word,word_descent_transfer z n word hw⟩

theorem family_or_drop_transfer (z : Six) (n : ℕ)
    (h : (∃ x y : ℤ, Reachable (cyclePower z n) (family x y)) ∨
      ∃ word : List Generator, l1 (applyWord (cyclePower z n) word) < l1 (cyclePower z n)) :
    (∃ x y : ℤ, Reachable z (family x y)) ∨
      ∃ word : List Generator, l1 (applyWord z word) < l1 z := by
  rcases h with ⟨x,y,hr⟩ | h
  · exact Or.inl ⟨x,y,reachable_trans (reachable_cyclePower z n) hr⟩
  · exact Or.inr (exists_word_descent_transfer z n h)

end SerreMarkov.CyclicMutation
