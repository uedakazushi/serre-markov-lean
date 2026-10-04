import SerreMarkov.PositiveChamber

/-! # Exact polynomial comparisons for short positive braid words

Every comparison below is derived from actual integral braid words. This
module supplies necessary inequalities for a short-word terminal point; it
does not assert the remaining universal terminal-height or small-edge bound.
-/

namespace SerreMarkov.PositiveShortWord

open NegativeDescent PositiveChamber

def coordinateSum (z : Six) : ℤ := z.a+z.b+z.c+z.d+z.e+z.f

def heightPolynomial (z : Six) (word : List Generator) : ℤ :=
  coordinateSum (applyWord z word)-coordinateSum z

def ShortTerminal (z : Six) (n : ℕ) : Prop :=
  ∀ word ∈ braidWords n, l1 z ≤ l1 (applyWord z word)

theorem braidMoves_isBraid {g : Generator} (hg : g ∈ braidMoves) : IsBraid g := by
  cases g <;> simp_all [braidMoves,IsBraid]

theorem integerL1_eq_coordinateSum (z : Six) (hz : Chamber z) :
    integerL1 z = coordinateSum z := by
  simpa [coordinateSum] using braid_word_integerL1_eq_sum z hz [] (by simp)

/-- Absolute heights become exact polynomial heights throughout the chamber. -/
theorem noDrop_iff_heightPolynomial (z : Six) (hz : Chamber z) (word : List Generator)
    (hword : ∀ g ∈ word, IsBraid g) :
    l1 z ≤ l1 (applyWord z word) ↔ 0 ≤ heightPolynomial z word := by
  have hw := applyWord_preserves_chamber z hz word hword
  have hcast : l1 z ≤ l1 (applyWord z word) ↔
      integerL1 z ≤ integerL1 (applyWord z word) := by
    rw [integerL1_cast,integerL1_cast]
    exact_mod_cast Iff.rfl
  rw [hcast,integerL1_eq_coordinateSum z hz,integerL1_eq_coordinateSum _ hw]
  dsimp [heightPolynomial]
  omega

theorem shortTerminal_iff_polynomial (z : Six) (hz : Chamber z) (n : ℕ) :
    ShortTerminal z n ↔ ∀ word ∈ braidWords n, 0 ≤ heightPolynomial z word := by
  constructor <;> intro h word hmem
  · exact (noDrop_iff_heightPolynomial z hz word
      (fun g hg => braidMoves_isBraid ((mem_braidWords_iff n word).mp hmem |>.2 g hg))).mp (h word hmem)
  · exact (noDrop_iff_heightPolynomial z hz word
      (fun g hg => braidMoves_isBraid ((mem_braidWords_iff n word).mp hmem |>.2 g hg))).mpr (h word hmem)

theorem shortTerminal_mono {z : Six} {m n : ℕ} (hmn : m ≤ n)
    (h : ShortTerminal z n) : ShortTerminal z m := by
  intro word hw
  apply h word
  rw [mem_braidWords_iff] at hw ⊢
  exact ⟨hw.1.trans hmn,hw.2⟩

/-- The six one-letter and two cyclic two-letter comparisons. -/
def BalanceInequalities (z : Six) : Prop :=
  2*(z.d+z.e) ≤ z.a*(z.b+z.c) ∧
  2*(z.b+z.c) ≤ z.a*(z.d+z.e) ∧
  2*(z.b+z.f) ≤ z.d*(z.a+z.e) ∧
  2*(z.a+z.e) ≤ z.d*(z.b+z.f) ∧
  2*(z.c+z.e) ≤ z.f*(z.b+z.d) ∧
  2*(z.b+z.d) ≤ z.f*(z.c+z.e) ∧
  2*(z.e+z.f) ≤ z.c*(z.a+z.b) ∧
  2*(z.a+z.b) ≤ z.c*(z.e+z.f)

theorem shortTerminal_balances (z : Six) (hz : Chamber z) (h : ShortTerminal z 2) :
    BalanceInequalities z := by
  have hp := (shortTerminal_iff_polynomial z hz 2).mp h
  have H (word : List Generator) (hlen : word.length ≤ 2)
      (hmoves : ∀ g ∈ word, g ∈ braidMoves) : 0 ≤ heightPolynomial z word :=
    hp word ((mem_braidWords_iff 2 word).mpr ⟨hlen,hmoves⟩)
  have h1 := H [.m1] (by decide) (by simp [braidMoves])
  have h2 := H [.i1] (by decide) (by simp [braidMoves])
  have h3 := H [.m2] (by decide) (by simp [braidMoves])
  have h4 := H [.i2] (by decide) (by simp [braidMoves])
  have h5 := H [.m3] (by decide) (by simp [braidMoves])
  have h6 := H [.i3] (by decide) (by simp [braidMoves])
  have h7 := H [.m1,.m2] (by decide) (by simp [braidMoves])
  have h8 := H [.i3,.i2] (by decide) (by simp [braidMoves])
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3] at h1 h2 h3 h4 h5 h6 h7 h8
  dsimp [BalanceInequalities]
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  constructor
  · nlinarith only [h3]
  constructor
  · nlinarith only [h4]
  constructor
  · nlinarith only [h5]
  constructor
  · nlinarith only [h6]
  constructor
  · nlinarith only [h7]
  · nlinarith only [h8]

/-- A three-letter cyclic braid permutes the six coordinates exactly. -/
theorem cyclic_word (z : Six) :
    applyWord z [.m1,.m2,.m3] = ⟨z.d,z.e,z.a,z.f,z.b,z.c⟩ := by
  ext <;> dsimp [applyWord,step,mu1,mu2,mu3] <;> ring

theorem cyclic_word_height (z : Six) :
    l1 (applyWord z [.m1,.m2,.m3]) = l1 z := by
  rw [cyclic_word]
  dsimp [l1]
  omega

end SerreMarkov.PositiveShortWord
