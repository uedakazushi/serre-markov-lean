import SerreMarkov.Basis

/-!
# Coincident adjacent roots give a family representative

This is the purely integral, coordinate part of the negative-side reduction.
It does not assert that an arbitrary solution can be mutated to coincident roots.
-/

namespace SerreMarkov

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

theorem repeated_pair_q1 (a c e : ℤ) : q1 ⟨a, a, c, 2, e, e⟩ = c ^ 2 + 4 := by
  unfold q1; ring

theorem repeated_pair_q2 (a c e : ℤ) : q2 ⟨a, a, c, 2, e, e⟩ = 2 * c := by
  unfold q2; ring

theorem repeated_pair_reachable_family (a c e : ℤ)
    (hz : isSolution ⟨a, a, c, 2, e, e⟩) :
    ∃ x y : ℤ, Reachable ⟨a, a, c, 2, e, e⟩ (family x y) := by
  have hc2 : c ^ 2 = 4 := by
    have h := hz.1
    rw [repeated_pair_q1] at h
    linarith
  have hf : (c - 2) * (c + 2) = 0 := by nlinarith [hc2]
  rcases mul_eq_zero.mp hf with hp | hn
  · have hc : c = 2 := by linarith
    refine ⟨-a, e, [.s4], ?_⟩
    ext <;> simp [applyWord, step, eps4, family, hc]
  · have hc : c = -2 := by linarith
    refine ⟨-a, -e, [], ?_⟩
    ext <;> simp [applyWord, family, hc]

theorem tail_repeated_to_middle (a b d : ℤ) :
    applyWord ⟨a, b, b, d, d, 2⟩ [.i2, .i3] = ⟨b, b, a, 2, d, d⟩ := by
  ext <;> simp [applyWord, step, inv2, inv3] <;> ring

theorem tail_repeated_reachable_family (a b d : ℤ)
    (hz : isSolution ⟨a, b, b, d, d, 2⟩) :
    ∃ x y : ℤ, Reachable ⟨a, b, b, d, d, 2⟩ (family x y) := by
  have hr : Reachable ⟨a, b, b, d, d, 2⟩ ⟨b, b, a, 2, d, d⟩ :=
    ⟨[.i2, .i3], tail_repeated_to_middle a b d⟩
  obtain ⟨x, y, hxy⟩ := repeated_pair_reachable_family b a d
    (reachable_preserves_solution hr hz)
  exact ⟨x, y, reachable_trans hr hxy⟩

/-- Equality of the two columns means that the second and third basis vectors
have the same image in the nondegenerate quotient of the symmetric form. -/
theorem coincident_middle_columns_reachable_family (z : Six) (hz : isSolution z)
    (hcolumns : ∀ i : Fin 4, symmetricForm z i 1 = symmetricForm z i 2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hab := hcolumns 0
  have hd := hcolumns 1
  have hef := hcolumns 3
  simp [symmetricForm, gram] at hab hd hef
  have heq : z = ⟨z.a, z.a, z.c, 2, z.e, z.e⟩ := by
    ext <;> simp [hab, hd, hef]
  rw [heq] at hz ⊢
  exact repeated_pair_reachable_family z.a z.c z.e hz

/-- An equality between two symmetric-form columns, expressed in coordinates. -/
def PositiveRepeatedColumns (z : Six) : Prop :=
  (z.a = 2 ∧ z.b = z.d ∧ z.c = z.e) ∨
  (z.b = 2 ∧ z.a = z.d ∧ z.c = z.f) ∨
  (z.c = 2 ∧ z.a = z.e ∧ z.b = z.f) ∨
  (z.d = 2 ∧ z.a = z.b ∧ z.e = z.f) ∨
  (z.e = 2 ∧ z.a = z.c ∧ z.d = z.f) ∨
  (z.f = 2 ∧ z.b = z.c ∧ z.d = z.e)

/-- Opposite symmetric-form columns, expressed in coordinates. -/
def NegativeRepeatedColumns (z : Six) : Prop :=
  (z.a = -2 ∧ z.b = -z.d ∧ z.c = -z.e) ∨
  (z.b = -2 ∧ z.a = -z.d ∧ z.c = -z.f) ∨
  (z.c = -2 ∧ z.a = -z.e ∧ z.b = -z.f) ∨
  (z.d = -2 ∧ z.a = -z.b ∧ z.e = -z.f) ∨
  (z.e = -2 ∧ z.a = -z.c ∧ z.d = -z.f) ∨
  (z.f = -2 ∧ z.b = -z.c ∧ z.d = -z.e)

private theorem family_of_middle_word (z : Six) (hz : isSolution z)
    (a c e : ℤ) (word : List Generator)
    (hw : applyWord z word = ⟨a, a, c, 2, e, e⟩) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hr : Reachable z ⟨a, a, c, 2, e, e⟩ := ⟨word, hw⟩
  obtain ⟨x, y, hxy⟩ := repeated_pair_reachable_family a c e
    (reachable_preserves_solution hr hz)
  exact ⟨x, y, reachable_trans hr hxy⟩

theorem positive_repeated_columns_reachable_family (z : Six) (hz : isSolution z)
    (h : PositiveRepeatedColumns z) : ∃ x y : ℤ, Reachable z (family x y) := by
  rcases h with ⟨ha, hb, hc⟩ | ⟨hb, ha, hc⟩ | ⟨hc, ha, hb⟩ |
    ⟨hd, ha, he⟩ | ⟨he, ha, hd⟩ | ⟨hf, hb, hd⟩
  · apply family_of_middle_word z hz z.b z.f z.c [.m2, .m1]
    ext <;> simp [applyWord, step, mu1, mu2, ha, hb, hc] <;> ring
  · apply family_of_middle_word z hz z.a (z.a * z.c - z.e) z.c [.m1]
    ext <;> simp [applyWord, step, mu1, hb, ha, hc]
    ring
  · apply family_of_middle_word z hz z.a z.d z.b [.i3, .m1]
    ext <;> simp [applyWord, step, mu1, inv3, hc, ha, hb] <;> ring
  · apply family_of_middle_word z hz z.a z.c z.e []
    ext <;> simp [applyWord, hd, ha, he]
  · apply family_of_middle_word z hz z.a (z.a * z.d - z.b) z.d [.i3]
    ext <;> simp [applyWord, step, inv3, he, ha, hd] <;> ring
  · apply family_of_middle_word z hz z.b z.a z.d [.i2, .i3]
    ext <;> simp [applyWord, step, inv2, inv3, hf, hb, hd] <;> ring

theorem negative_repeated_columns_sign (z : Six) (h : NegativeRepeatedColumns z) :
    ∃ g : Generator, PositiveRepeatedColumns (step g z) := by
  rcases h with ⟨ha, hb, hc⟩ | ⟨hb, ha, hc⟩ | ⟨hc, ha, hb⟩ |
    ⟨hd, ha, he⟩ | ⟨he, ha, hd⟩ | ⟨hf, hb, hd⟩
  · refine ⟨.s1, Or.inl ?_⟩
    simp [step, eps1, ha, hb, hc]
  · refine ⟨.s1, Or.inr (Or.inl ?_)⟩
    simp [step, eps1, ha, hb, hc]
  · refine ⟨.s1, Or.inr (Or.inr (Or.inl ?_))⟩
    simp [step, eps1, ha, hb, hc]
  · refine ⟨.s2, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    simp [step, eps2, hd, ha, he]
  · refine ⟨.s2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    simp [step, eps2, he, ha, hd]
  · refine ⟨.s3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    simp [step, eps3, hf, hb, hd]

theorem negative_repeated_columns_reachable_family (z : Six) (hz : isSolution z)
    (h : NegativeRepeatedColumns z) : ∃ x y : ℤ, Reachable z (family x y) := by
  obtain ⟨g, hg⟩ := negative_repeated_columns_sign z h
  have hr : Reachable z (step g z) := ⟨[g], rfl⟩
  obtain ⟨x, y, hxy⟩ := positive_repeated_columns_reachable_family (step g z)
    (step_preserves_solution g z hz) hg
  exact ⟨x, y, reachable_trans hr hxy⟩

private theorem repeated_columns_coordinates (z : Six) (i j : Fin 4) (hij : i < j)
    (hcols : (∀ k, symmetricForm z k i = symmetricForm z k j) ∨
      (∀ k, symmetricForm z k i = -symmetricForm z k j)) :
    PositiveRepeatedColumns z ∨ NegativeRepeatedColumns z := by
  rcases hcols with hcols | hcols
  all_goals
    have h0 := hcols 0
    have h1 := hcols 1
    have h2 := hcols 2
    have h3 := hcols 3
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals
      simp [symmetricForm, gram] at h0 h1 h2 h3
      simp only [PositiveRepeatedColumns, NegativeRepeatedColumns]
      aesop

/-- Any two equal or opposite columns already admit an explicit mutation word
leading to the family. This is the complete algebraic repeated-root step. -/
theorem coincident_columns_reachable_family (z : Six) (hz : isSolution z)
    (i j : Fin 4) (hne : i ≠ j)
    (hcols : (∀ k, symmetricForm z k i = symmetricForm z k j) ∨
      (∀ k, symmetricForm z k i = -symmetricForm z k j)) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hcoord : PositiveRepeatedColumns z ∨ NegativeRepeatedColumns z := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact repeated_columns_coordinates z i j hij hcols
    · apply repeated_columns_coordinates z j i hji
      rcases hcols with hp | hn
      · exact Or.inl (fun k => (hp k).symm)
      · exact Or.inr (fun k => by have := hn k; linarith)
  rcases hcoord with hp | hn
  · exact positive_repeated_columns_reachable_family z hz hp
  · exact negative_repeated_columns_reachable_family z hz hn

end SerreMarkov
