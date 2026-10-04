import SerreMarkov.DegenerateClassification
import SerreMarkov.NegativeClassification
import SerreMarkov.PositiveRepresentatives

/-! # Joint uniqueness of the manuscript's canonical representatives

The three kinds of representatives give distinct actual mutation orbits.
This is unconditional uniqueness, including the cross-kind comparisons.
Surjectivity for all solutions is not asserted in this module.
-/

namespace SerreMarkov.CanonicalRepresentatives

open NegativeClassification

inductive Canonical where
  | degenerate (k : ℕ)
  | negative (p : {p : ℤ × ℤ // NormalizedNegativePair p})
  | positive (r : Fin 5)

def representative : Canonical → Six
  | .degenerate k => family (k : ℤ) (-(k : ℤ))
  | .negative p => family p.val.1 p.val.2
  | .positive r => PositiveExamples.representative r

def kind : Canonical → IntrinsicKind
  | .degenerate _ => .degenerate
  | .negative _ => .negative
  | .positive _ => .positive

theorem representative_isSolution (c : Canonical) : isSolution (representative c) := by
  cases c with
  | degenerate k => exact family_isSolution _ _
  | negative p => exact family_isSolution _ _
  | positive r => exact PositiveExamples.representative_isSolution r

theorem representative_kind (c : Canonical) : intrinsicKind (representative c) = kind c := by
  cases c with
  | degenerate k =>
    apply (intrinsicKind_degenerate_iff _).mpr
    exact (family_cube_eq_zero_iff _ _).mpr (by ring)
  | negative p =>
    apply (intrinsicKind_negative_iff _ (family_isSolution _ _)).mpr
    have h := FamilyIntrinsic.family_negative (p.val.1+p.val.2) p.val.2 p.property.2.2
    simpa only [add_sub_cancel_right] using h
  | positive r => exact PositiveExamples.representative_intrinsicKind r

theorem representatives_reachable_iff (c d : Canonical) :
    Reachable (representative c) (representative d) ↔ c = d := by
  constructor
  · intro hr
    have hk := reachable_intrinsicKind (representative_isSolution c) hr
    rw [representative_kind, representative_kind] at hk
    cases c <;> cases d <;> try {simp [kind] at hk}
    · rename_i k l
      have hkl : (k : ℤ) = l :=
        (degenerate_family_reachable_iff (Nat.cast_nonneg k) (Nat.cast_nonneg l)).mp hr
      have h : k = l := by exact_mod_cast hkl
      exact congrArg Canonical.degenerate h
    · rename_i p q
      have hpq := normalized_negative_pair_injective p.val q.val p.property q.property hr
      exact congrArg Canonical.negative (Subtype.ext hpq)
    · rename_i r s
      exact congrArg Canonical.positive ((PositiveExamples.representatives_reachable_iff r s).mp hr)
  · rintro rfl
    exact reachable_refl _

theorem canonical_target_unique (z : Six) (c d : Canonical)
    (hc : Reachable z (representative c)) (hd : Reachable z (representative d)) : c = d :=
  (representatives_reachable_iff c d).mp (reachable_trans (reachable_symm hc) hd)

theorem unique_canonical_of_exists (z : Six)
    (h : ∃ c : Canonical, Reachable z (representative c)) :
    ∃! c : Canonical, Reachable z (representative c) := by
  obtain ⟨c,hc⟩ := h
  exact ⟨c,hc,fun d hd => canonical_target_unique z d c hd hc⟩

def representativeSolution (c : Canonical) : Solution :=
  ⟨representative c, representative_isSolution c⟩

def orbitMap (c : Canonical) : Quotient solutionSetoid :=
  Quotient.mk solutionSetoid (representativeSolution c)

theorem orbitMap_injective : Function.Injective orbitMap := by
  intro c d h
  exact (representatives_reachable_iff c d).mp (Quotient.exact h)

def orbitEmbedding : Canonical ↪ Quotient solutionSetoid :=
  ⟨orbitMap, orbitMap_injective⟩

end SerreMarkov.CanonicalRepresentatives
