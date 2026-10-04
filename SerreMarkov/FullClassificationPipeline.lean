import SerreMarkov.CanonicalRepresentatives
import SerreMarkov.NegativeClassificationFull
import SerreMarkov.NegativeFiberFiniteGeneral
import SerreMarkov.DegenerateFibers

/-! # Consequences of positive completeness

This module isolates the final assembly step. Negative and degenerate
classification are already unconditional. Its positive completeness argument
is explicit, and is to be supplied by the terminal chamber arithmetic.
-/

namespace SerreMarkov.FullClassificationPipeline
open CanonicalRepresentatives

def PositiveCompleteness : Prop :=
  ∀ z : Six, isSolution z → 0<IntrinsicSigns.thirdMinorSum z →
    ∃ r : Fin 5, Reachable z (PositiveExamples.representative r)

theorem canonical_classification_of_positive (hpos : PositiveCompleteness)
    (z : Six) (hz : isSolution z) :
    ∃! c : Canonical, Reachable z (representative c) := by
  apply unique_canonical_of_exists
  cases hk : intrinsicKind z with
  | degenerate =>
    obtain ⟨k,hk0,hr⟩ := degenerate_classification_surjective z hz
      ((intrinsicKind_degenerate_iff z).mp hk)
    refine ⟨.degenerate k.toNat,?_⟩
    simpa only [representative,Int.toNat_of_nonneg hk0] using hr
  | positive =>
    obtain ⟨r,hr⟩ := hpos z hz ((intrinsicKind_positive_iff z hz).mp hk)
    exact ⟨.positive r,hr⟩
  | negative =>
    obtain ⟨p,hp,hr⟩ := NegativeClassificationFull.negative_normalized_existence z hz
      ((intrinsicKind_negative_iff z hz).mp hk)
    exact ⟨.negative ⟨p,hp⟩,hr⟩

theorem orbitMap_surjective_of_positive (hpos : PositiveCompleteness) :
    Function.Surjective orbitMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  obtain ⟨c,hr,_⟩ := canonical_classification_of_positive hpos z.val z.property
  exact ⟨c,Quotient.sound (reachable_symm hr)⟩

noncomputable def canonicalOrbitEquivOfPositive (hpos : PositiveCompleteness) :
    Canonical ≃ Quotient solutionSetoid :=
  Equiv.ofBijective orbitMap ⟨orbitMap_injective,orbitMap_surjective_of_positive hpos⟩

theorem positive_latticeEquivalent_iff_reachable_of_positive
    (hpos : PositiveCompleteness) (z w : Six) (hz : isSolution z) (hw : isSolution w)
    (hpz : 0<IntrinsicSigns.thirdMinorSum z) (hpw : 0<IntrinsicSigns.thirdMinorSum w) :
    LatticeEquivalent z w ↔ Reachable z w := by
  constructor
  · intro h
    obtain ⟨r,hr⟩ := hpos z hz hpz
    obtain ⟨s,hs⟩ := hpos w hw hpw
    have hrs : r=s := (PositiveExamples.representatives_latticeEquivalent_iff r s).mp
      (latticeEquivalent_trans (latticeEquivalent_symm (reachable_latticeEquivalent hr))
        (latticeEquivalent_trans h (reachable_latticeEquivalent hs)))
    subst s
    exact reachable_trans hr (reachable_symm hs)
  · exact reachable_latticeEquivalent

theorem positive_fiber_subsingleton_of_positive (hpos : PositiveCompleteness)
    (z : Six) (hz : isSolution z) (hpz : 0<IntrinsicSigns.thirdMinorSum z) :
    Subsingleton (DegenerateFibers.SolutionFiber z) := by
  have hunique : ∀ q : Quotient solutionSetoid,
      solutionForgetfulMap q=Quotient.mk latticeSetoid z →
      q=Quotient.mk solutionSetoid ⟨z,hz⟩ := by
    intro q
    refine Quotient.inductionOn q ?_
    intro w heq
    have hl : LatticeEquivalent w.val z := Quotient.exact heq
    have hwkind := latticeEquivalent_intrinsicKind w.property hl
    have hwpos : 0<IntrinsicSigns.thirdMinorSum w.val :=
      (intrinsicKind_positive_iff w.val w.property).mp
        (hwkind.trans ((intrinsicKind_positive_iff z hz).mpr hpz))
    exact Quotient.sound ((positive_latticeEquivalent_iff_reachable_of_positive
      hpos w.val z w.property hz hwpos hpz).mp hl)
  exact ⟨fun o p => Subtype.ext ((hunique o.val o.property).trans
    (hunique p.val p.property).symm)⟩

theorem positive_fiber_card_of_positive (hpos : PositiveCompleteness)
    (z : Six) (hz : isSolution z) (hpz : 0<IntrinsicSigns.thirdMinorSum z) :
    Nat.card (DegenerateFibers.SolutionFiber z)=1 := by
  letI := positive_fiber_subsingleton_of_positive hpos z hz hpz
  letI : Nonempty (DegenerateFibers.SolutionFiber z) :=
    ⟨DegenerateFibers.referenceFiber z hz⟩
  exact Nat.card_unique

theorem solution_fiber_finite_of_positive (hpos : PositiveCompleteness)
    (z : Six) (hz : isSolution z) : Finite (DegenerateFibers.SolutionFiber z) := by
  cases hk : intrinsicKind z with
  | degenerate =>
    exact DegenerateFibers.degenerate_fiber_finite z hz
      ((intrinsicKind_degenerate_iff z).mp hk)
  | positive =>
    letI := positive_fiber_subsingleton_of_positive hpos z hz
      ((intrinsicKind_positive_iff z hz).mp hk)
    infer_instance
  | negative =>
    exact NegativeFiberFiniteGeneral.negative_solution_fiber_finite z hz
      ((intrinsicKind_negative_iff z hz).mp hk)

theorem all_forgetful_fibers_finite_of_positive (hpos : PositiveCompleteness)
    (L : Quotient latticeSetoid) :
    Finite {o : Quotient solutionSetoid // solutionForgetfulMap o=L} := by
  classical
  by_cases h : Nonempty {o : Quotient solutionSetoid // solutionForgetfulMap o=L}
  · obtain ⟨o⟩ := h
    have hfinite : ∀ q : Quotient solutionSetoid, solutionForgetfulMap q=L →
        Finite {o : Quotient solutionSetoid // solutionForgetfulMap o=L} := by
      intro q
      refine Quotient.inductionOn q ?_
      intro z heq
      rw [←heq]
      exact solution_fiber_finite_of_positive hpos z.val z.property
    exact hfinite o.val o.property
  · letI : IsEmpty {o : Quotient solutionSetoid // solutionForgetfulMap o=L} :=
      ⟨fun o => h ⟨o⟩⟩
    infer_instance

end SerreMarkov.FullClassificationPipeline
