import SerreMarkov.LatticeQuotient
import SerreMarkov.RootProductFormula
import SerreMarkov.PrimePowerFamilyCount
import SerreMarkov.FamilyUniqueness
import Mathlib.Data.Fintype.EquivFin

/-!
# Normalized family orbits inside actual forgetful-map fibers

The full fiber consists of mutation orbits of all integer solutions. The
normalized family candidates map into this actual fiber. Once normalized
family uniqueness is used, this map is injective; the modular root count is
therefore a lower bound on the full fiber. Its exact value counts only the
part of the fiber represented by normalized family solutions.
-/

namespace SerreMarkov.FamilyOrbitFibers

open FamilyFiberFinite
noncomputable section

def familyLatticeClass (m : ℕ) (y : ℤ) : Quotient latticeSetoid :=
  Quotient.mk latticeSetoid (family ((m : ℤ) - y) y)

/-- The actual fiber on mutation orbits of all integral solutions. -/
abbrev FullFiber (m : ℕ) (y : ℤ) :=
  {o : Quotient solutionSetoid // solutionForgetfulMap o = familyLatticeClass m y}

def candidateSolution (m : ℕ) (y : ℤ) (j : Candidate m y) : Solution :=
  ⟨family ((m : ℤ) - j.val.val) j.val.val, family_isSolution _ _⟩

def normalizedOrbit (m : ℕ) (j : NormalizedParameter m) : Quotient solutionSetoid :=
  Quotient.mk solutionSetoid ⟨family ((m : ℤ) - j.val) j.val, family_isSolution _ _⟩

def candidateOrbit (m : ℕ) (y : ℤ) (j : Candidate m y) : Quotient solutionSetoid :=
  normalizedOrbit m j.val

theorem candidateOrbit_in_fiber (m : ℕ) (y : ℤ) (j : Candidate m y) :
    solutionForgetfulMap (candidateOrbit m y j) = familyLatticeClass m y := by
  apply Quotient.sound
  obtain ⟨B, hdet, hB⟩ := j.property
  exact latticeEquivalent_symm (latticeEquivalent_of_congruence B hdet hB)

def candidateFiberMap (m : ℕ) (y : ℤ) : Candidate m y → FullFiber m y :=
  fun j => ⟨candidateOrbit m y j, candidateOrbit_in_fiber m y j⟩

theorem candidateOrbit_eq_iff_reachable (m : ℕ) (y : ℤ) (i j : Candidate m y) :
    candidateOrbit m y i = candidateOrbit m y j ↔
      Reachable (family ((m : ℤ) - i.val.val) i.val.val)
        (family ((m : ℤ) - j.val.val) j.val.val) := by
  constructor
  · exact Quotient.exact
  · intro hr
    exact Quotient.sound (show solutionSetoid.r (candidateSolution m y i)
      (candidateSolution m y j) from hr)

/-- The family part is an actual subset of the full solution-orbit fiber. -/
abbrev FamilyPart (m : ℕ) (y : ℤ) := Set.range (candidateFiberMap m y)

instance familyPart_finite (m : ℕ) (y : ℤ) : Finite (FamilyPart m y) :=
  Set.finite_range (candidateFiberMap m y)

/-- Membership in the restricted part means exactly that the actual
solution orbit has a normalized family representative. -/
theorem mem_familyPart_iff (m : ℕ) (y : ℤ) (o : FullFiber m y) :
    o ∈ Set.range (candidateFiberMap m y) ↔
      ∃ j : NormalizedParameter m, o.val = normalizedOrbit m j := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  · rintro ⟨j, hj⟩
    have hclass : Quotient.mk latticeSetoid (family ((m : ℤ)-j.val) j.val) =
        familyLatticeClass m y := by
      change solutionForgetfulMap (normalizedOrbit m j) = familyLatticeClass m y
      rw [← hj]
      exact o.property
    obtain ⟨B, hB⟩ := latticeEquivalent_symm (Quotient.exact hclass)
    have hdet : (B : Mat4).det = 1 ∨ (B : Mat4).det = -1 :=
      Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det (B : Mat4)).mp B.isUnit)
    let k : Candidate m y := ⟨j, ⟨(B : Mat4), hdet, hB⟩⟩
    refine ⟨k, Subtype.ext ?_⟩
    exact hj.symm

private theorem candidateFiberMap_injective_of_unique (m : ℕ) (y : ℤ)
    (hunique : ∀ (a b : ℤ), 0 ≤ a → 0 ≤ b → 2*a ≤ m → 2*b ≤ m →
      Reachable (family ((m : ℤ)-a) a) (family ((m : ℤ)-b) b) → a = b) :
    Function.Injective (candidateFiberMap m y) := by
  intro i j hij
  have hr := (candidateOrbit_eq_iff_reachable m y i j).mp (congrArg Subtype.val hij)
  have hb_i := normalized_parameter_bound m i.val
  have hb_j := normalized_parameter_bound m j.val
  have he := hunique i.val.val j.val.val hb_i.1 hb_j.1 hb_i.2 hb_j.2 hr
  apply Subtype.ext
  apply Fin.ext
  exact_mod_cast he

theorem candidateFiberMap_injective (m : ℕ) (hm : 0 < m) (y : ℤ) :
    Function.Injective (candidateFiberMap m y) := by
  apply candidateFiberMap_injective_of_unique
  intro a b ha hb hba hbb hr
  exact FamilyUniqueness.normalized_family_reachable_unique (m : ℤ) a b
    (by exact_mod_cast hm) ha hb hba hbb hr

/-- Every distinct normalized candidate gives a distinct actual solution
mutation orbit in the full forgetful-map fiber. -/
def candidateFiberEmbedding (m : ℕ) (hm : 0 < m) (y : ℤ) :
    Candidate m y ↪ FullFiber m y :=
  ⟨candidateFiberMap m y, candidateFiberMap_injective m hm y⟩

def familyPartEquivCandidate (m : ℕ) (hm : 0 < m) (y : ℤ) :
    FamilyPart m y ≃ Candidate m y :=
  (Equiv.ofInjective (candidateFiberMap m y) (candidateFiberMap_injective m hm y)).symm

theorem familyPart_card (m : ℕ) (hm : 0 < m) (y : ℤ) :
    Nat.card (FamilyPart m y) = Fintype.card (Candidate m y) := by
  rw [Nat.card_congr (familyPartEquivCandidate m hm y), Nat.card_eq_fintype_card]

/-- An exact root-sign quotient description of the family part of the
actual solution-orbit fiber, for odd positive moduli. -/
def oddRootSignQuotientEquivFamilyPart (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Quotient (rootSignSetoid m ((y : ZMod m)^2)) ≃ FamilyPart m y :=
  (oddRootSignQuotientEquivCandidate m hodd y).trans (familyPartEquivCandidate m hm y).symm

theorem odd_familyPart_twice_card (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    2 * Nat.card (FamilyPart m y) = Nat.card (Roots m ((y : ZMod m)^2)) +
      if (y : ZMod m)^2 = 0 then 1 else 0 := by
  rw [familyPart_card m hm y]
  exact odd_lattice_candidate_count m hodd y

/-- The explicit odd-modulus root-product count after quotienting by sign. -/
def oddFamilyCount (m : ℕ) (y : ℤ) : ℕ :=
  ((∏ p ∈ m.factorization.support,
    if y = 0 ∨ m.factorization p ≤ 2*y.natAbs.factorization p
    then p^(m.factorization p / 2) else 2*p^(y.natAbs.factorization p)) +
    if (y : ZMod m)^2 = 0 then 1 else 0) / 2

theorem odd_candidate_card (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Fintype.card (Candidate m y) = oddFamilyCount m y :=
  RootProductFormula.odd_lattice_candidate_formula m hm hodd y

theorem odd_familyPart_card (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Nat.card (FamilyPart m y) = oddFamilyCount m y := by
  rw [familyPart_card m hm y, odd_candidate_card m hm hodd y]

/-- The count injects into the full fiber, without assuming that every
solution orbit in the fiber has a normalized family representative. -/
def oddCountFiberEmbedding (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    Fin (oddFamilyCount m y) ↪ FullFiber m y :=
  (Fintype.equivFinOfCardEq (odd_candidate_card m hm hodd y)).symm.toEmbedding.trans
    (candidateFiberEmbedding m hm y)

theorem odd_solution_forgetful_fiber_injection (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ) :
    ∃ f : Fin (oddFamilyCount m y) →
      {o : Quotient solutionSetoid // solutionForgetfulMap o = familyLatticeClass m y},
      Function.Injective f :=
  ⟨oddCountFiberEmbedding m hm hodd y, (oddCountFiberEmbedding m hm hodd y).injective⟩

/-- For an odd prime square power, the sharp family contribution is
`(p^e+1)/2`, realized by actual distinct solution mutation orbits. -/
def primePowerZeroFiberEmbedding (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Fin ((p^e + 1) / 2) ↪ FullFiber (p^(2*e)) 0 :=
  (primePowerZeroCandidateEquivFin p e hp hodd).symm.toEmbedding.trans
    (candidateFiberEmbedding (p^(2*e)) (pow_pos hp.pos _) 0)

theorem primePower_zero_solution_forgetful_fiber_injection
    (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ∃ f : Fin ((p^e+1)/2) →
      {o : Quotient solutionSetoid // solutionForgetfulMap o =
        Quotient.mk latticeSetoid (family (p^(2*e)) 0)}, Function.Injective f := by
  let E := primePowerZeroFiberEmbedding p e hp hodd
  refine ⟨fun i => ⟨(E i).val, ?_⟩, ?_⟩
  · simpa [familyLatticeClass] using (E i).property
  · intro i j hij
    apply E.injective
    apply Subtype.ext
    exact congrArg (fun o => o.1) hij

def primePowerZeroFamilyPartEquivFin (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    FamilyPart (p^(2*e)) 0 ≃ Fin ((p^e+1)/2) :=
  (familyPartEquivCandidate (p^(2*e)) (pow_pos hp.pos _) 0).trans
    (primePowerZeroCandidateEquivFin p e hp hodd)

theorem primePower_zero_familyPart_card (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Nat.card (FamilyPart (p^(2*e)) 0) = (p^e+1)/2 := by
  rw [Nat.card_congr (primePowerZeroFamilyPartEquivFin p e hp hodd), Nat.card_fin]

/-- A numerical full-fiber lower bound is valid when the full fiber is
finite. The embedding statements above do not need this assumption. -/
theorem odd_fullFiber_card_lower_bound (m : ℕ) (hm : 0 < m) (hodd : Odd m) (y : ℤ)
    [Finite (FullFiber m y)] : oddFamilyCount m y ≤ Nat.card (FullFiber m y) := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    (oddCountFiberEmbedding m hm hodd y) (oddCountFiberEmbedding m hm hodd y).injective

theorem primePower_zero_fullFiber_card_lower_bound
    (p e : ℕ) (hp : p.Prime) (hodd : Odd p) [Finite (FullFiber (p^(2*e)) 0)] :
    (p^e+1)/2 ≤ Nat.card (FullFiber (p^(2*e)) 0) := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    (primePowerZeroFiberEmbedding p e hp hodd) (primePowerZeroFiberEmbedding p e hp hodd).injective

end
end SerreMarkov.FamilyOrbitFibers
