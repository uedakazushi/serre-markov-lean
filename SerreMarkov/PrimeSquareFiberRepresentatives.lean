import SerreMarkov.NegativeFamilyOrbitFibers
import SerreMarkov.PrimePowerRoots

/-! # Explicit complete representatives over an odd prime square power

For `m=p^(2e)`, the actual full forgetful-map fiber is parameterized directly
by `j ↦ family (m-j*p^e) (j*p^e)`, with `0≤j≤(p^e-1)/2`.
The construction uses square-zero divisibility, normalized-family uniqueness,
and the completed negative classification. It does not choose a bijection
from a cardinality equality. The case `e=0` is included.
-/
namespace SerreMarkov.PrimeSquareFiberRepresentatives
open FamilyFiberFinite FamilyOrbitFibers NegativeFamilyOrbitFibers
noncomputable section

private theorem half_index_bound (q : ℕ) (hq : Odd q) (j : Fin ((q+1)/2)) :
    2*j.val≤q := by
  obtain ⟨k,hk⟩ := hq
  have hj := j.isLt
  omega

theorem index_bound (p e : ℕ) (hodd : Odd p) (j : Fin ((p^e+1)/2)) :
    j.val≤(p^e-1)/2 := by
  obtain ⟨k,hk⟩ := (show Odd (p^e) from hodd.pow)
  have hj := j.isLt
  omega

private theorem parameter_bound (p e : ℕ) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) : 2*(j.val*p^e)≤p^(2*e) := by
  calc
    2*(j.val*p^e)=(2*j.val)*p^e := by ring
    _ ≤ p^e*p^e := Nat.mul_le_mul_right _ (half_index_bound _ ((show Odd (p^e) from hodd.pow)) j)
    _ = p^(2*e) := (squarePower_eq_mul p e).symm

/-- The directly specified normalized parameter `j*p^e`. -/
def parameter (p e : ℕ) (hodd : Odd p) (j : Fin ((p^e+1)/2)) :
    NormalizedParameter (p^(2*e)) :=
  ⟨j.val*p^e, Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by decide)).mpr
    (by simpa [Nat.mul_comm] using parameter_bound p e hodd j))⟩

@[simp] theorem parameter_val (p e : ℕ) (hodd : Odd p) (j : Fin ((p^e+1)/2)) :
    (parameter p e hodd j).val=j.val*p^e := rfl

private theorem parameter_square_zero (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) :
    (((parameter p e hodd j).val : ℕ) : ZMod (p^(2*e)))^2=0 := by
  rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff]
  apply (prime_square_power_dvd_square p e _ hp).mpr
  exact dvd_mul_left _ _

/-- The same-lattice candidate is constructed from its actual square-zero
parameter, rather than from a finite cardinality theorem. -/
def explicitCandidate (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) : Candidate (p^(2*e)) 0 := by
  refine ⟨parameter p e hodd j,?_⟩
  apply (family_isometry_iff_odd_square (p^(2*e)) hodd.pow 0 _).mpr
  simpa using parameter_square_zero p e hp hodd j

@[simp] theorem explicitCandidate_val (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) : (explicitCandidate p e hp hodd j).val.val=j.val*p^e := rfl

/-- Every normalized candidate parameter is a multiple of `p^e`. -/
theorem candidate_parameter_divisible (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (c : Candidate (p^(2*e)) 0) : p^e∣c.val.val := by
  have h := (family_isometry_iff_odd_square (p^(2*e)) hodd.pow 0 c.val.val).mp c.property
  have hs : ((c.val.val^2 : ℕ) : ZMod (p^(2*e)))=0 := by
    rw [Nat.cast_pow]
    simpa using h
  rw [ZMod.natCast_eq_zero_iff] at hs
  exact (prime_square_power_dvd_square p e _ hp).mp hs

private theorem candidate_quotient_bound (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (c : Candidate (p^(2*e)) 0) : c.val.val/(p^e)<(p^e+1)/2 := by
  have hq : 0<p^e := pow_pos hp.pos _
  have hd := candidate_parameter_divisible p e hp hodd c
  have hb := normalized_parameter_nat_bound (p^(2*e)) c.val
  have hb' : (2*(c.val.val/(p^e)))*p^e≤p^e*p^e := by
    calc
      (2*(c.val.val/(p^e)))*p^e=2*((c.val.val/(p^e))*p^e) := by ring
      _ = 2*c.val.val := by rw [Nat.div_mul_cancel hd]
      _ ≤ p^e*p^e := by simpa [squarePower_eq_mul] using hb
  have ht := Nat.le_of_mul_le_mul_right hb' hq
  obtain ⟨k,hk⟩ := (show Odd (p^e) from hodd.pow)
  omega

/-- The inverse index is the normalized parameter divided by `p^e`. -/
def candidateIndex (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (c : Candidate (p^(2*e)) 0) : Fin ((p^e+1)/2) :=
  ⟨c.val.val/(p^e), candidate_quotient_bound p e hp hodd c⟩

@[simp] theorem candidateIndex_val (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (c : Candidate (p^(2*e)) 0) :
    (candidateIndex p e hp hodd c).val=c.val.val/(p^e) := rfl

/-- A formula-specified equivalence with the normalized family candidates. -/
def explicitCandidateEquiv (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Fin ((p^e+1)/2) ≃ Candidate (p^(2*e)) 0 where
  toFun := explicitCandidate p e hp hodd
  invFun := candidateIndex p e hp hodd
  left_inv j := by
    apply Fin.ext
    change (j.val*p^e)/(p^e)=j.val
    exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
  right_inv c := by
    apply Subtype.ext
    apply Fin.ext
    change (c.val.val/(p^e))*p^e=c.val.val
    exact Nat.div_mul_cancel (candidate_parameter_divisible p e hp hodd c)

/-- The manuscript's explicitly listed actual solution. -/
def representative (p e : ℕ) (j : Fin ((p^e+1)/2)) : Six :=
  family (((p^(2*e) : ℕ) : ℤ)-((j.val*p^e : ℕ) : ℤ)) ((j.val*p^e : ℕ) : ℤ)

/-- This actual orbit lies in the full forgetful-map fiber of `family m 0`. -/
def explicitFiberMap (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Fin ((p^e+1)/2) → FullFiber (p^(2*e)) 0 :=
  fun j => candidateFiberMap (p^(2*e)) 0 (explicitCandidate p e hp hodd j)

@[simp] theorem explicitFiberMap_orbit (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) :
    (explicitFiberMap p e hp hodd j).val=
      Quotient.mk solutionSetoid ⟨representative p e j, family_isSolution _ _⟩ := rfl

theorem explicitFiberMap_injective (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Function.Injective (explicitFiberMap p e hp hodd) :=
  (candidateFiberMap_injective (p^(2*e)) (pow_pos hp.pos _) 0).comp
    (explicitCandidateEquiv p e hp hodd).injective

/-- Completeness concerns all solution mutation orbits in this fiber. -/
theorem explicitFiberMap_surjective (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Function.Surjective (explicitFiberMap p e hp hodd) :=
  (candidateFiberMap_surjective (p^(2*e)) (pow_pos hp.pos _) 0).comp
    (explicitCandidateEquiv p e hp hodd).surjective

/-- A complete, duplicate-free list whose forward map is exactly the
manuscript's `j*p^e` representative formula. -/
def explicitFullFiberEquiv (p e : ℕ) (hp : p.Prime) (hodd : Odd p) :
    Fin ((p^e+1)/2) ≃ FullFiber (p^(2*e)) 0 :=
  Equiv.ofBijective (explicitFiberMap p e hp hodd)
    ⟨explicitFiberMap_injective p e hp hodd, explicitFiberMap_surjective p e hp hodd⟩

@[simp] theorem explicitFullFiberEquiv_orbit (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j : Fin ((p^e+1)/2)) :
    (explicitFullFiberEquiv p e hp hodd j).val=
      Quotient.mk solutionSetoid ⟨representative p e j,family_isSolution _ _⟩ := rfl

theorem fullFiber_unique_representative (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (o : FullFiber (p^(2*e)) 0) :
    ∃! j : Fin ((p^e+1)/2), o=explicitFiberMap p e hp hodd j := by
  obtain ⟨j,hj⟩ := explicitFiberMap_surjective p e hp hodd o
  refine ⟨j,hj.symm,?_⟩
  intro k hk
  exact explicitFiberMap_injective p e hp hodd (hk.symm.trans hj.symm)

/-- The displayed solutions have distinct actual mutation orbits. -/
theorem representatives_reachable_iff (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (j k : Fin ((p^e+1)/2)) :
    Reachable (representative p e j) (representative p e k) ↔ j=k := by
  constructor
  · intro hr
    apply explicitFiberMap_injective p e hp hodd
    apply Subtype.ext
    rw [explicitFiberMap_orbit,explicitFiberMap_orbit]
    exact Quotient.sound hr
  · rintro rfl
    exact reachable_refl _

/-- Every actual integer solution isometric to the source family reaches
exactly one of the explicitly printed representatives. -/
theorem solution_unique_representative (p e : ℕ) (hp : p.Prime) (hodd : Odd p)
    (z : Six) (hz : isSolution z)
    (hl : LatticeEquivalent z (family (p^(2*e)) 0)) :
    ∃! j : Fin ((p^e+1)/2), Reachable z (representative p e j) := by
  have hi : solutionForgetfulMap (Quotient.mk solutionSetoid ⟨z,hz⟩)=
      familyLatticeClass (p^(2*e)) 0 := by
    change Quotient.mk latticeSetoid z=
      Quotient.mk latticeSetoid (family (((p^(2*e) : ℕ) : ℤ)-0) 0)
    apply Quotient.sound
    simpa using hl
  let o : FullFiber (p^(2*e)) 0 := ⟨Quotient.mk solutionSetoid ⟨z,hz⟩,hi⟩
  obtain ⟨j,hj,hunique⟩ := fullFiber_unique_representative p e hp hodd o
  have hjval : Quotient.mk solutionSetoid ⟨z,hz⟩=
      Quotient.mk solutionSetoid ⟨representative p e j,family_isSolution _ _⟩ := by
    simpa only [o,explicitFiberMap_orbit] using congrArg Subtype.val hj
  refine ⟨j,Quotient.exact hjval,?_⟩
  intro k hk
  apply hunique k
  apply Subtype.ext
  rw [explicitFiberMap_orbit]
  exact Quotient.sound hk

end
end SerreMarkov.PrimeSquareFiberRepresentatives
