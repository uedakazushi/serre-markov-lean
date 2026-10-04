import SerreMarkov.IsometryNecessary
import SerreMarkov.InvolutionCount
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Finite normalized candidates in a family lattice fiber

These are candidates within the family `family (m-y) y`. No assertion about
the completeness of that family for all mutation orbits is used. For odd
moduli the previously proved lattice-isometry criterion identifies these
candidates with normalized square roots modulo `m`.
-/

namespace SerreMarkov.FamilyFiberFinite

open Matrix
noncomputable section

abbrev NormalizedParameter (m : ℕ) := Fin (m / 2 + 1)

theorem normalized_parameter_bound (m : ℕ) (j : NormalizedParameter m) :
    0 ≤ (j.val : ℤ) ∧ 2 * (j.val : ℤ) ≤ m := by
  constructor
  · exact Int.natCast_nonneg _
  · have hj : j.val ≤ m / 2 := Nat.le_of_lt_succ j.isLt
    have hp : j.val * 2 ≤ m := (Nat.le_div_iff_mul_le (by decide)).mp hj
    exact_mod_cast (by omega : 2 * j.val ≤ m)

/-- Integer parameters in the closed normalized interval are exactly the
`m/2+1` natural-number indices. -/
def boundedParameterEquiv (m : ℕ) :
    {y : ℤ // 0 ≤ y ∧ 2*y ≤ m} ≃ NormalizedParameter m where
  toFun y := ⟨y.val.toNat, by
    have hy : 2 * y.val.toNat ≤ m := by
      have hcast : (y.val.toNat : ℤ) = y.val := Int.toNat_of_nonneg y.property.1
      exact_mod_cast (show 2 * (y.val.toNat : ℤ) ≤ m by rw [hcast]; exact y.property.2)
    exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by decide)).mpr (by omega))⟩
  invFun j := ⟨j.val, normalized_parameter_bound m j⟩
  left_inv y := Subtype.ext (Int.toNat_of_nonneg y.property.1)
  right_inv j := by apply Fin.ext; simp

def SameFamilyLattice (m : ℕ) (y y' : ℤ) : Prop :=
  ∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
    Bᵀ * gram (family ((m : ℤ)-y) y) * B = gram (family ((m : ℤ)-y') y')

abbrev Candidate (m : ℕ) (y : ℤ) :=
  {j : NormalizedParameter m // SameFamilyLattice m y j.val}

instance candidate_fintype (m : ℕ) (y : ℤ) : Fintype (Candidate m y) := Fintype.ofFinite _

/-- The bound applies to every modulus, including even moduli. -/
theorem candidate_card_le (m : ℕ) (y : ℤ) :
    Fintype.card (Candidate m y) ≤ m / 2 + 1 := by
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun j : NormalizedParameter m => SameFamilyLattice m y j.val))

theorem integer_normalized_candidate_iff (m : ℕ) (y y' : ℤ) :
    (0 ≤ y' ∧ 2*y' ≤ m ∧ SameFamilyLattice m y y') ↔
      ∃ j : Candidate m y, (j.val.val : ℤ) = y' := by
  constructor
  · rintro ⟨h0, hb, hi⟩
    let j := boundedParameterEquiv m ⟨y', h0, hb⟩
    have hj : (j.val : ℤ) = y' := Int.toNat_of_nonneg h0
    exact ⟨⟨j, hj.symm ▸ hi⟩, hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(normalized_parameter_bound m j.val).1,
      (normalized_parameter_bound m j.val).2, j.property⟩

theorem normalized_integer_candidates_finite (m : ℕ) (y : ℤ) :
    Set.Finite {y' : ℤ | 0 ≤ y' ∧ 2*y' ≤ m ∧ SameFamilyLattice m y y'} := by
  have he : {y' : ℤ | 0 ≤ y' ∧ 2*y' ≤ m ∧ SameFamilyLattice m y y'} =
      Set.range (fun j : Candidate m y => (j.val.val : ℤ)) := by
    ext y'
    exact integer_normalized_candidate_iff m y y'
  rw [he]
  exact Set.finite_range _

abbrev SquareCandidate (m : ℕ) (c : ZMod m) :=
  {j : NormalizedParameter m // (j.val : ZMod m)^2 = c}

instance squareCandidate_fintype (m : ℕ) (c : ZMod m) : Fintype (SquareCandidate m c) :=
  Fintype.ofFinite _

def oddCandidateEquiv (m : ℕ) (hm : Odd m) (y : ℤ) :
    Candidate m y ≃ SquareCandidate m ((y : ZMod m)^2) where
  toFun j := ⟨j.val, by
    simpa only [Int.cast_natCast] using
      (family_isometry_iff_odd_square m hm y j.val.val).mp j.property⟩
  invFun j := ⟨j.val, by
    apply (family_isometry_iff_odd_square m hm y j.val.val).mpr
    simpa only [Int.cast_natCast] using j.property⟩
  left_inv j := rfl
  right_inv j := rfl

theorem odd_candidate_card_eq (m : ℕ) (hm : Odd m) (y : ℤ) :
    Fintype.card (Candidate m y) = Fintype.card (SquareCandidate m ((y : ZMod m)^2)) :=
  Fintype.card_congr (oddCandidateEquiv m hm y)

theorem normalized_parameter_nat_bound (m : ℕ) (j : NormalizedParameter m) :
    2*j.val ≤ m := by exact_mod_cast (normalized_parameter_bound m j).2

def negateFin {m : ℕ} [NeZero m] (j : Fin m) : Fin m :=
  ⟨(-(j.val : ZMod m)).val, ZMod.val_lt _⟩

@[simp] theorem negateFin_cast {m : ℕ} [NeZero m] (j : Fin m) :
    ((negateFin j).val : ZMod m) = -(j.val : ZMod m) := ZMod.natCast_zmod_val _

theorem negateFin_involutive {m : ℕ} [NeZero m] : Function.Involutive (@negateFin m _) := by
  intro j
  apply Fin.ext
  change (-((negateFin j).val : ZMod m)).val = j.val
  rw [negateFin_cast, neg_neg, ZMod.val_natCast_of_lt j.isLt]

theorem fin_cast_eq_zero_iff {m : ℕ} [NeZero m] (j : Fin m) :
    (j.val : ZMod m) = 0 ↔ j.val = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt j.isLt, ZMod.val_zero] using hv
  · intro h
    simp [h]

theorem negateFin_val {m : ℕ} [NeZero m] (j : Fin m) :
    (negateFin j).val = if j.val = 0 then 0 else m-j.val := by
  change (-(j.val : ZMod m)).val = _
  rw [ZMod.neg_val, ZMod.val_natCast_of_lt j.isLt]
  simp only [fin_cast_eq_zero_iff]

theorem le_negateFin_iff {m : ℕ} [NeZero m] (j : Fin m) :
    j ≤ negateFin j ↔ 2*j.val ≤ m := by
  change j.val ≤ (negateFin j).val ↔ _
  rw [negateFin_val]
  split_ifs <;> omega

def rootIndices (m : ℕ) (c : ZMod m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (j.val : ZMod m)^2 = c)

theorem rootIndices_negate {m : ℕ} [NeZero m] (c : ZMod m) (j : Fin m)
    (hj : j ∈ rootIndices m c) : negateFin j ∈ rootIndices m c := by
  have hs := (Finset.mem_filter.mp hj).2
  simpa only [rootIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    negateFin_cast, neg_sq] using hs

abbrev Roots (m : ℕ) (c : ZMod m) := {z : ZMod m // z^2 = c}

instance roots_fintype (m : ℕ) [NeZero m] (c : ZMod m) : Fintype (Roots m c) :=
  Fintype.ofFinite _

def rootIndicesEquivRoots (m : ℕ) [NeZero m] (c : ZMod m) :
    {j : Fin m // j ∈ rootIndices m c} ≃ Roots m c where
  toFun j := ⟨j.val.val, (Finset.mem_filter.mp j.property).2⟩
  invFun z := ⟨⟨z.val.val, ZMod.val_lt _⟩, by
    simp only [rootIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.natCast_zmod_val]
    exact z.property⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    exact ZMod.val_natCast_of_lt j.val.isLt
  right_inv z := Subtype.ext (ZMod.natCast_zmod_val _)

def representativeEquivSquareCandidate (m : ℕ) [NeZero m] (c : ZMod m) :
    {j : Fin m // j ∈ InvolutionCount.representatives (rootIndices m c) negateFin} ≃
      SquareCandidate m c where
  toFun j := by
    have hj := Finset.mem_filter.mp j.property
    have hb : 2*j.val.val ≤ m := (le_negateFin_iff j.val).mp hj.2
    exact ⟨⟨j.val.val, Nat.lt_succ_of_le
      ((Nat.le_div_iff_mul_le (by decide)).mpr (by omega))⟩,
      (Finset.mem_filter.mp hj.1).2⟩
  invFun j := by
    have hb := normalized_parameter_nat_bound m j.val
    have hpos := NeZero.pos m
    let k : Fin m := ⟨j.val.val, by omega⟩
    refine ⟨k, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩
    · exact (le_negateFin_iff k).mpr hb
  left_inv j := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Subtype.ext; apply Fin.ext; rfl

theorem negateFin_fixed_iff {m : ℕ} [NeZero m] (hm : Odd m) (j : Fin m) :
    negateFin j = j ↔ j.val = 0 := by
  constructor
  · intro h
    by_contra hn
    have hz : (j.val : ZMod m) ≠ 0 := fun h0 => hn ((fin_cast_eq_zero_iff j).mp h0)
    have he := congrArg (fun k : Fin m => (k.val : ZMod m)) h
    dsimp only at he
    rw [negateFin_cast] at he
    exact ZMod.ne_neg_self hm hz he.symm
  · intro h
    apply Fin.ext
    simp only [negateFin_val, h, ↓reduceIte]

theorem odd_fixed_root_count (m : ℕ) [NeZero m] (hm : Odd m) (c : ZMod m) :
    (InvolutionCount.fixedPoints (rootIndices m c) negateFin).card =
      if c = 0 then 1 else 0 := by
  have he : InvolutionCount.fixedPoints (rootIndices m c) negateFin =
      if c = 0 then {(0 : Fin m)} else ∅ := by
    by_cases hc : c = 0
    · rw [if_pos hc]
      subst c
      ext j
      simp only [InvolutionCount.fixedPoints, Finset.mem_filter,
        negateFin_fixed_iff hm, Finset.mem_singleton]
      constructor
      · intro hj; apply Fin.ext; simpa using hj.2
      · rintro rfl
        simp [rootIndices]
    · rw [if_neg hc]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have h0 := (negateFin_fixed_iff hm j).mp (Finset.mem_filter.mp hj).2
      have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      simp only [h0, Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      exact hc hs.symm
  rw [he]
  split_ifs <;> simp

/-- For odd moduli, only the zero root is fixed by sign. -/
theorem odd_square_candidate_count (m : ℕ) (hm : Odd m) (c : ZMod m) :
    2 * Fintype.card (SquareCandidate m c) =
      Nat.card (Roots m c) + if c = 0 then 1 else 0 := by
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  have hrep : (InvolutionCount.representatives (rootIndices m c) negateFin).card =
      Fintype.card (SquareCandidate m c) :=
    (Fintype.card_coe _).symm.trans (Fintype.card_congr (representativeEquivSquareCandidate m c))
  have hroot : (rootIndices m c).card = Fintype.card (Roots m c) :=
    (Fintype.card_coe _).symm.trans (Fintype.card_congr (rootIndicesEquivRoots m c))
  have hcount := InvolutionCount.twice_representative_card (rootIndices m c) negateFin
    negateFin_involutive (rootIndices_negate c)
  simpa only [hrep, hroot, odd_fixed_root_count m hm c, Nat.card_eq_fintype_card] using hcount

theorem odd_lattice_candidate_count (m : ℕ) (hm : Odd m) (y : ℤ) :
    2 * Fintype.card (Candidate m y) =
      Nat.card (Roots m ((y : ZMod m)^2)) +
        if (y : ZMod m)^2 = 0 then 1 else 0 := by
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  rw [odd_candidate_card_eq m hm y]
  exact odd_square_candidate_count m hm _

instance roots_linearOrder (m : ℕ) [NeZero m] (c : ZMod m) : LinearOrder (Roots m c) :=
  LinearOrder.lift' (fun z : Roots m c => z.val.val)
    (fun _ _ h => Subtype.ext (ZMod.val_injective m h))

def negateRoot (m : ℕ) (c : ZMod m) (z : Roots m c) : Roots m c :=
  ⟨-z.val, by simpa only [neg_sq] using z.property⟩

theorem negateRoot_involutive (m : ℕ) (c : ZMod m) :
    Function.Involutive (negateRoot m c) := fun z => Subtype.ext (neg_neg z.val)

def rootSignSetoid (m : ℕ) (c : ZMod m) : Setoid (Roots m c) :=
  InvolutionCount.orbitSetoid (negateRoot m c) (negateRoot_involutive m c)

theorem root_sign_related_iff (m : ℕ) (c : ZMod m) (x y : Roots m c) :
    (rootSignSetoid m c).r x y ↔ x.val = y.val ∨ x.val = -y.val := by
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h.symm)
    · right
      have he : y.val = -x.val := congrArg Subtype.val h
      simpa only [neg_neg] using (congrArg Neg.neg he).symm
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h.symm)
    · right
      apply Subtype.ext
      simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem normalized_parameter_lt_modulus (m : ℕ) [NeZero m] (j : NormalizedParameter m) :
    j.val < m := by
  have hb := normalized_parameter_nat_bound m j
  have hpos := NeZero.pos m
  omega

def rootRepresentativeEquivSquareCandidate (m : ℕ) [NeZero m] (c : ZMod m) :
    {z : Roots m c // z ≤ negateRoot m c z} ≃ SquareCandidate m c where
  toFun z := by
    let j : Fin m := ⟨z.val.val.val, ZMod.val_lt _⟩
    have hl : j ≤ negateFin j := by
      change z.val.val.val ≤ (-((z.val.val.val : ZMod m))).val
      rw [ZMod.natCast_zmod_val]
      exact z.property
    have hb := (le_negateFin_iff j).mp hl
    refine ⟨⟨j.val, Nat.lt_succ_of_le
      ((Nat.le_div_iff_mul_le (by decide)).mpr (by omega))⟩, ?_⟩
    change (z.val.val.val : ZMod m)^2 = c
    rw [ZMod.natCast_zmod_val]
    exact z.val.property
  invFun j := by
    let z : Roots m c := ⟨j.val.val, j.property⟩
    let k : Fin m := ⟨j.val.val, normalized_parameter_lt_modulus m j.val⟩
    refine ⟨z, ?_⟩
    change (j.val.val : ZMod m).val ≤ (-(j.val.val : ZMod m)).val
    rw [ZMod.val_natCast_of_lt k.isLt]
    exact (le_negateFin_iff k).mpr (normalized_parameter_nat_bound m j.val)
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact ZMod.natCast_zmod_val _
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (normalized_parameter_lt_modulus m j.val)

/-- Square roots modulo sign are in bijection with the normalized interval,
for every positive modulus. -/
def rootSignQuotientEquivSquareCandidate (m : ℕ) [NeZero m] (c : ZMod m) :
    Quotient (rootSignSetoid m c) ≃ SquareCandidate m c :=
  (InvolutionCount.quotientEquivRepresentatives (negateRoot m c) (negateRoot_involutive m c)).trans
    (rootRepresentativeEquivSquareCandidate m c)

/-- For odd moduli this bijection counts precisely the normalized family
parameters whose lattices are isometric to the given family lattice. -/
def oddRootSignQuotientEquivCandidate (m : ℕ) (hm : Odd m) (y : ℤ) :
    Quotient (rootSignSetoid m ((y : ZMod m)^2)) ≃ Candidate m y := by
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  exact (rootSignQuotientEquivSquareCandidate m _).trans (oddCandidateEquiv m hm y).symm

theorem odd_candidate_card_eq_root_sign_quotient (m : ℕ) (hm : Odd m) (y : ℤ) :
    Fintype.card (Candidate m y) =
      Nat.card (Quotient (rootSignSetoid m ((y : ZMod m)^2))) := by
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  letI : Fintype (Quotient (rootSignSetoid m ((y : ZMod m)^2))) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (oddRootSignQuotientEquivCandidate m hm y)).symm

end
end SerreMarkov.FamilyFiberFinite
