import SerreMarkov.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# The rational kernel flag of a regular rank-four Serre lattice

The Jordan flag is obtained from strict growth of kernels, without invoking a
Jordan normal form algorithm or assuming geometric realization.
-/

namespace SerreMarkov

open Matrix Module

abbrev RatMat4 := Matrix (Fin 4) (Fin 4) ℚ
abbrev RatVec4 := Fin 4 → ℚ

def integerToRatMatrix : Mat4 →+* RatMat4 := (Int.castRingHom ℚ).mapMatrix

theorem integerToRatMatrix_injective : Function.Injective integerToRatMatrix := by
  intro A B h
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun M : RatMat4 => M i j) h
  change (A i j : ℚ) = (B i j : ℚ) at hh
  exact_mod_cast hh

noncomputable def rationalN (z : Six) : Module.End ℚ RatVec4 :=
  (integerToRatMatrix (shiftedSerre z)).toLin'

theorem rationalN_fourth (z : Six) (hz : isSolution z) : rationalN z ^ 4 = 0 := by
  rw [rationalN, ← Matrix.toLin'_pow, ← map_pow,
    (solution_iff_fourth_power_zero z).mp hz, map_zero, map_zero]

theorem rationalN_cube_ne_zero (z : Six) (h : shiftedSerre z ^ 3 ≠ 0) :
    rationalN z ^ 3 ≠ 0 := by
  intro hf
  have hm : integerToRatMatrix (shiftedSerre z ^ 3) = integerToRatMatrix 0 := by
    apply Matrix.toLin'.injective
    simpa [map_pow, rationalN] using hf
  exact h (integerToRatMatrix_injective hm)

/-- Nilpotence of index four forces all four kernel inclusions to be strict. -/
theorem regular_kernel_strict (f : Module.End ℚ RatVec4)
    (h4 : f ^ 4 = 0) (h3 : f ^ 3 ≠ 0) (k : ℕ) (hk : k < 4) :
    LinearMap.ker (f ^ k) < LinearMap.ker (f ^ (k + 1)) := by
  apply lt_of_le_of_ne
  · rw [pow_succ']
    exact LinearMap.ker_le_ker_comp (f ^ k) f
  · intro heq
    have hto4 : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ 4) := by
      have ht := Module.End.ker_pow_constant heq (4-k)
      simpa [Nat.add_sub_of_le (by omega : k ≤ 4)] using ht
    have hto3 : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ 3) := by
      have ht := Module.End.ker_pow_constant heq (3-k)
      simpa [Nat.add_sub_of_le (by omega : k ≤ 3)] using ht
    apply h3
    apply LinearMap.ker_eq_top.mp
    rw [← hto3, hto4, h4]
    simp

theorem regular_kernel_finranks (f : Module.End ℚ RatVec4)
    (h4 : f ^ 4 = 0) (h3 : f ^ 3 ≠ 0) :
    Module.finrank ℚ (LinearMap.ker f) = 1 ∧
      Module.finrank ℚ (LinearMap.ker (f ^ 2)) = 2 ∧
      Module.finrank ℚ (LinearMap.ker (f ^ 3)) = 3 := by
  have h01 := Submodule.finrank_lt_finrank_of_lt (regular_kernel_strict f h4 h3 0 (by omega))
  have h12 := Submodule.finrank_lt_finrank_of_lt (regular_kernel_strict f h4 h3 1 (by omega))
  have h23 := Submodule.finrank_lt_finrank_of_lt (regular_kernel_strict f h4 h3 2 (by omega))
  have h34 := Submodule.finrank_lt_finrank_of_lt (regular_kernel_strict f h4 h3 3 (by omega))
  let d : ℕ → ℕ := fun k => Module.finrank ℚ (LinearMap.ker (f ^ k))
  change d 0 < d 1 at h01
  change d 1 < d 2 at h12
  change d 2 < d 3 at h23
  change d 3 < d 4 at h34
  have hker0 : LinearMap.ker (f ^ 0) = ⊥ := by simp [Module.End.one_eq_id]
  have hker4 : LinearMap.ker (f ^ 4) = ⊤ := by rw [h4]; simp
  have hd0 : d 0 = 0 := by
    have hh := congrArg (fun U : Submodule ℚ RatVec4 => Module.finrank ℚ U) hker0
    exact hh.trans (by simp)
  have hd4 : d 4 = 4 := by
    have hh := congrArg (fun U : Submodule ℚ RatVec4 => Module.finrank ℚ U) hker4
    exact hh.trans (by simp [RatVec4])
  have hd1 : d 1 = 1 := by omega
  have hd2 : d 2 = 2 := by omega
  have hd3 : d 3 = 3 := by omega
  have hker1 : LinearMap.ker (f ^ 1) = LinearMap.ker f := by rw [pow_one]
  have hdim1 := congrArg (fun U : Submodule ℚ RatVec4 => Module.finrank ℚ U) hker1
  exact ⟨hdim1.symm.trans hd1, hd2, hd3⟩

theorem regular_range_finranks (f : Module.End ℚ RatVec4)
    (h4 : f ^ 4 = 0) (h3 : f ^ 3 ≠ 0) :
    Module.finrank ℚ (LinearMap.range f) = 3 ∧
      Module.finrank ℚ (LinearMap.range (f ^ 2)) = 2 ∧
      Module.finrank ℚ (LinearMap.range (f ^ 3)) = 1 := by
  obtain ⟨h1, h2, h3'⟩ := regular_kernel_finranks f h4 h3
  have hr1 := LinearMap.finrank_range_add_finrank_ker f
  have hr2 := LinearMap.finrank_range_add_finrank_ker (f ^ 2)
  have hr3 := LinearMap.finrank_range_add_finrank_ker (f ^ 3)
  rw [h1] at hr1
  rw [h2] at hr2
  rw [h3'] at hr3
  have hv : Module.finrank ℚ RatVec4 = 4 := by simp [RatVec4, Module.finrank_pi]
  rw [hv] at hr1 hr2 hr3
  omega

theorem regular_image_kernel_flag (f : Module.End ℚ RatVec4)
    (h4 : f ^ 4 = 0) (h3 : f ^ 3 ≠ 0) :
    LinearMap.range (f ^ 3) = LinearMap.ker f ∧
      LinearMap.range (f ^ 2) = LinearMap.ker (f ^ 2) ∧
      LinearMap.range f = LinearMap.ker (f ^ 3) := by
  obtain ⟨hk1, hk2, hk3⟩ := regular_kernel_finranks f h4 h3
  obtain ⟨hr1, hr2, hr3⟩ := regular_range_finranks f h4 h3
  have hi1 : LinearMap.range (f ^ 3) ≤ LinearMap.ker f := by
    rw [LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp, ← pow_succ']
    exact h4
  have hi2 : LinearMap.range (f ^ 2) ≤ LinearMap.ker (f ^ 2) := by
    rw [LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp, ← pow_add]
    exact h4
  have hi3 : LinearMap.range f ≤ LinearMap.ker (f ^ 3) := by
    rw [LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp, ← pow_succ]
    exact h4
  exact ⟨Submodule.eq_of_le_of_finrank_eq hi1 (hr3.trans hk1.symm),
    Submodule.eq_of_le_of_finrank_eq hi2 (hr2.trans hk2.symm),
    Submodule.eq_of_le_of_finrank_eq hi3 (hr1.trans hk3.symm)⟩

theorem solution_regular_flag (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    Module.finrank ℚ (LinearMap.ker (rationalN z)) = 1 ∧
      Module.finrank ℚ (LinearMap.ker (rationalN z ^ 2)) = 2 ∧
      Module.finrank ℚ (LinearMap.ker (rationalN z ^ 3)) = 3 :=
  regular_kernel_finranks _ (rationalN_fourth z hz) (rationalN_cube_ne_zero z hreg)

theorem solution_regular_ranks (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    Module.finrank ℚ (LinearMap.range (rationalN z)) = 3 ∧
      Module.finrank ℚ (LinearMap.range (rationalN z ^ 2)) = 2 ∧
      Module.finrank ℚ (LinearMap.range (rationalN z ^ 3)) = 1 :=
  regular_range_finranks _ (rationalN_fourth z hz) (rationalN_cube_ne_zero z hreg)

theorem solution_regular_image_flag (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    LinearMap.range (rationalN z ^ 3) = LinearMap.ker (rationalN z) ∧
      LinearMap.range (rationalN z ^ 2) = LinearMap.ker (rationalN z ^ 2) ∧
      LinearMap.range (rationalN z) = LinearMap.ker (rationalN z ^ 3) :=
  regular_image_kernel_flag _ (rationalN_fourth z hz) (rationalN_cube_ne_zero z hreg)

abbrev IntVec4 := Fin 4 → ℤ

open scoped Matrix

theorem gram_mulVec_injective (z : Six) : Function.Injective (gram z *ᵥ ·) := by
  intro x y h
  have hh := congrArg (fun v : IntVec4 => gramInverse z *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, inverse_mul_gram, Matrix.one_mulVec] using hh

theorem symmetric_radical_iff (z : Six) (x : IntVec4) :
    symmetricForm z *ᵥ x = 0 ↔ shiftedSerre z *ᵥ x = 0 := by
  rw [symmetricForm_eq, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    apply gram_mulVec_injective z
    simpa using h
  · intro h
    simp [h]

/-- Kernels of integral matrices are saturated in the ambient free lattice. -/
theorem integral_kernel_saturated (A : Mat4) (x : IntVec4) (n : ℤ)
    (hn : n ≠ 0) (h : A *ᵥ (n • x) = 0) : A *ᵥ x = 0 := by
  rw [Matrix.mulVec_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hn

theorem kernel_power_saturated (z : Six) (k : ℕ) (x : IntVec4) (n : ℤ)
    (hn : n ≠ 0) (h : (shiftedSerre z ^ k) *ᵥ (n • x) = 0) :
    (shiftedSerre z ^ k) *ᵥ x = 0 :=
  integral_kernel_saturated _ x n hn h

/-- An integral matrix kernel admits an integral basis. -/
theorem integral_kernel_has_basis (A : Mat4) :
    Nonempty (Σ n : ℕ, Basis (Fin n) ℤ (LinearMap.ker A.toLin')) := by
  exact ⟨Module.basisOfFiniteTypeTorsionFree'⟩

/-- The kernel quotient is free, hence the kernel is a direct factor. -/
theorem integral_kernel_quotient_free (A : Mat4) :
    Module.Free ℤ (IntVec4 ⧸ LinearMap.ker A.toLin') := by
  haveI : Module.Free ℤ (LinearMap.range A.toLin') := inferInstance
  exact Module.Free.of_equiv A.toLin'.quotKerEquivRange.symm

theorem integral_range_has_section (A : Mat4) :
    ∃ i : LinearMap.range A.toLin' →ₗ[ℤ] IntVec4,
      A.toLin'.rangeRestrict ∘ₗ i = LinearMap.id := by
  haveI : Module.Free ℤ (LinearMap.range A.toLin') := inferInstance
  haveI : Module.Projective ℤ (LinearMap.range A.toLin') := inferInstance
  exact (Module.Projective.iff_split_of_projective A.toLin'.rangeRestrict
    A.toLin'.surjective_rangeRestrict).mp inferInstance

/-- The integral Euler pairing on coordinate vectors. -/
def chiVec (z : Six) (x y : IntVec4) : ℤ := x ⬝ᵥ (gram z *ᵥ y)

theorem chiVec_add_left (z : Six) (x y v : IntVec4) :
    chiVec z (x+y) v = chiVec z x v + chiVec z y v := by
  simp [chiVec, add_dotProduct]

theorem chiVec_add_right (z : Six) (x y v : IntVec4) :
    chiVec z x (y+v) = chiVec z x y + chiVec z x v := by
  simp [chiVec, Matrix.mulVec_add, dotProduct_add]

theorem chiVec_sub_right (z : Six) (x y v : IntVec4) :
    chiVec z x (y-v) = chiVec z x y - chiVec z x v := by
  simp [chiVec, Matrix.mulVec_sub, dotProduct_sub]

theorem chiVec_neg_right (z : Six) (x y : IntVec4) :
    chiVec z x (-y) = -chiVec z x y := by
  simp [chiVec, Matrix.mulVec_neg, dotProduct_neg]

theorem chiVec_smul_right (z : Six) (x y : IntVec4) (k : ℤ) :
    chiVec z x (k • y) = k * chiVec z x y := by
  simp only [chiVec, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem chiVec_serre (z : Six) (x y : IntVec4) :
    chiVec z x (serre z *ᵥ y) = chiVec z y x := by
  simp only [chiVec]
  rw [Matrix.mulVec_mulVec, gram_mul_serre, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, dotProduct_comm]

theorem chiVec_serre_isometry (z : Six) (x y : IntVec4) :
    chiVec z (serre z *ᵥ x) (serre z *ᵥ y) = chiVec z x y := by
  simp only [chiVec]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, serre_isometry]

theorem serre_kernel_eigen (z : Six) (p : IntVec4)
    (hp : shiftedSerre z *ᵥ p = 0) : serre z *ᵥ p = -p := by
  have hh : serre z *ᵥ p + p = 0 := by
    simpa [shiftedSerre, Matrix.add_mulVec] using hp
  exact eq_neg_of_add_eq_zero_left hh

theorem serre_flag_second (z : Six) (p l : IntVec4) (k : ℤ)
    (hl : shiftedSerre z *ᵥ l = -(k • p)) :
    serre z *ᵥ l = -l - k • p := by
  have hh : serre z *ᵥ l + l = -(k • p) := by
    simpa [shiftedSerre, Matrix.add_mulVec] using hl
  have ht := eq_sub_of_add_eq hh
  calc
    serre z *ᵥ l = -(k • p) - l := ht
    _ = -l - k • p := by abel

theorem flag_rank_left (z : Six) (p x : IntVec4)
    (hp : shiftedSerre z *ᵥ p = 0) : chiVec z p x = -chiVec z x p := by
  have h := chiVec_serre z x p
  rw [serre_kernel_eigen z p hp, chiVec_neg_right] at h
  exact h.symm

theorem flag_degree_left (z : Six) (p l x : IntVec4) (k : ℤ)
    (hl : shiftedSerre z *ᵥ l = -(k • p)) :
    chiVec z l x = -chiVec z x l - k * chiVec z x p := by
  have h := chiVec_serre z x l
  rw [serre_flag_second z p l k hl, chiVec_sub_right, chiVec_neg_right,
    chiVec_smul_right] at h
  exact h.symm

theorem flag_rank_serre (z : Six) (p x : IntVec4)
    (hp : shiftedSerre z *ᵥ p = 0) :
    chiVec z (serre z *ᵥ x) p = -chiVec z x p := by
  have h := chiVec_serre_isometry z x p
  rw [serre_kernel_eigen z p hp, chiVec_neg_right] at h
  linarith

theorem flag_degree_serre (z : Six) (p l x : IntVec4) (k : ℤ)
    (hp : shiftedSerre z *ᵥ p = 0) (hl : shiftedSerre z *ᵥ l = -(k • p)) :
    chiVec z (serre z *ᵥ x) l = -chiVec z x l + k * chiVec z x p := by
  have h := chiVec_serre_isometry z x l
  rw [serre_flag_second z p l k hl, chiVec_sub_right, chiVec_neg_right,
    chiVec_smul_right, flag_rank_serre z p x hp] at h
  linarith

theorem flag_rank_shifted (z : Six) (p x : IntVec4)
    (hp : shiftedSerre z *ᵥ p = 0) : chiVec z (shiftedSerre z *ᵥ x) p = 0 := by
  simp [shiftedSerre, Matrix.add_mulVec, chiVec_add_left, flag_rank_serre z p x hp]

theorem flag_degree_shifted (z : Six) (p l x : IntVec4) (k : ℤ)
    (hp : shiftedSerre z *ᵥ p = 0) (hl : shiftedSerre z *ᵥ l = -(k • p)) :
    chiVec z (shiftedSerre z *ᵥ x) l = k * chiVec z x p := by
  simp [shiftedSerre, Matrix.add_mulVec, chiVec_add_left,
    flag_degree_serre z p l x k hp hl]

theorem flag_degree_second_power (z : Six) (p l x : IntVec4) (k : ℤ)
    (hp : shiftedSerre z *ᵥ p = 0) (hl : shiftedSerre z *ᵥ l = -(k • p)) :
    chiVec z ((shiftedSerre z ^ 2) *ᵥ x) l = 0 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, flag_degree_shifted z p l _ k hp hl,
    flag_rank_shifted z p x hp, mul_zero]

open scoped TensorProduct
open TensorProduct

noncomputable def rationalCoordinateEquiv : ℚ ⊗[ℤ] IntVec4 ≃ₗ[ℚ] RatVec4 :=
  TensorProduct.piScalarRight ℤ ℚ ℚ (Fin 4)

theorem rationalCoordinate_intertwine (A : Mat4) :
    rationalCoordinateEquiv.toLinearMap.comp (AlgebraTensorModule.lTensor ℚ ℚ A.toLin') =
      (integerToRatMatrix A).toLin'.comp rationalCoordinateEquiv.toLinearMap := by
  ext i j
  simp [LinearMap.comp_apply, rationalCoordinateEquiv, integerToRatMatrix,
    Matrix.mulVec, dotProduct, zsmul_eq_mul, Pi.single_apply]

noncomputable def rationalKernelEquiv (A : Mat4) :
    ℚ ⊗[ℤ] (LinearMap.ker A.toLin') ≃ₗ[ℚ]
      LinearMap.ker (integerToRatMatrix A).toLin' := by
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let e := rationalCoordinateEquiv
  let f := AlgebraTensorModule.lTensor ℚ ℚ A.toLin'
  have hmap : (LinearMap.ker f).map e.toLinearMap =
      LinearMap.ker (integerToRatMatrix A).toLin' := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      change (integerToRatMatrix A).toLin' (e v) = 0
      have h := congrArg (fun F => F v) (rationalCoordinate_intertwine A)
      change e (f v) = (integerToRatMatrix A).toLin' (e v) at h
      rw [← h, show f v = 0 from hv, map_zero]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      change f (e.symm x) = 0
      apply e.injective
      have h := congrArg (fun F => F (e.symm x)) (rationalCoordinate_intertwine A)
      change e (f (e.symm x)) = (integerToRatMatrix A).toLin' (e (e.symm x)) at h
      rw [h, e.apply_symm_apply, show (integerToRatMatrix A).toLin' x = 0 from hx,
        map_zero]
  exact (LinearMap.tensorKerEquiv ℚ ℚ A.toLin').trans
    (e.ofSubmodules _ _ hmap)

theorem integral_kernel_finrank_rat (A : Mat4) :
    Module.finrank ℤ (LinearMap.ker A.toLin') =
      Module.finrank ℚ (LinearMap.ker (integerToRatMatrix A).toLin') := by
  rw [← (rationalKernelEquiv A).finrank_eq, Module.finrank_baseChange]

/-- Rationalization preserves the rank of every integral kernel in the flag. -/
theorem integral_kernel_power_finrank_rat (z : Six) (k : ℕ) :
    Module.finrank ℤ (LinearMap.ker (shiftedSerre z ^ k).toLin') =
      Module.finrank ℚ (LinearMap.ker (rationalN z ^ k)) := by
  have h := integral_kernel_finrank_rat (shiftedSerre z ^ k)
  have hh : (integerToRatMatrix (shiftedSerre z ^ k)).toLin' = rationalN z ^ k := by
    simp [map_pow, rationalN]
  exact h.trans (congrArg (fun U : Submodule ℚ RatVec4 => Module.finrank ℚ U)
    (congrArg LinearMap.ker hh))

theorem solution_regular_integral_flag (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    Module.finrank ℤ (LinearMap.ker (shiftedSerre z).toLin') = 1 ∧
      Module.finrank ℤ (LinearMap.ker (shiftedSerre z ^ 2).toLin') = 2 ∧
      Module.finrank ℤ (LinearMap.ker (shiftedSerre z ^ 3).toLin') = 3 := by
  have h := solution_regular_flag z hz hreg
  constructor
  · have hh := integral_kernel_power_finrank_rat z 1
    have hp := congrArg (fun A : Mat4 => Module.finrank ℤ (LinearMap.ker A.toLin'))
      (pow_one (shiftedSerre z))
    exact hp.symm.trans (hh.trans (by simpa using h.1))
  · exact ⟨(integral_kernel_power_finrank_rat z 2).trans h.2.1,
      (integral_kernel_power_finrank_rat z 3).trans h.2.2⟩

theorem integral_kernel_has_retraction (A : Mat4) :
    ∃ r : IntVec4 →ₗ[ℤ] LinearMap.ker A.toLin',
      r.comp (LinearMap.ker A.toLin').subtype = LinearMap.id := by
  obtain ⟨i, hi⟩ := integral_range_has_section A
  let q : IntVec4 →ₗ[ℤ] IntVec4 := LinearMap.id -
    i.comp A.toLin'.rangeRestrict
  have hq (x : IntVec4) : A.toLin' (q x) = 0 := by
    have hx := congrArg (fun F : LinearMap.range A.toLin' →ₗ[ℤ]
        LinearMap.range A.toLin' => F (A.toLin'.rangeRestrict x)) hi
    have hy := congrArg (fun u : LinearMap.range A.toLin' => (u : IntVec4)) hx
    simpa [q, Matrix.mulVec_sub] using sub_eq_zero.mpr hy.symm
  let r := q.codRestrict (LinearMap.ker A.toLin') hq
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : A.toLin'.rangeRestrict (x : IntVec4) = 0 := by
    apply Subtype.ext
    exact x.property
  simp [r, q, hx]

theorem solution_regular_kernel_bases (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    Nonempty (Basis (Fin 1) ℤ (LinearMap.ker (shiftedSerre z).toLin')) ∧
      Nonempty (Basis (Fin 2) ℤ (LinearMap.ker (shiftedSerre z ^ 2).toLin')) := by
  obtain ⟨h1, h2, _⟩ := solution_regular_integral_flag z hz hreg
  exact ⟨⟨Module.finBasisOfFinrankEq ℤ _ h1⟩,
    ⟨Module.finBasisOfFinrankEq ℤ _ h2⟩⟩


/-- A retraction gives an explicit direct sum decomposition. -/
noncomputable def retractionProdEquiv {R M P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P]
    (r : M →ₗ[R] P) (j : P →ₗ[R] M)
    (h : r.comp j = LinearMap.id) : (P × LinearMap.ker r) ≃ₗ[R] M := by
  have hj (x : P) : r (j x) = x := congrArg (fun F : P →ₗ[R] P => F x) h
  let q : M →ₗ[R] M := LinearMap.id - j.comp r
  have hq (x : M) : r (q x) = 0 := by simp [q, hj]
  let qr := q.codRestrict (LinearMap.ker r) hq
  refine LinearEquiv.ofLinear (j.coprod (LinearMap.ker r).subtype) (r.prod qr) ?_ ?_
  · apply LinearMap.ext
    intro x
    simp [qr, q]
  · apply LinearMap.ext
    intro x
    apply Prod.ext
    · simp [hj]
    · apply Subtype.ext
      simp [qr, q, hj]

/-- Unimodularity of the Euler form realizes each integral linear functional. -/
theorem chiVec_realizes_functional (z : Six) (φ : IntVec4 →ₗ[ℤ] ℤ) :
    ∃ x : IntVec4, ∀ y : IntVec4, chiVec z x y = φ y := by
  let w : IntVec4 := fun i => φ (Pi.single i 1)
  have hw : dotProductBilin ℤ ℤ w = φ := by
    apply (Pi.basisFun ℤ (Fin 4)).ext
    intro i
    simp [w, Pi.basisFun_apply, dotProductBilin, dotProduct, Pi.single_apply]
  refine ⟨(gramInverse z)ᵀ *ᵥ w, ?_⟩
  intro y
  have hh : (gram z)ᵀ *ᵥ ((gramInverse z)ᵀ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, inverse_mul_gram]
    simp
  calc
    chiVec z ((gramInverse z)ᵀ *ᵥ w) y =
        ((gram z)ᵀ *ᵥ ((gramInverse z)ᵀ *ᵥ w)) ⬝ᵥ y := by
      unfold chiVec
      rw [Matrix.dotProduct_mulVec,
        Matrix.mulVec_transpose (gram z) ((gramInverse z)ᵀ *ᵥ w)]
    _ = w ⬝ᵥ y := by rw [hh]
    _ = φ y := congrArg (fun F : IntVec4 →ₗ[ℤ] ℤ => F y) hw

/-- The Euler pairing is onto the two coordinate functionals of any kernel basis. -/
theorem chiVec_kernel_coordinates_surjective (z : Six) (A : Mat4)
    (b : Basis (Fin 2) ℤ (LinearMap.ker A.toLin')) :
    Function.Surjective (fun x : IntVec4 => fun i : Fin 2 => chiVec z x (b i : IntVec4)) := by
  intro t
  obtain ⟨r, hr⟩ := integral_kernel_has_retraction A
  let φ : LinearMap.ker A.toLin' →ₗ[ℤ] ℤ :=
    (dotProductBilin ℤ ℤ t).comp b.equivFun.toLinearMap
  obtain ⟨x, hx⟩ := chiVec_realizes_functional z (φ.comp r)
  refine ⟨x, ?_⟩
  funext i
  change chiVec z x (b i : IntVec4) = t i
  rw [hx]
  have hri : r (b i : IntVec4) = b i := congrArg
    (fun F : LinearMap.ker A.toLin' →ₗ[ℤ] LinearMap.ker A.toLin' => F (b i)) hr
  rw [LinearMap.comp_apply, hri]
  fin_cases i <;> simp [φ, dotProductBilin, dotProduct, Basis.equivFun_self]

/-- A regular solution has an integral kernel basis compatible with its first flag step. -/
theorem solution_regular_compatible_basis (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    ∃ b : Basis (Fin 2) ℤ (LinearMap.ker (shiftedSerre z ^ 2).toLin'),
      (shiftedSerre z *ᵥ (b 0 : IntVec4) = 0) ∧
      (∀ x : IntVec4, shiftedSerre z *ᵥ x = 0 →
        ∃ n : ℤ, x = n • (b 0 : IntVec4)) ∧
      ∃ c : ℤ, c ≠ 0 ∧ shiftedSerre z *ᵥ (b 1 : IntVec4) = c • (b 0 : IntVec4) := by
  let K1 := LinearMap.ker (shiftedSerre z).toLin'
  let K2 := LinearMap.ker (shiftedSerre z ^ 2).toLin'
  have h12 : K1 ≤ K2 := by
    intro x hx
    change (shiftedSerre z ^ 2) *ᵥ x = 0
    rw [pow_two, ← Matrix.mulVec_mulVec, show shiftedSerre z *ᵥ x = 0 from hx]
    simp
  obtain ⟨r, hr⟩ := integral_kernel_has_retraction (shiftedSerre z)
  let j : K1 →ₗ[ℤ] K2 := Submodule.inclusion h12
  let r2 : K2 →ₗ[ℤ] K1 := r.comp K2.subtype
  have hr2 : r2.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun F : K1 →ₗ[ℤ] K1 => F x) hr
  let e := retractionProdEquiv r2 j hr2
  obtain ⟨h1, h2, _⟩ := solution_regular_integral_flag z hz hreg
  have hc : Module.finrank ℤ (LinearMap.ker r2) = 1 := by
    have he := LinearEquiv.finrank_eq e
    rw [Module.finrank_prod, h1, h2] at he
    omega
  let b1 := Module.finBasisOfFinrankEq ℤ K1 h1
  let bc := Module.finBasisOfFinrankEq ℤ (LinearMap.ker r2) hc
  let b : Basis (Fin 2) ℤ K2 := ((b1.prod bc).map e).reindex finSumFinEquiv
  have hb0 : (b 0 : IntVec4) = (b1 0 : IntVec4) := by
    simp [b, e, Basis.reindex_apply, Basis.map_apply, retractionProdEquiv,
      j,
      show (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 from rfl]
  have hp : shiftedSerre z *ᵥ (b 0 : IntVec4) = 0 := by
    rw [hb0]
    exact (b1 0).property
  have hgen (x : IntVec4) (hx : shiftedSerre z *ᵥ x = 0) :
      ∃ n : ℤ, x = n • (b 0 : IntVec4) := by
    let xx : K1 := ⟨x, hx⟩
    refine ⟨b1.repr xx 0, ?_⟩
    have hh := b1.sum_repr xx
    simp only [Fin.sum_univ_one] at hh
    have hhh := congrArg (fun u : K1 => (u : IntVec4)) hh
    simpa [hb0] using hhh.symm
  have hl : shiftedSerre z *ᵥ (shiftedSerre z *ᵥ (b 1 : IntVec4)) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_two]
    exact (b 1).property
  obtain ⟨c, hc⟩ := hgen _ hl
  refine ⟨b, hp, hgen, c, ?_, hc⟩
  intro hc0
  have hzero : shiftedSerre z *ᵥ (b 1 : IntVec4) = 0 := by simpa [hc0] using hc
  obtain ⟨n, hn⟩ := hgen _ hzero
  have hh : b 1 = n • b 0 := Subtype.ext hn
  have hrepr := congrArg (fun u : K2 => b.repr u 1) hh
  simp at hrepr

/-- Choose the primitive flag generators with positive integral step length. -/
theorem solution_regular_positive_flag_basis (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    ∃ b : Basis (Fin 2) ℤ (LinearMap.ker (shiftedSerre z ^ 2).toLin'),
      (shiftedSerre z *ᵥ (b 0 : IntVec4) = 0) ∧
      (∀ x : IntVec4, shiftedSerre z *ᵥ x = 0 →
        ∃ n : ℤ, x = n • (b 0 : IntVec4)) ∧
      ∃ k : ℤ, 0 < k ∧ shiftedSerre z *ᵥ (b 1 : IntVec4) = -(k • (b 0 : IntVec4)) := by
  obtain ⟨b, hp, hgen, c, hc, hstep⟩ := solution_regular_compatible_basis z hz hreg
  by_cases hneg : c < 0
  · refine ⟨b, hp, hgen, -c, by omega, ?_⟩
    simpa using hstep
  · let b' := b.unitsSMul (fun i : Fin 2 => if i = 0 then 1 else (-1 : ℤˣ))
    have hb0 : b' 0 = b 0 := by simp [b', Basis.unitsSMul_apply]
    have hb1 : b' 1 = -b 1 := by simp [b', Basis.unitsSMul_apply, Units.smul_def]
    refine ⟨b', ?_, ?_, c, by omega, ?_⟩
    · simpa [hb0] using hp
    · intro x hx
      simpa [hb0] using hgen x hx
    · simp only [hb1, hb0, Submodule.coe_neg, Matrix.mulVec_neg, hstep]

/-- The primitive rank and degree coordinates are jointly onto. -/
theorem solution_regular_primitive_coordinates (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) :
    ∃ (p l : IntVec4) (k : ℤ), 0 < k ∧ shiftedSerre z *ᵥ p = 0 ∧
      shiftedSerre z *ᵥ l = -(k • p) ∧
      (∀ x : IntVec4, shiftedSerre z *ᵥ x = 0 → ∃ n : ℤ, x = n • p) ∧
      (∀ x : IntVec4, (shiftedSerre z ^ 2) *ᵥ x = 0 ↔
        ∃ n t : ℤ, x = n • p + t • l) ∧
      Function.Surjective (fun x : IntVec4 => (chiVec z x p, chiVec z x l)) := by
  obtain ⟨b, hp, hgen, k, hk, hl⟩ := solution_regular_positive_flag_basis z hz hreg
  refine ⟨b 0, b 1, k, hk, hp, hl, hgen, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      let xx : LinearMap.ker (shiftedSerre z ^ 2).toLin' := ⟨x, hx⟩
      refine ⟨b.repr xx 0, b.repr xx 1, ?_⟩
      have hsum : b.repr xx 0 • b 0 + b.repr xx 1 • b 1 = xx := by
        simpa only [Fin.sum_univ_two] using b.sum_repr xx
      have hh := congrArg (fun u : LinearMap.ker (shiftedSerre z ^ 2).toLin' =>
        (u : IntVec4)) hsum
      exact hh.symm
    · rintro ⟨n, t, rfl⟩
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
      rw [show (shiftedSerre z ^ 2) *ᵥ (b 0 : IntVec4) = 0 from (b 0).property,
        show (shiftedSerre z ^ 2) *ᵥ (b 1 : IntVec4) = 0 from (b 1).property]
      simp
  · rintro ⟨u,v⟩
    obtain ⟨x,hx⟩ := chiVec_kernel_coordinates_surjective z (shiftedSerre z ^ 2) b ![u,v]
    refine ⟨x, ?_⟩
    exact Prod.ext (congrFun hx 0) (congrFun hx 1)


theorem chiVec_smul_left (z : Six) (x y : IntVec4) (n : ℤ) :
    chiVec z (n • x) y = n * chiVec z x y := by
  simp only [chiVec, smul_dotProduct, smul_eq_mul]

/-- Every primitive regular Serre flag is totally isotropic for the Euler pairing. -/
theorem regular_primitive_flag_isotropic (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) (p l : IntVec4) (k : ℤ)
    (hp : shiftedSerre z *ᵥ p = 0) (hl : shiftedSerre z *ᵥ l = -(k • p))
    (hgen : ∀ x : IntVec4, shiftedSerre z *ᵥ x = 0 → ∃ n : ℤ, x = n • p)
    (hspan : ∀ x : IntVec4, (shiftedSerre z ^ 2) *ᵥ x = 0 ↔
      ∃ n t : ℤ, x = n • p + t • l) :
    chiVec z p p = 0 ∧ chiVec z p l = 0 ∧ chiVec z l p = 0 ∧ chiVec z l l = 0 := by
  let N := shiftedSerre z
  have h4 : N ^ 4 = 0 := (solution_iff_fourth_power_zero z).mp hz
  have hw : ∃ x : IntVec4, (N ^ 3) *ᵥ x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hreg
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simpa only [Matrix.toLin'_apply, Matrix.zero_mulVec] using h x
  obtain ⟨x, hx⟩ := hw
  have hNx : N *ᵥ ((N ^ 3) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', h4]
    simp
  obtain ⟨a, ha⟩ := hgen _ hNx
  have ha0 : a ≠ 0 := by
    intro hh
    apply hx
    simpa [hh] using ha
  have hd3 : chiVec z ((N ^ 3) *ᵥ x) l = 0 := by
    have hh := flag_degree_second_power z p l (N *ᵥ x) k hp hl
    simpa only [Matrix.mulVec_mulVec, ← pow_succ] using hh
  have hdp : chiVec z p l = 0 := by
    rw [ha, chiVec_smul_left] at hd3
    exact (mul_eq_zero.mp hd3).resolve_left ha0
  have hN2 : (N ^ 2) *ᵥ ((N ^ 2) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_add, h4]
    simp
  obtain ⟨n, t, ht⟩ := (hspan _).mp hN2
  have ht0 : t ≠ 0 := by
    intro hh
    have hh2 : (N ^ 2) *ᵥ x = n • p := by simpa [hh] using ht
    apply hx
    rw [pow_succ', ← Matrix.mulVec_mulVec, hh2, Matrix.mulVec_smul, hp]
    simp
  have hd2 := flag_degree_second_power z p l x k hp hl
  rw [ht, chiVec_add_left, chiVec_smul_left, chiVec_smul_left, hdp] at hd2
  have hdl : chiVec z l l = 0 := by
    exact (mul_eq_zero.mp (by simpa using hd2)).resolve_left ht0
  have hpp := flag_rank_left z p p hp
  have hlp := flag_rank_left z p l hp
  exact ⟨by linarith, hdp, by linarith, hdl⟩


/-- The primitive integral Jordan flag and its rank and degree coordinates. -/
structure PrimitiveSerreFlag (z : Six) where
  p : IntVec4
  l : IntVec4
  k : ℤ
  k_pos : 0 < k
  first_step : shiftedSerre z *ᵥ p = 0
  second_step : shiftedSerre z *ᵥ l = -(k • p)
  first_generator : ∀ x : IntVec4, shiftedSerre z *ᵥ x = 0 → ∃ n : ℤ, x = n • p
  second_span : ∀ x : IntVec4, (shiftedSerre z ^ 2) *ᵥ x = 0 ↔
    ∃ n t : ℤ, x = n • p + t • l
  coordinates_surjective : Function.Surjective
    (fun x : IntVec4 => (chiVec z x p, chiVec z x l))
  isotropic_pp : chiVec z p p = 0
  isotropic_pl : chiVec z p l = 0
  isotropic_lp : chiVec z l p = 0
  isotropic_ll : chiVec z l l = 0

/-- Every regular integral solution admits the primitive isotropic flag. -/
theorem solution_regular_has_primitive_flag (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) : Nonempty (PrimitiveSerreFlag z) := by
  obtain ⟨p, l, k, hk, hp, hl, hgen, hspan, hsurj⟩ :=
    solution_regular_primitive_coordinates z hz hreg
  obtain ⟨hpp, hpl, hlp, hll⟩ :=
    regular_primitive_flag_isotropic z hz hreg p l k hp hl hgen hspan
  exact ⟨⟨p, l, k, hk, hp, hl, hgen, hspan, hsurj, hpp, hpl, hlp, hll⟩⟩

end SerreMarkov
