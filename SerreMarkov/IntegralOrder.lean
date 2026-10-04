import SerreMarkov.HalfTurns
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Matrix.Basis

namespace SerreMarkov.IntegralOrder

open Matrix
abbrev Vec2 := Fin 2 → ℚ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

def standard (j : Fin 2) : Vec2 := Pi.single j 1

def evaluation (O : Subalgebra ℤ Mat2) (j : Fin 2) : O →ₗ[ℤ] Vec2 where
  toFun B := (B : Mat2) *ᵥ standard j
  map_add' B C := by simp [Matrix.add_mulVec]
  map_smul' n B := by
    change (n • (B : Mat2)) *ᵥ standard j = n • ((B : Mat2) *ᵥ standard j)
    exact Matrix.smul_mulVec n (B : Mat2) (standard j)

/-- The order applied to the standard integer lattice. -/
def lattice (O : Subalgebra ℤ Mat2) : Submodule ℤ Vec2 :=
  LinearMap.range (evaluation O 0) ⊔ LinearMap.range (evaluation O 1)

theorem range_fg (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] (j : Fin 2) :
    (LinearMap.range (evaluation O j)).FG := by
  simpa only [Submodule.map_top] using
    (Module.Finite.fg_top (R := ℤ) (M := O)).map (evaluation O j)

theorem lattice_fg (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] : (lattice O).FG :=
  (range_fg O 0).sup (range_fg O 1)

theorem standard_mem (O : Subalgebra ℤ Mat2) (j : Fin 2) : standard j ∈ lattice O := by
  have hj : standard j ∈ LinearMap.range (evaluation O j) := by
    refine ⟨1, ?_⟩
    simp [evaluation]
  fin_cases j
  · exact Submodule.mem_sup_left hj
  · exact Submodule.mem_sup_right hj

theorem lattice_spans (O : Subalgebra ℤ Mat2) :
    Submodule.span ℚ (lattice O : Set Vec2) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℚ (Fin 2)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  simpa [standard, Pi.basisFun_apply] using standard_mem O j

instance lattice_isLattice (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] :
    Submodule.IsLattice ℚ (lattice O) where
  fg := lattice_fg O
  span_eq_top := lattice_spans O

theorem lattice_rank (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] :
    Module.finrank ℤ (lattice O) = 2 := by
  simpa using (Submodule.IsLattice.finrank_of_pi ℚ (lattice O))

theorem evaluation_stable (O : Subalgebra ℤ Mat2) (B : O) (j : Fin 2)
    {v : Vec2} (hv : v ∈ LinearMap.range (evaluation O j)) :
    (B : Mat2) *ᵥ v ∈ LinearMap.range (evaluation O j) := by
  obtain ⟨C, rfl⟩ := hv
  refine ⟨B*C, ?_⟩
  exact (Matrix.mulVec_mulVec (standard j) (B : Mat2) (C : Mat2)).symm

theorem lattice_stable (O : Subalgebra ℤ Mat2) (B : O)
    {v : Vec2} (hv : v ∈ lattice O) : (B : Mat2) *ᵥ v ∈ lattice O := by
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (evaluation_stable O B 0 hv₀))
    (Submodule.mem_sup_right (evaluation_stable O B 1 hv₁))

def latticeAction (O : Subalgebra ℤ Mat2) (B : O) :
    lattice O →ₗ[ℤ] lattice O where
  toFun v := ⟨(B : Mat2) *ᵥ (v : Vec2), lattice_stable O B v.property⟩
  map_add' v w := by
    apply Subtype.ext
    change (B : Mat2) *ᵥ ((v : Vec2) + (w : Vec2)) =
      (B : Mat2) *ᵥ (v : Vec2) + (B : Mat2) *ᵥ (w : Vec2)
    exact Matrix.mulVec_add _ _ _
  map_smul' n v := by
    apply Subtype.ext
    change (B : Mat2) *ᵥ (n • (v : Vec2)) = n • ((B : Mat2) *ᵥ (v : Vec2))
    exact Matrix.mulVec_smul _ _ _

theorem extended_repr (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O]
    (b : Module.Basis (Fin 2) ℤ (lattice O)) (v : lattice O) (i : Fin 2) :
    (b.extendOfIsLattice ℚ).repr (v : Vec2) i = (b.repr v i : ℚ) := by
  have hv := congrArg (fun x : lattice O => (x : Vec2)) (b.sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hv
  have hrepr (j : Fin 2) : (b.extendOfIsLattice ℚ).repr (b j : Vec2) =
      Finsupp.single j 1 := by
    rw [← Module.Basis.extendOfIsLattice_apply ℚ b]
    exact (b.extendOfIsLattice ℚ).repr_self j
  rw [← hv]
  simp only [← Int.cast_smul_eq_zsmul ℚ, map_sum, map_smul, hrepr]
  fin_cases i <;> simp [Finsupp.single_apply]

/-- A single rational basis gives integer matrices for every element of the
finite integral order. No separate basis is chosen for individual elements. -/
theorem exists_integral_representation (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] :
    ∃ b : Module.Basis (Fin 2) ℚ Vec2,
      ∀ B : O, ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
        LinearMap.toMatrix b b (Matrix.mulVecLin (B : Mat2)) =
          Z.map (Int.cast : ℤ → ℚ) := by
  let b := Module.finBasisOfFinrankEq ℤ (lattice O) (lattice_rank O)
  refine ⟨b.extendOfIsLattice ℚ, fun B => ?_⟩
  refine ⟨LinearMap.toMatrix b b (latticeAction O B), ?_⟩
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply,
    Module.Basis.extendOfIsLattice_apply, Matrix.mulVecLin_apply]
  exact extended_repr O b (latticeAction O B (b j)) i

/-- The common integer representation is an actual rational conjugation. -/
theorem exists_integral_conjugation (O : Subalgebra ℤ Mat2) [Module.Finite ℤ O] :
    ∃ C Cinv : Mat2, C*Cinv = 1 ∧ Cinv*C = 1 ∧
      ∀ B : O, ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
        Cinv * (B : Mat2) * C = Z.map (Int.cast : ℤ → ℚ) := by
  obtain ⟨b, hb⟩ := exists_integral_representation O
  let s := Pi.basisFun ℚ (Fin 2)
  refine ⟨s.toMatrix b, b.toMatrix s, s.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip s, fun B => ?_⟩
  obtain ⟨Z, hZ⟩ := hb B
  refine ⟨Z, ?_⟩
  have hstd : LinearMap.toMatrix s s (Matrix.mulVecLin (B : Mat2)) = (B : Mat2) := by
    simp only [s, LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin']
  rw [← hstd,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b s b s,
    hZ]

/-- The conjugating rational basis can be chosen with positive orientation. -/
theorem exists_integral_conjugation_positive (O : Subalgebra ℤ Mat2)
    [Module.Finite ℤ O] :
    ∃ C Cinv : Mat2, 0 < C.det ∧ C*Cinv = 1 ∧ Cinv*C = 1 ∧
      ∀ B : O, ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
        Cinv * (B : Mat2) * C = Z.map (Int.cast : ℤ → ℚ) := by
  obtain ⟨C, Cinv, hCC, hIC, h⟩ := exists_integral_conjugation O
  by_cases hp : 0 < C.det
  · exact ⟨C, Cinv, hp, hCC, hIC, h⟩
  have hn : C.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hCC
    simp [Matrix.det_mul, hz] at hh
  have hneg : C.det < 0 := by
    rcases eq_or_lt_of_le (le_of_not_gt hp) with hz | hlt
    · exact False.elim (hn hz)
    · exact hlt
  let Pz : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]
  let f : Matrix (Fin 2) (Fin 2) ℤ →+* Mat2 := (Int.castRingHom ℚ).mapMatrix
  let P := f Pz
  have hPP : P*P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, f, Pz, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hPd : P.det = -1 := by
    norm_num [P, f, Pz, Matrix.det_fin_two, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine ⟨C*P, P*Cinv, ?_, ?_, ?_, fun B => ?_⟩
  · rw [Matrix.det_mul, hPd]
    linarith
  · calc
      C*P*(P*Cinv) = C*(P*P)*Cinv := by noncomm_ring
      _ = 1 := by rw [hPP]; simpa using hCC
  · calc
      P*Cinv*(C*P) = P*(Cinv*C)*P := by noncomm_ring
      _ = 1 := by rw [hIC]; simpa using hPP
  · obtain ⟨Z, hZ⟩ := h B
    refine ⟨Pz*Z*Pz, ?_⟩
    change Cinv * (B : Mat2) * C = f Z at hZ
    change (P*Cinv) * (B : Mat2) * (C*P) = f (Pz*Z*Pz)
    calc
      (P*Cinv) * (B : Mat2) * (C*P) = P * (Cinv * (B : Mat2) * C) * P := by
        noncomm_ring
      _ = f (Pz*Z*Pz) := by rw [hZ, map_mul, map_mul]

end SerreMarkov.IntegralOrder
