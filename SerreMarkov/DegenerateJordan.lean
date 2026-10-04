import SerreMarkov.DegenerateClassification
import SerreMarkov.Intrinsic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # The two square-zero types of the degenerate representatives

The rational rank is one at parameter two and two at every other normalized
parameter. Together with square-zero, these are respectively the Jordan
block sizes [2,1,1] and [2,2].
-/

namespace SerreMarkov.DegenerateJordan
open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

def shifted (k : ℤ) : RatMat4 :=
  !![-2,(k:ℚ),(k:ℚ),2;
     -(k:ℚ),(k:ℚ)^2-2,(k:ℚ)^2-2,(k:ℚ);
     (k:ℚ),2-(k:ℚ)^2,2-(k:ℚ)^2,-(k:ℚ);
     -2,(k:ℚ),(k:ℚ),2]

theorem shifted_eq_cast (k : ℤ) :
    shifted k=integerToRatMatrix (shiftedSerre (family k (-k))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted,integerToRatMatrix,shiftedSerre,serre,gramInverse,gram,family,
      Matrix.mul_apply,Fin.sum_univ_four] <;> ring

theorem shifted_square_zero (k : ℤ) : shifted k*shifted k=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shifted,Matrix.mul_apply,Fin.sum_univ_four] <;> ring

private def firstTwoRows : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
private def firstTwoCols : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,0;0,0]
private def firstRow : Matrix (Fin 1) (Fin 4) ℚ := !![1,0,0,0]
private def firstCol : Matrix (Fin 4) (Fin 1) ℚ := !![1;0;0;0]

private theorem two_minor_det (k : ℤ) :
    (firstTwoRows*shifted k*firstTwoCols).det=4-(k:ℚ)^2 := by
  simp [firstTwoRows,firstTwoCols,shifted,Matrix.det_fin_two,Matrix.mul_apply,
    Fin.sum_univ_four]
  ring

private theorem one_minor (k : ℤ) : firstRow*shifted k*firstCol=!![(-2:ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  simp [firstRow,firstCol,shifted,Matrix.mul_apply,Fin.sum_univ_four]

theorem shifted_rank_pos (k : ℤ) : 1≤(shifted k).rank := by
  have hu : IsUnit (firstRow*shifted k*firstCol) := by
    rw [one_minor]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    norm_num [Matrix.det_fin_one]
  have hr := Matrix.rank_of_isUnit _ hu
  have h1 := Matrix.rank_mul_le_left (firstRow*shifted k) firstCol
  have h2 := Matrix.rank_mul_le_right firstRow (shifted k)
  simp only [Fintype.card_fin] at hr
  omega

theorem shifted_rank_le_two (k : ℤ) : (shifted k).rank≤2 := by
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero (shifted_square_zero k)
  simp only [Fintype.card_fin] at h
  omega

theorem shifted_rank_at_two : (shifted 2).rank=1 := by
  have houter : shifted 2=Matrix.vecMulVec ![(-2:ℚ),-2,2,-2] ![(1:ℚ),-1,-1,-1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [shifted,Matrix.vecMulVec]
  have hhi : (shifted 2).rank≤1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le _ _
  exact Nat.le_antisymm hhi (shifted_rank_pos 2)

theorem shifted_rank_away_from_two (k : ℤ) (hk : 0≤k) (hne : k≠2) :
    (shifted k).rank=2 := by
  have hdet : 4-(k:ℚ)^2≠0 := by
    have hkq : 0≤(k:ℚ) := by exact_mod_cast hk
    have hneq : (k:ℚ)≠2 := by exact_mod_cast hne
    intro h
    have htwo : (k:ℚ)=2 := by nlinarith only [h,hkq]
    exact hneq htwo
  have hu : IsUnit (firstTwoRows*shifted k*firstTwoCols) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [two_minor_det,isUnit_iff_ne_zero]
    exact hdet
  have hr := Matrix.rank_of_isUnit _ hu
  have h1 := Matrix.rank_mul_le_left (firstTwoRows*shifted k) firstTwoCols
  have h2 := Matrix.rank_mul_le_right firstTwoRows (shifted k)
  simp only [Fintype.card_fin] at hr
  exact Nat.le_antisymm (shifted_rank_le_two k) (by omega)

theorem degenerate_family_rank (k : ℤ) (hk : 0≤k) :
    (integerToRatMatrix (shiftedSerre (family k (-k)))).rank=
      if k=2 then 1 else 2 := by
  rw [←shifted_eq_cast]
  by_cases h : k=2
  · subst k
    simpa using shifted_rank_at_two
  · simpa [h] using shifted_rank_away_from_two k hk h

theorem latticeEquivalent_shifted_rank {z w : Six} (h : LatticeEquivalent z w) :
    (integerToRatMatrix (shiftedSerre z)).rank=
      (integerToRatMatrix (shiftedSerre w)).rank := by
  obtain ⟨B,hB⟩ := h
  have hu : IsUnit (integerToRatMatrix (B : Mat4)) :=
    (show IsUnit (B : Mat4) from ⟨B,rfl⟩).map integerToRatMatrix
  have hv : IsUnit (integerToRatMatrix (↑B⁻¹ : Mat4)) :=
    (show IsUnit (↑B⁻¹ : Mat4) from ⟨B⁻¹,rfl⟩).map integerToRatMatrix
  rw [shiftedSerre_unit_conjugate B hB,map_mul,map_mul]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hv)]

theorem degenerate_classification_with_rank (z : Six) (hz : isSolution z)
    (hc : shiftedSerre z^3=0) :
    ∃! k : ℤ, 0≤k ∧ Reachable z (family k (-k)) ∧
      (integerToRatMatrix (shiftedSerre z)).rank=(if k=2 then 1 else 2) := by
  obtain ⟨k,⟨hk,hr⟩,hu⟩ := degenerate_classification z hz hc
  refine ⟨k,⟨hk,hr,?_⟩,fun l hl => hu l ⟨hl.1,hl.2.1⟩⟩
  rw [latticeEquivalent_shifted_rank (reachable_latticeEquivalent hr)]
  exact degenerate_family_rank k hk

end SerreMarkov.DegenerateJordan
