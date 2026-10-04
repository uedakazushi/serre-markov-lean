import SerreMarkov.PositiveGroups
import SerreMarkov.PositiveTriangleLower

/-! # Exact traces of the actual positive half-turn product

The genuine even matrix group contains a nonidentity parabolic: its four-turn
product has determinant one, trace squared four, and is not either scalar lift
of the identity. This is an algebraic bridge only; finite index and a
fundamental domain are not asserted here. -/

namespace SerreMarkov.PositiveParabolicTrace

open Matrix RationalClifford CliffordOrder IntrinsicFrame PositiveChamber
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

private theorem zero_trace_entry (U : RealMat2) (hU : U.trace=0) : U 1 1 = -U 0 0 := by
  simp only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two] at hU
  linarith

/-- The four-matrix Clifford trace identity, with no normalization assumptions. -/
theorem four_trace_identity (U V W X : RealMat2)
    (hU : U.trace=0) (hV : V.trace=0) (hW : W.trace=0) (hX : X.trace=0) :
    2*(U*V*W*X).trace = (U*V).trace*(W*X).trace-
      (U*W).trace*(V*X).trace+(U*X).trace*(V*W).trace := by
  have hu := zero_trace_entry U hU
  have hv := zero_trace_entry V hV
  have hw := zero_trace_entry W hW
  have hx := zero_trace_entry X hX
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fin.sum_univ_two,hu,hv,hw,hx]
  ring

/-- The squared three-matrix trace is an exact Gram determinant formula. -/
theorem three_trace_identity (U V W : RealMat2)
    (hU : U.trace=0) (hV : V.trace=0) (hW : W.trace=0) :
    (U*V*W).trace^2 = 4*U.det*V.det*W.det-
      U.det*(V*W).trace^2-V.det*(U*W).trace^2-W.det*(U*V).trace^2-
      (U*V).trace*(U*W).trace*(V*W).trace := by
  have hu := zero_trace_entry U hU
  have hv := zero_trace_entry V hV
  have hw := zero_trace_entry W hW
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_two,hu,hv,hw]
  ring

theorem normalized_generator_eq (D : NormedClifford.Data) (i : Fin 4) :
    generator (NormedClifford.generators D) i = NormedClifford.normalized D.A (D.B i) := by
  fin_cases i <;> rfl

theorem normalized_generator_trace (D : NormedClifford.Data) (i : Fin 4) :
    (generator (NormedClifford.generators D) i).trace=0 := by
  rw [normalized_generator_eq]
  dsimp [NormedClifford.normalized]
  rw [Matrix.trace_smul]
  have hz : (rationalMatrixCast (D.B i)).trace=0 := by
    have h := D.trace_zero i
    simp only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,rationalMatrixCast_apply] at h ⊢
    exact_mod_cast h
  rw [hz,smul_zero]

theorem normalized_pair_trace (D : NormedClifford.Data) (i j : Fin 4) :
    (generator (NormedClifford.generators D) i *
      generator (NormedClifford.generators D) j).trace=(D.pairing i j : ℝ) := by
  rw [normalized_generator_eq,normalized_generator_eq,
    NormedClifford.normalized_product D.A D.positive]
  rw [NormedClifford.rationalMatrixCast_smul,Matrix.trace_smul]
  have ht : (rationalMatrixCast (D.B i*D.B j)).trace=
      (D.A : ℝ)*(D.pairing i j : ℝ) := by
    have h := D.pair_trace i j
    simp only [Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,rationalMatrixCast_apply] at h ⊢
    exact_mod_cast h
  rw [ht]
  simp only [smul_eq_mul,Rat.cast_div,Rat.cast_one]
  have hA : (D.A : ℝ) ≠ 0 := by exact_mod_cast D.positive.ne'
  field_simp

noncomputable def turn {z : Six} (R : Frame z) (hA : 0 < A R) (i : Fin 4) : RealMat2 :=
  generator (NormedClifford.generators (positiveHalfTurnData R hA)) i

noncomputable def product {z : Six} (R : Frame z) (hA : 0 < A R) : RealMat2 :=
  turn R hA 0 * turn R hA 1 * turn R hA 2 * turn R hA 3

theorem turn_trace {z : Six} (R : Frame z) (hA : 0 < A R) (i : Fin 4) :
    (turn R hA i).trace=0 := normalized_generator_trace _ i

theorem turn_det {z : Six} (R : Frame z) (hA : 0 < A R) (i : Fin 4) :
    (turn R hA i).det=1 := NormedClifford.generator_determinant _ i

theorem turn_pair_trace {z : Six} (R : Frame z) (hA : 0 < A R) (i j : Fin 4) :
    (turn R hA i * turn R hA j).trace=-(symmetricForm z i j : ℝ) := by
  have ht := normalized_pair_trace (positiveHalfTurnData R hA) i j
  simpa only [turn,positiveHalfTurnData,NormedClifford.ofNumerators,Int.cast_neg] using ht

theorem product_trace {z : Six} (R : Frame z) (hA : 0 < A R) :
    2*(product R hA).trace=(q2 z : ℝ) := by
  have ht := four_trace_identity (turn R hA 0) (turn R hA 1) (turn R hA 2)
    (turn R hA 3) (turn_trace R hA 0) (turn_trace R hA 1)
    (turn_trace R hA 2) (turn_trace R hA 3)
  rw [turn_pair_trace R hA 0 1,turn_pair_trace R hA 2 3,
    turn_pair_trace R hA 0 2,turn_pair_trace R hA 1 3,
    turn_pair_trace R hA 0 3,turn_pair_trace R hA 1 2] at ht
  simpa [product,symmetricForm,gram,q2] using ht

theorem triple_trace_square {z : Six} (R : Frame z) (hA : 0 < A R) :
    (turn R hA 0 * turn R hA 1 * turn R hA 2).trace^2 =
      4-(triangleDefect z.a z.b z.d : ℝ) := by
  have ht := three_trace_identity (turn R hA 0) (turn R hA 1) (turn R hA 2)
    (turn_trace R hA 0) (turn_trace R hA 1) (turn_trace R hA 2)
  rw [turn_det R hA 0,turn_det R hA 1,turn_det R hA 2,
    turn_pair_trace R hA 1 2,turn_pair_trace R hA 0 2,
    turn_pair_trace R hA 0 1] at ht
  simp [symmetricForm,gram] at ht
  rw [ht]
  push_cast [triangleDefect]
  ring

theorem product_det {z : Six} (R : Frame z) (hA : 0 < A R) :
    (product R hA).det=1 := by
  simp only [product,Matrix.det_mul,turn_det,mul_one]

theorem product_trace_square {z : Six} (R : Frame z) (hA : 0 < A R)
    (hz : isSolution z) : (product R hA).trace^2=4 := by
  have ht := product_trace R hA
  have hq : (q2 z : ℝ)^2=16 := by exact_mod_cast hz.2
  have hs := congrArg (fun x : ℝ => x^2) ht
  nlinarith only [hs,hq]

theorem turn_square {z : Six} (R : Frame z) (hA : 0 < A R) (i : Fin 4) :
    turn R hA i * turn R hA i = -1 := by
  let D := positiveHalfTurnData R hA
  fin_cases i
  · exact (NormedClifford.generators D).square_a
  · exact (NormedClifford.generators D).square_b
  · exact (NormedClifford.generators D).square_c
  · exact (NormedClifford.generators D).square_d

theorem triple_trace_square_ge_eleven {z : Six} (R : Frame z) (hA : 0 < A R)
    (hz : Chamber z) : 11 ≤ (turn R hA 0 * turn R hA 1 * turn R hA 2).trace^2 := by
  rw [triple_trace_square]
  have hf : (triangleDefect z.a z.b z.d : ℝ) ≤ -7 := by
    exact_mod_cast PositiveTriangleLower.chamber_abd_defect_bound z hz
  linarith

/-- Scalar lifts of the projective identity are excluded by the exact
three-turn trace, without using a fundamental domain. -/
theorem product_ne_scalar {z : Six} (R : Frame z) (hA : 0 < A R)
    (hz : Chamber z) (s : ℝ) : product R hA ≠ s • (1 : RealMat2) := by
  intro hscalar
  have hprod : product R hA * turn R hA 3 =
      -(turn R hA 0 * turn R hA 1 * turn R hA 2) := by
    dsimp only [product]
    rw [Matrix.mul_assoc (turn R hA 0 * turn R hA 1 * turn R hA 2),turn_square]
    simp only [mul_neg,mul_one]
  have ht := congrArg Matrix.trace hprod
  rw [hscalar,Matrix.smul_mul,one_mul,Matrix.trace_smul,turn_trace,
    smul_zero,Matrix.trace_neg] at ht
  have hl := triple_trace_square_ge_eleven R hA hz
  nlinarith only [ht,hl]

theorem product_word {z : Six} (R : Frame z) (hA : 0 < A R) :
    (PositiveGroups.liftedWord (positiveHalfTurnData R hA) [0,1,2,3] : RealMat2) =
      product R hA := by
  change wordProduct (NormedClifford.generators (positiveHalfTurnData R hA)) [0,1,2,3]=_
  simp only [wordProduct,product,turn,mul_one,Matrix.mul_assoc]

/-- The actual projective even group contains a nonidentity element with
parabolic trace. No finite-index premise is added. -/
theorem actual_even_group_parabolic {z : Six} (R : Frame z) (hA : 0 < A R)
    (hz : Chamber z) :
    ∃ P : PositiveGroups.RealSL2,
      P ∈ PositiveGroups.evenGroup (positiveHalfTurnData R hA) ∧
      (P : RealMat2).trace^2=4 ∧ PositiveGroups.projective P ≠ 1 := by
  let P := PositiveGroups.liftedWord (positiveHalfTurnData R hA) [0,1,2,3]
  have hword : (P : RealMat2)=product R hA := product_word R hA
  refine ⟨P,PositiveGroups.even_word_mem_evenGroup _ _ (by decide),?_,?_⟩
  · rw [hword]
    exact product_trace_square R hA hz.1
  · intro hidentity
    have hcenter : P ∈ Subgroup.center PositiveGroups.RealSL2 := by
      change (QuotientGroup.mk P : PositiveGroups.RealPSL2)=1 at hidentity
      rwa [QuotientGroup.eq_one_iff] at hidentity
    obtain ⟨s,_,hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
    apply product_ne_scalar R hA hz s
    rw [←hword,←hscalar]
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply]

end SerreMarkov.PositiveParabolicTrace
