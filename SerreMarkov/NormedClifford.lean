import SerreMarkov.RationalClifford
import SerreMarkov.HalfTurns
import Mathlib.Data.Real.Sqrt

/-!
# Square-root normalization of rational half-turn numerators

Positive rational `A` and four trace-zero rational matrices with square `-A`
define real Clifford generators. All eight even monomials are rational,
although the four generators involve a square root.
-/

namespace SerreMarkov.NormedClifford

open RationalClifford
set_option maxHeartbeats 2000000

@[simp] theorem rationalMatrixCast_smul (q : ℚ) (B : RatMat2) :
    rationalMatrixCast (q • B) = (q : ℝ) • rationalMatrixCast B := by
  ext i j
  simp [Matrix.smul_apply, Rat.cast_mul]

/-- The actual real square-root-normalized lift. -/
noncomputable def normalized (A : ℚ) (B : RatMat2) : RealMat2 :=
  (Real.sqrt (A : ℝ))⁻¹ • rationalMatrixCast B

private theorem normalization_scalar (A : ℚ) (hA : 0 < A) :
    (Real.sqrt (A : ℝ))⁻¹ * (Real.sqrt (A : ℝ))⁻¹ = ((1/A : ℚ) : ℝ) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hs : Real.sqrt (A : ℝ) ≠ 0 := (Real.sqrt_pos.2 hAr).ne'
  have hsq := Real.sq_sqrt hAr.le
  push_cast
  field_simp
  nlinarith [hsq]

/-- Pair products are the casts of rational matrices with denominator `A`. -/
theorem normalized_product (A : ℚ) (hA : 0 < A) (U V : RatMat2) :
    normalized A U * normalized A V = rationalMatrixCast ((1/A) • (U*V)) := by
  rw [normalized, normalized, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    normalization_scalar A hA, ← map_mul, rationalMatrixCast_smul]

/-- Four normalized factors have the rational denominator `A²`. -/
theorem normalized_quadruple (A : ℚ) (hA : 0 < A) (U V W X : RatMat2) :
    normalized A U * (normalized A V * (normalized A W * normalized A X)) =
      rationalMatrixCast ((1/A^2) • (U*(V*(W*X)))) := by
  calc
    _ = (normalized A U * normalized A V) * (normalized A W * normalized A X) := by
      simp only [mul_assoc]
    _ = rationalMatrixCast (((1/A) • (U*V)) * ((1/A) • (W*X))) := by
      rw [normalized_product A hA, normalized_product A hA, map_mul]
    _ = _ := by
      congr 1
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hs : (1/A : ℚ)*(1/A) = 1/A^2 := by ring
      rw [hs, mul_assoc]

theorem normalized_square (A : ℚ) (hA : 0 < A) (B : RatMat2)
    (hB : B*B = (-A) • (1 : RatMat2)) :
    normalized A B * normalized A B = -1 := by
  rw [normalized_product A hA, hB, smul_smul]
  have hs : (1/A : ℚ)*(-A) = -1 := by field_simp
  rw [hs]
  simp

theorem normalized_anticommutator (A : ℚ) (hA : 0 < A) (U V : RatMat2)
    (hU : U.trace = 0) (hV : V.trace = 0) (h : ℤ)
    (htrace : (U*V).trace = A*(h : ℚ)) :
    normalized A U * normalized A V + normalized A V * normalized A U =
      h • (1 : RealMat2) := by
  rw [normalized_product A hA, normalized_product A hA, ← map_add,
    ← smul_add, HalfTurns.anticommutator U V hU hV, htrace, smul_smul]
  have hs : (1/A : ℚ)*(A*(h:ℚ)) = h := by field_simp
  rw [hs]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- A trace-zero two-by-two square `-A I` has determinant `A`. -/
theorem numerator_determinant (A : ℚ) (B : RatMat2)
    (ht : B.trace = 0) (hs : B*B = (-A) • (1 : RatMat2)) : B.det = A := by
  have hdiag : B 1 1 = -B 0 0 := by
    simp [Matrix.trace, Fin.sum_univ_succ] at ht
    linarith
  have h00 := congrArg (fun M : RatMat2 => M 0 0) hs
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply] at h00
  rw [Matrix.det_fin_two, hdiag]
  nlinarith [h00]

/-- Each normalized half-turn is a concrete determinant-one real matrix. -/
theorem normalized_determinant (A : ℚ) (hA : 0 < A) (B : RatMat2)
    (ht : B.trace = 0) (hs : B*B = (-A) • (1 : RatMat2)) :
    (normalized A B).det = 1 := by
  rw [normalized, Matrix.det_smul]
  simp only [Fintype.card_fin, pow_two]
  rw [normalization_scalar A hA]
  have hcast : (rationalMatrixCast B).det = (B.det : ℝ) :=
    ((Rat.castHom ℝ).map_det B).symm
  rw [hcast, numerator_determinant A B ht hs]
  push_cast
  field_simp

/-- Rational input data, including the integral normalized pair traces. -/
structure Data where
  A : ℚ
  positive : 0 < A
  B : Fin 4 → RatMat2
  pairing : Fin 4 → Fin 4 → ℤ
  trace_zero : ∀ i, (B i).trace = 0
  square : ∀ i, B i * B i = (-A) • (1 : RatMat2)
  pair_trace : ∀ i j, (B i*B j).trace = A*(pairing i j : ℚ)

/-- Riemann--Roch data supply the rational Clifford numerators directly. -/
def ofNumerators (A : ℚ) (hA : 0 < A) (r d : Fin 4 → ℚ)
    (h : Fin 4 → Fin 4 → ℤ) (hr : ∀ i, r i ≠ 0)
    (hRR : ∀ i j, (h i j : ℚ)*r i*r j =
      (r i)^2+(r j)^2+A*(r i*d j-r j*d i)^2) : Data where
  A := A
  positive := hA
  B i := HalfTurns.numerator A (r i) (d i)
  pairing i j := -h i j
  trace_zero i := HalfTurns.numerator_trace A (r i) (d i)
  square i := HalfTurns.numerator_square A (r i) (d i) (hr i)
  pair_trace i j := by
    have ht := HalfTurns.even_product_trace A (r i) (r j) (d i) (d j)
      (h i j : ℚ) hA.ne' (hr i) (hr j) (hRR i j)
    rw [Matrix.trace_smul, smul_eq_mul] at ht
    push_cast
    field_simp [hA.ne'] at ht
    linarith

/-- Concrete real Clifford generators built using the positive square root. -/
noncomputable def generators (D : Data) : CliffordOrder.Generators RealMat2 where
  a := normalized D.A (D.B 0)
  b := normalized D.A (D.B 1)
  c := normalized D.A (D.B 2)
  d := normalized D.A (D.B 3)
  hab := D.pairing 0 1
  hac := D.pairing 0 2
  had := D.pairing 0 3
  hbc := D.pairing 1 2
  hbd := D.pairing 1 3
  hcd := D.pairing 2 3
  square_a := normalized_square D.A D.positive (D.B 0) (D.square 0)
  square_b := normalized_square D.A D.positive (D.B 1) (D.square 1)
  square_c := normalized_square D.A D.positive (D.B 2) (D.square 2)
  square_d := normalized_square D.A D.positive (D.B 3) (D.square 3)
  relation_ab := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 0) (D.trace_zero 1) _ (D.pair_trace 0 1)
  relation_ac := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 0) (D.trace_zero 2) _ (D.pair_trace 0 2)
  relation_ad := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 0) (D.trace_zero 3) _ (D.pair_trace 0 3)
  relation_bc := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 1) (D.trace_zero 2) _ (D.pair_trace 1 2)
  relation_bd := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 1) (D.trace_zero 3) _ (D.pair_trace 1 3)
  relation_cd := normalized_anticommutator D.A D.positive _ _
    (D.trace_zero 2) (D.trace_zero 3) _ (D.pair_trace 2 3)

theorem generator_determinant (D : Data) (i : Fin 4) :
    (CliffordOrder.generator (generators D) i).det = 1 := by
  fin_cases i <;> dsimp [CliffordOrder.generator, generators] <;>
    exact normalized_determinant D.A D.positive _ (D.trace_zero _) (D.square _)

/-- Every word in the actual normalized real matrices has determinant one. -/
theorem word_determinant (D : Data) (w : List (Fin 4)) :
    (CliffordOrder.wordProduct (generators D) w).det = 1 := by
  induction w with
  | nil => simp [CliffordOrder.wordProduct]
  | cons i w ih =>
    rw [CliffordOrder.wordProduct, Matrix.det_mul, generator_determinant, ih, mul_one]

/-- Eight explicit rational lifts of the ordered even Clifford monomials. -/
def rationalEvenMonomial (D : Data) (i : Fin 8) : RatMat2 :=
  match i.val with
  | 0 => 1
  | 1 => (1/D.A) • (D.B 0*D.B 1)
  | 2 => (1/D.A) • (D.B 0*D.B 2)
  | 3 => (1/D.A) • (D.B 0*D.B 3)
  | 4 => (1/D.A) • (D.B 1*D.B 2)
  | 5 => (1/D.A) • (D.B 1*D.B 3)
  | 6 => (1/D.A) • (D.B 2*D.B 3)
  | _ => (1/D.A^2) • (D.B 0*(D.B 1*(D.B 2*D.B 3)))

theorem cast_rationalEvenMonomial (D : Data) (i : Fin 8) :
    rationalMatrixCast (rationalEvenMonomial D i) =
      CliffordOrder.evenMonomial (generators D) i := by
  fin_cases i <;> dsimp [rationalEvenMonomial, CliffordOrder.evenMonomial, generators]
  · exact map_one _
  all_goals first
    | exact (normalized_product D.A D.positive _ _).symm
    | exact (normalized_quadruple D.A D.positive _ _ _ _).symm

/-- The normalized half-turns generate a finite rational integral even order. -/
noncomputable def order (D : Data) : Subalgebra ℤ RatMat2 :=
  rationalOrder (generators D) (rationalEvenMonomial D) (cast_rationalEvenMonomial D)

instance order_finite (D : Data) : Module.Finite ℤ (order D) := by
  unfold order rationalOrder
  infer_instance

end SerreMarkov.NormedClifford
