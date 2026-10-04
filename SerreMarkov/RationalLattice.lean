import SerreMarkov.RationalClifford
import SerreMarkov.IntegralOrder
import SerreMarkov.NormedClifford
import Mathlib.LinearAlgebra.Determinant

/-!
# A rational lattice preserved by the even Clifford order

The eight rational lifts of the real even monomials give a single rank-two
integer lattice preserved by every rational matrix in the even order.
-/

namespace SerreMarkov.RationalClifford

open CliffordOrder IntegralOrder Matrix

theorem rational_even_order_invariant_lattice
    (r : Generators RealMat2) (v : Fin 8 → RatMat2)
    (hv : ∀ i, rationalMatrixCast (v i) = evenMonomial r i) :
    ∃ L : Submodule ℤ (Fin 2 → ℚ),
      L.FG ∧ Submodule.span ℚ (L : Set (Fin 2 → ℚ)) = ⊤ ∧
      Module.finrank ℤ L = 2 ∧
      ∀ B : RatMat2, rationalMatrixCast B ∈ evenSpan r →
        ∀ x : Fin 2 → ℚ, x ∈ L → B *ᵥ x ∈ L := by
  let O := rationalOrder r v hv
  refine ⟨lattice O, lattice_fg O, lattice_spans O, lattice_rank O, ?_⟩
  intro B hB x hx
  have hm : B ∈ O :=
    (mem_liftedSpan_iff rationalMatrixCast rationalMatrixCast_injective r v hv B).mpr hB
  exact lattice_stable O ⟨B, hm⟩ hx

/-- All rational elements of the even Clifford order have integer matrices
in one rational basis. -/
theorem rational_even_order_integral_representation
    (r : Generators RealMat2) (v : Fin 8 → RatMat2)
    (hv : ∀ i, rationalMatrixCast (v i) = evenMonomial r i) :
    ∃ b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ),
      ∀ B : RatMat2, rationalMatrixCast B ∈ evenSpan r →
        ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
          LinearMap.toMatrix b b (Matrix.mulVecLin B) =
            Z.map (Int.cast : ℤ → ℚ) := by
  let O := rationalOrder r v hv
  obtain ⟨b, hb⟩ := exists_integral_representation O
  refine ⟨b, fun B hB => ?_⟩
  have hm : B ∈ O :=
    (mem_liftedSpan_iff rationalMatrixCast rationalMatrixCast_injective r v hv B).mpr hB
  exact hb ⟨B, hm⟩

/-- Every even product of the actual square-root-normalized half-turns has
a rational lift preserving one rank-two integer lattice. -/
theorem normalized_even_words_invariant_lattice (D : NormedClifford.Data) :
    ∃ L : Submodule ℤ (Fin 2 → ℚ),
      L.FG ∧ Submodule.span ℚ (L : Set (Fin 2 → ℚ)) = ⊤ ∧
      Module.finrank ℤ L = 2 ∧
      ∀ w : List (Fin 4), Even w.length →
        ∃ B : RatMat2,
          rationalMatrixCast B = wordProduct (NormedClifford.generators D) w ∧
          ∀ x : Fin 2 → ℚ, x ∈ L → B *ᵥ x ∈ L := by
  obtain ⟨L, hfg, hspan, hrank, hstable⟩ :=
    rational_even_order_invariant_lattice (NormedClifford.generators D)
      (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D)
  refine ⟨L, hfg, hspan, hrank, fun w hw => ?_⟩
  obtain ⟨B, _, hB⟩ := even_word_has_lift rationalMatrixCast (NormedClifford.generators D)
    (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D) w hw
  refine ⟨B, hB, hstable B ?_⟩
  rw [hB]
  exact even_word_mem (NormedClifford.generators D) w hw

/-- One rational basis makes every even word an integer matrix; the square
root used to define individual half-turns has disappeared from the result. -/
theorem normalized_even_words_integral_representation (D : NormedClifford.Data) :
    ∃ b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ),
      ∀ w : List (Fin 4), Even w.length →
        ∃ B : RatMat2, ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
          rationalMatrixCast B = wordProduct (NormedClifford.generators D) w ∧
          LinearMap.toMatrix b b (Matrix.mulVecLin B) =
            Z.map (Int.cast : ℤ → ℚ) := by
  obtain ⟨b, hb⟩ := rational_even_order_integral_representation (NormedClifford.generators D)
    (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D)
  refine ⟨b, fun w hw => ?_⟩
  obtain ⟨B, _, hB⟩ := even_word_has_lift rationalMatrixCast (NormedClifford.generators D)
    (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D) w hw
  have hm : rationalMatrixCast B ∈ evenSpan (NormedClifford.generators D) := by
    rw [hB]
    exact even_word_mem (NormedClifford.generators D) w hw
  obtain ⟨Z, hZ⟩ := hb B hm
  exact ⟨B, Z, hB, hZ⟩

theorem determinant_of_integral_representation
    (b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ)) (B : RatMat2)
    (Z : Matrix (Fin 2) (Fin 2) ℤ)
    (hZ : LinearMap.toMatrix b b (Matrix.mulVecLin B) =
      Z.map (Int.cast : ℤ → ℚ)) : (Z.det : ℚ) = B.det := by
  calc
    (Z.det : ℚ) = (Z.map (Int.cast : ℤ → ℚ)).det :=
      (Int.castRingHom ℚ).map_det Z
    _ = (LinearMap.toMatrix b b (Matrix.mulVecLin B)).det :=
      congrArg Matrix.det hZ.symm
    _ = LinearMap.det (Matrix.mulVecLin B) := LinearMap.det_toMatrix b _
    _ = B.det := by rw [← Matrix.toLin'_apply', LinearMap.det_toLin']

/-- The common integer matrices for all even normalized words have
determinant one, completing the arithmetic conclusion in one basis. -/
theorem normalized_even_words_integral_SL2_representation (D : NormedClifford.Data) :
    ∃ b : Module.Basis (Fin 2) ℚ (Fin 2 → ℚ),
      ∀ w : List (Fin 4), Even w.length →
        ∃ B : RatMat2, ∃ Z : Matrix (Fin 2) (Fin 2) ℤ,
          rationalMatrixCast B = wordProduct (NormedClifford.generators D) w ∧
          LinearMap.toMatrix b b (Matrix.mulVecLin B) =
            Z.map (Int.cast : ℤ → ℚ) ∧ Z.det = 1 := by
  obtain ⟨b, hb⟩ := normalized_even_words_integral_representation D
  refine ⟨b, fun w hw => ?_⟩
  obtain ⟨B, Z, hB, hZ⟩ := hb w hw
  refine ⟨B, Z, hB, hZ, ?_⟩
  have hBd_real : (B.det : ℝ) = 1 := by
    calc
      (B.det : ℝ) = (rationalMatrixCast B).det := (Rat.castHom ℝ).map_det B
      _ = 1 := by rw [hB, NormedClifford.word_determinant]
  have hBd : B.det = 1 := by exact_mod_cast hBd_real
  have hZd : (Z.det : ℚ) = 1 :=
    (determinant_of_integral_representation b B Z hZ).trans hBd
  exact_mod_cast hZd

@[simp] theorem rationalMatrixCast_intMatrix (Z : Matrix (Fin 2) (Fin 2) ℤ) :
    rationalMatrixCast (Z.map (Int.cast : ℤ → ℚ)) =
      Z.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp

/-- One rational change of coordinates conjugates every even normalized
word into `SL₂(ℤ)`. The same inverse pair is used for all words. -/
theorem normalized_even_words_integral_SL2_conjugation (D : NormedClifford.Data) :
    ∃ C Cinv : RatMat2, C*Cinv = 1 ∧ Cinv*C = 1 ∧
      ∀ w : List (Fin 4), Even w.length →
        ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det = 1 ∧
          rationalMatrixCast Cinv * wordProduct (NormedClifford.generators D) w *
            rationalMatrixCast C = Z.map (Int.cast : ℤ → ℝ) := by
  let O := NormedClifford.order D
  obtain ⟨C, Cinv, hCC, hIC, hconj⟩ := exists_integral_conjugation O
  refine ⟨C, Cinv, hCC, hIC, fun w hw => ?_⟩
  obtain ⟨B, hm, hB⟩ := even_word_has_lift rationalMatrixCast (NormedClifford.generators D)
    (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D) w hw
  have hO : B ∈ O := hm
  obtain ⟨Z, hZ⟩ := hconj ⟨B, hO⟩
  have hBd_real : (B.det : ℝ) = 1 := by
    calc
      (B.det : ℝ) = (rationalMatrixCast B).det := (Rat.castHom ℝ).map_det B
      _ = 1 := by rw [hB, NormedClifford.word_determinant]
  have hBd : B.det = 1 := by exact_mod_cast hBd_real
  have hCdet : Cinv.det * C.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hIC
  have hZd : (Z.det : ℚ) = 1 := by
    calc
      (Z.det : ℚ) = (Z.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det Z
      _ = (Cinv * B * C).det := congrArg Matrix.det hZ.symm
      _ = 1 := by simp only [Matrix.det_mul, hBd, mul_one, hCdet]
  refine ⟨Z, by exact_mod_cast hZd, ?_⟩
  calc
    _ = rationalMatrixCast (Cinv * B * C) := by rw [map_mul, map_mul, hB]
    _ = _ := by rw [hZ, rationalMatrixCast_intMatrix]

/-- The common rational conjugation can be chosen with positive determinant. -/
theorem normalized_even_words_integral_SL2_positive_conjugation (D : NormedClifford.Data) :
    ∃ C Cinv : RatMat2, 0 < C.det ∧ C*Cinv = 1 ∧ Cinv*C = 1 ∧
      ∀ w : List (Fin 4), Even w.length →
        ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det = 1 ∧
          rationalMatrixCast Cinv * wordProduct (NormedClifford.generators D) w *
            rationalMatrixCast C = Z.map (Int.cast : ℤ → ℝ) := by
  let O := NormedClifford.order D
  obtain ⟨C, Cinv, hpos, hCC, hIC, hconj⟩ := exists_integral_conjugation_positive O
  refine ⟨C, Cinv, hpos, hCC, hIC, fun w hw => ?_⟩
  obtain ⟨B, hm, hB⟩ := even_word_has_lift rationalMatrixCast (NormedClifford.generators D)
    (NormedClifford.rationalEvenMonomial D) (NormedClifford.cast_rationalEvenMonomial D) w hw
  have hO : B ∈ O := hm
  obtain ⟨Z, hZ⟩ := hconj ⟨B, hO⟩
  have hBd_real : (B.det : ℝ) = 1 := by
    calc
      (B.det : ℝ) = (rationalMatrixCast B).det := (Rat.castHom ℝ).map_det B
      _ = 1 := by rw [hB, NormedClifford.word_determinant]
  have hBd : B.det = 1 := by exact_mod_cast hBd_real
  have hCdet : Cinv.det * C.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hIC
  have hZd : (Z.det : ℚ) = 1 := by
    calc
      (Z.det : ℚ) = (Z.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det Z
      _ = (Cinv * B * C).det := congrArg Matrix.det hZ.symm
      _ = 1 := by simp only [Matrix.det_mul, hBd, mul_one, hCdet]
  refine ⟨Z, by exact_mod_cast hZd, ?_⟩
  calc
    _ = rationalMatrixCast (Cinv * B * C) := by rw [map_mul, map_mul, hB]
    _ = _ := by rw [hZ, rationalMatrixCast_intMatrix]

end SerreMarkov.RationalClifford
