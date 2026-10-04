import SerreMarkov.AdaptedOperator

/-!
# Necessity of the family lattice congruences

The proof uses explicit integral matrix entries. The cube of the adapted shifted
Serre operator forces the six outer zero entries, and the operator itself forces
the remaining triangular shape. No flag-classification theorem is assumed.
-/

namespace SerreMarkov

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

private theorem intertwine_pow (P Q B : Mat4) (h : B * P = Q * B) (n : ℕ) :
    B * P ^ n = Q ^ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        B * P ^ (n + 1) = (B * P ^ n) * P := by rw [pow_succ, Matrix.mul_assoc]
        _ = (Q ^ n * B) * P := by rw [ih]
        _ = Q ^ n * (Q * B) := by rw [Matrix.mul_assoc, h]
        _ = Q ^ (n + 1) * B := by rw [pow_succ, Matrix.mul_assoc]

theorem adapted_isometry_lower_shape (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hinter : B * adaptedN m y' = adaptedN m y * B) :
    ∃ s r a g b h k : ℤ, s ^ 2 = 1 ∧
      B = !![s, 0, 0, 0; r, s, 0, 0; a, g, s, 0; b, h, k, s] := by
  have hcube := intertwine_pow (adaptedN m y') (adaptedN m y) B hinter 3
  rw [adaptedN_cube, adaptedN_cube] at hcube
  have hk : (-2 * m ^ 2 : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hm)
  have hb03 : B 0 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 0 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hm] using h
  have hb13 : B 1 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 1 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hm] using h
  have hb23 : B 2 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 2 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hm] using h
  have hb01 : B 0 1 = 0 := by
    have h := congrArg (fun A : Mat4 => A 3 1) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hm] using h.symm
  have hb02 : B 0 2 = 0 := by
    have h := congrArg (fun A : Mat4 => A 3 2) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hm] using h.symm
  have hb33 : B 3 3 = B 0 0 := by
    have h := congrArg (fun A : Mat4 => A 3 0) hcube
    have h' : B 3 3 * (-2 * m ^ 2) = (-2 * m ^ 2) * B 0 0 := by
      simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four] using h
    have hh : (-2 * m ^ 2) * (B 3 3 - B 0 0) = 0 := by
      calc
        (-2 * m ^ 2) * (B 3 3 - B 0 0) =
          B 3 3 * (-2 * m ^ 2) - (-2 * m ^ 2) * B 0 0 := by ring
        _ = 0 := sub_eq_zero.mpr h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hk)
  have hb12 : B 1 2 = 0 := by
    have h := congrArg (fun A : Mat4 => A 1 1) hinter
    simp [adaptedN, Matrix.mul_apply, Fin.sum_univ_four, hb01, hb13] at h
    linarith
  have hb22 : B 2 2 = B 1 1 := by
    have h := congrArg (fun A : Mat4 => A 2 1) hinter
    simp [adaptedN, Matrix.mul_apply, Fin.sum_univ_four, hb01, hb23] at h
    linarith
  have hb11 : B 1 1 = B 0 0 := by
    have h := congrArg (fun A : Mat4 => A 1 0) hinter
    simp [adaptedN, Matrix.mul_apply, Fin.sum_univ_four, hb12, hb13] at h
    have hh : m * (B 1 1 - B 0 0) = 0 := by
      calc
        m * (B 1 1 - B 0 0) = B 1 1 * m - m * B 0 0 := by ring
        _ = 0 := sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hm)
  have hshape : B =
      !![B 0 0, 0, 0, 0;
         B 1 0, B 0 0, 0, 0;
         B 2 0, B 2 1, B 0 0, 0;
         B 3 0, B 3 1, B 3 2, B 0 0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hb01, hb02, hb03, hb11, hb12, hb13, hb22, hb23, hb33]
  have hd : B.det = (B 0 0) ^ 4 := by
    rw [hshape, Matrix.det_succ_row_zero]
    simp [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_four, Fin.succAbove]
    ring
  have hs4 : (B 0 0) ^ 4 = 1 := by
    rcases hdet with h | h
    · exact hd.symm.trans h
    · rw [hd] at h
      nlinarith [sq_nonneg ((B 0 0) ^ 2)]
  have hs2 : (B 0 0) ^ 2 = 1 := by
    have hf : ((B 0 0) ^ 2 - 1) * ((B 0 0) ^ 2 + 1) = 0 := by nlinarith [hs4]
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · nlinarith [sq_nonneg (B 0 0)]
  exact ⟨B 0 0, B 1 0, B 2 0, B 2 1, B 3 0, B 3 1, B 3 2, hs2, hshape⟩

/-- Every integral adapted isometry forces the two simultaneous congruences.
This theorem applies to all nonzero integer moduli, including even moduli. -/
theorem adapted_divisibility_of_isometry (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * adaptedGram m y * B = adaptedGram m y') :
    ∃ t : ℤ, m ∣ y - y' - 2 * t ∧ m ∣ t * (t - y) := by
  have hinter := adaptedN_intertwine m y y' B hdet hcong
  obtain ⟨s, r, a, g, b, h, k, hs2, hshape⟩ :=
    adapted_isometry_lower_shape m y y' hm B hdet hinter
  have hnorm := congrArg (fun A : Mat4 => A 0 0) hcong
  simp [hshape, adaptedGram, Matrix.mul_apply, Fin.sum_univ_four] at hnorm
  have hrel := congrArg (fun A : Mat4 => A 2 0) hinter
  simp [hshape, adaptedN, Matrix.mul_apply, Fin.sum_univ_four] at hrel
  have hsrel := congrArg (fun v : ℤ => s * v) hrel
  ring_nf at hsrel
  rw [hs2] at hsrel
  have ht : y - y' - 2 * (-s * r) = m * (s * g) := by linarith [hsrel]
  have hnorm' : r ^ 2 + s * r * y = m * (y' - y - r * s + s * a) := by
    have hnorms := hnorm
    ring_nf at hnorms
    rw [hs2] at hnorms
    nlinarith [hnorms]
  refine ⟨-s * r, ⟨s * g, ht⟩, ?_⟩
  refine ⟨y' - y - r * s + s * a, ?_⟩
  calc
    (-s * r) * (-s * r - y) = s ^ 2 * r ^ 2 + s * r * y := by ring
    _ = r ^ 2 + s * r * y := by rw [hs2]; ring
    _ = m * (y' - y - r * s + s * a) := hnorm'

theorem family_divisibility_of_isometry (m y y' : ℤ) (hm : m ≠ 0) (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) :
    ∃ t : ℤ, m ∣ y - y' - 2 * t ∧ m ∣ t * (t - y) := by
  let T := adaptedBasisInverse y * B * adaptedBasis y'
  have hTdet : T.det = B.det := by
    simp [T, Matrix.det_mul, adaptedBasisInverse_det, adaptedBasis_det]
  have hTcong : Tᵀ * adaptedGram m y * T = adaptedGram m y' := by
    calc
      Tᵀ * adaptedGram m y * T =
        (adaptedBasis y')ᵀ * Bᵀ *
          ((adaptedBasisInverse y)ᵀ * adaptedGram m y * adaptedBasisInverse y) *
          B * adaptedBasis y' := by
        simp only [T, Matrix.transpose_mul]
        noncomm_ring
      _ = (adaptedBasis y')ᵀ * Bᵀ * gram (family (m-y) y) * B * adaptedBasis y' := by
        rw [← adaptedBasis_congruence m y]
        have hmid : (adaptedBasisInverse y)ᵀ *
            ((adaptedBasis y)ᵀ * gram (family (m-y) y) * adaptedBasis y) *
            adaptedBasisInverse y = gram (family (m-y) y) := by
          calc
            _ = (adaptedBasis y * adaptedBasisInverse y)ᵀ *
                gram (family (m-y) y) * (adaptedBasis y * adaptedBasisInverse y) := by
                  rw [Matrix.transpose_mul]
                  noncomm_ring
            _ = gram (family (m-y) y) := by rw [adaptedBasis_mul_inverse]; simp
        rw [hmid]
      _ = adaptedGram m y' := by
        calc
          _ = (adaptedBasis y')ᵀ *
              (Bᵀ * gram (family (m-y) y) * B) * adaptedBasis y' := by noncomm_ring
          _ = adaptedGram m y' := by rw [hcong, adaptedBasis_congruence]
  exact adapted_divisibility_of_isometry m y y' hm T (hTdet ▸ hdet) hTcong

/-- Complete lattice-isometry criterion, independent of mutation classification. -/
theorem family_isometry_iff_divisibility (m y y' : ℤ) (hm : m ≠ 0) :
    (∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
      Bᵀ * gram (family (m-y) y) * B = gram (family (m-y') y')) ↔
    (∃ t : ℤ, m ∣ y - y' - 2 * t ∧ m ∣ t * (t - y)) := by
  constructor
  · rintro ⟨B, hdet, hcong⟩
    exact family_divisibility_of_isometry m y y' hm B hdet hcong
  · intro h
    obtain ⟨B, hdet, hcong⟩ := family_isometry_of_divisibility m y y' h
    exact ⟨B, Or.inl hdet, hcong⟩

theorem congruenceWitness_of_integer_congruences (m : ℕ) (y y' : ℤ)
    (h : ∃ t : ℤ, (m : ℤ) ∣ y - y' - 2 * t ∧ (m : ℤ) ∣ t * (t - y)) :
    CongruenceWitness (y : ZMod m) (y' : ZMod m) := by
  obtain ⟨t, ht, hz⟩ := h
  have ht0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (y - y' - 2 * t) m).2 ht
  have hz0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (t * (t - y)) m).2 hz
  push_cast at ht0 hz0
  refine ⟨(t : ZMod m), ?_, hz0⟩
  apply (sub_eq_zero.mp ?_).symm
  calc
    (y : ZMod m) - 2 * (t : ZMod m) - (y' : ZMod m) =
      (y : ZMod m) - (y' : ZMod m) - 2 * (t : ZMod m) := by ring
    _ = 0 := ht0

theorem square_of_integer_congruences (m : ℕ) (y y' : ℤ)
    (h : ∃ t : ℤ, (m : ℤ) ∣ y - y' - 2 * t ∧ (m : ℤ) ∣ t * (t - y)) :
    (y' : ZMod m) ^ 2 = (y : ZMod m) ^ 2 := by
  obtain ⟨t, ht, hz⟩ := congruenceWitness_of_integer_congruences m y y' h
  rw [ht]
  calc
    ((y : ZMod m) - 2 * t) ^ 2 = (y : ZMod m) ^ 2 + 4 * (t * (t - y)) := by ring
    _ = (y : ZMod m) ^ 2 := by rw [hz]; ring

/-- For odd moduli, equality of squares is the complete integral lattice
isometry criterion, without any mutation-classification input. -/
theorem family_isometry_iff_odd_square (m : ℕ) (hm : Odd m) (y y' : ℤ) :
    (∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
      Bᵀ * gram (family ((m : ℤ)-y) y) * B = gram (family ((m : ℤ)-y') y')) ↔
      (y' : ZMod m) ^ 2 = (y : ZMod m) ^ 2 := by
  have hmne : m ≠ 0 := by rintro rfl; simp at hm
  have hmi : (m : ℤ) ≠ 0 := by exact_mod_cast hmne
  constructor
  · rintro ⟨B, hd, hc⟩
    exact square_of_integer_congruences m y y'
      (family_divisibility_of_isometry m y y' hmi B hd hc)
  · intro hs
    obtain ⟨B, hd, hc⟩ := family_isometry_of_odd_square m hm y y' hs
    exact ⟨B, Or.inl hd, hc⟩

/-- Equality of squares modulo an even modulus need not give a lattice
isometry. Both the square equality and the nonexistence are kernel proved. -/
theorem family_even_square_counterexample :
    (0 : ZMod 4) ^ 2 = (2 : ZMod 4) ^ 2 ∧
      ¬(∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
        Bᵀ * gram (family 4 0) * B = gram (family 2 2)) := by
  refine ⟨even_modulus_counterexample.1, ?_⟩
  rintro ⟨B, hd, hc⟩
  have h : ∃ t : ℤ, (4 : ℤ) ∣ 0 - 2 - 2 * t ∧ (4 : ℤ) ∣ t * (t - 0) := by
    apply family_divisibility_of_isometry 4 0 2 (by norm_num) B hd
    simpa using hc
  exact even_modulus_counterexample.2 (congruenceWitness_of_integer_congruences 4 0 2 h)

theorem adapted_positive_totals_eq_of_isometry (m m' y y' : ℤ)
    (hm : 0 < m) (hm' : 0 < m') (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * adaptedGram m y * B = adaptedGram m' y') : m = m' := by
  have hinter := adaptedN_intertwine_totals m m' y y' B hdet hcong
  have hcube := intertwine_pow (adaptedN m' y') (adaptedN m y) B hinter 3
  rw [adaptedN_cube, adaptedN_cube] at hcube
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmne' : m' ≠ 0 := ne_of_gt hm'
  have hb03 : B 0 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 0 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hmne'] using h
  have hb13 : B 1 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 1 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hmne'] using h
  have hb23 : B 2 3 = 0 := by
    have h := congrArg (fun A : Mat4 => A 2 0) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hmne'] using h
  have hb01 : B 0 1 = 0 := by
    have h := congrArg (fun A : Mat4 => A 3 1) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hmne] using h.symm
  have hb02 : B 0 2 = 0 := by
    have h := congrArg (fun A : Mat4 => A 3 2) hcube
    simpa [adaptedCube, Matrix.mul_apply, Fin.sum_univ_four, mul_eq_zero, hmne] using h.symm
  have hb12 : B 1 2 = 0 := by
    have h := congrArg (fun A : Mat4 => A 1 1) hinter
    simp [adaptedN, Matrix.mul_apply, Fin.sum_univ_four, hb01, hb13] at h
    linarith
  have hshape : B =
      !![B 0 0, 0, 0, 0;
         B 1 0, B 1 1, 0, 0;
         B 2 0, B 2 1, B 2 2, 0;
         B 3 0, B 3 1, B 3 2, B 3 3] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hb01, hb02, hb03, hb12, hb13, hb23]
  have hd : B.det = B 0 0 * B 1 1 * B 2 2 * B 3 3 := by
    rw [hshape, Matrix.det_succ_row_zero]
    simp [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_four, Fin.succAbove]
    ring
  have hu : IsUnit (B 0 0 * B 1 1 * B 2 2 * B 3 3) := by
    rw [← hd]
    exact Int.isUnit_iff.mpr hdet
  have hu01 : IsUnit (B 0 0 * B 1 1) :=
    (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hu).1).1
  have hu0 : IsUnit (B 0 0) := (IsUnit.mul_iff.mp hu01).1
  have hu1 : IsUnit (B 1 1) := (IsUnit.mul_iff.mp hu01).2
  have hrel := congrArg (fun A : Mat4 => A 1 0) hinter
  simp [adaptedN, Matrix.mul_apply, Fin.sum_univ_four, hb12, hb13] at hrel
  rcases Int.isUnit_eq_one_or hu0 with hs | hs <;>
    rcases Int.isUnit_eq_one_or hu1 with ht | ht <;>
    rw [hs, ht] at hrel <;> linarith

/-- The positive total parameter is an invariant of the integral Euler lattice. -/
theorem family_positive_totals_eq_of_isometry (m m' y y' : ℤ)
    (hm : 0 < m) (hm' : 0 < m') (B : Mat4)
    (hdet : B.det = 1 ∨ B.det = -1)
    (hcong : Bᵀ * gram (family (m-y) y) * B = gram (family (m'-y') y')) : m = m' := by
  obtain ⟨T, hd, hc⟩ := family_isometry_to_adapted m m' y y' B hdet hcong
  exact adapted_positive_totals_eq_of_isometry m m' y y' hm hm' T hd hc

/-- Complete isometry classification of all family lattices with positive total
parameter, including even totals. -/
theorem family_positive_isometry_iff (m m' y y' : ℤ) (hm : 0 < m) (hm' : 0 < m') :
    (∃ B : Mat4, (B.det = 1 ∨ B.det = -1) ∧
      Bᵀ * gram (family (m-y) y) * B = gram (family (m'-y') y')) ↔
      m = m' ∧ (∃ t : ℤ, m ∣ y - y' - 2 * t ∧ m ∣ t * (t-y)) := by
  constructor
  · rintro ⟨B, hd, hc⟩
    have heq := family_positive_totals_eq_of_isometry m m' y y' hm hm' B hd hc
    refine ⟨heq, ?_⟩
    rw [← heq] at hc
    exact family_divisibility_of_isometry m y y' (ne_of_gt hm) B hd hc
  · rintro ⟨heq, h⟩
    rw [← heq]
    exact (family_isometry_iff_divisibility m y y' (ne_of_gt hm)).mpr h

end SerreMarkov
