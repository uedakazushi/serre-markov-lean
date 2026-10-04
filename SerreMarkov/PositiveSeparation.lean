import SerreMarkov.PositiveIntegral

/-! # Arithmetic separation of positive exceptional roots

The rank-degree Riemann--Roch identity and the actual solution equation
exclude coincident roots without using a hyperbolic fundamental domain.
-/

namespace SerreMarkov.PositiveSeparation

open Matrix IntrinsicFrame IntrinsicSigns
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- Coincident symmetric rows force a nonpositive third minor sum.
This uses the actual quadratic solution equation. -/
private theorem row_equal_nonpositive (z : Six) (hquad : q2 z ^ 2 = 16)
    (i j : Fin 4) (hij : i < j)
    (hrow : ∀ k, symmetricForm z i k = symmetricForm z j k) :
    thirdMinorSum z ≤ 0 := by
  rcases z with ⟨a,b,c,d,e,f⟩
  have hq : q2 ⟨a,b,c,d,e,f⟩ = 4 ∨ q2 ⟨a,b,c,d,e,f⟩ = -4 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simpa only [show (4:ℤ)^2=16 by norm_num] using hquad
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have ha : a = 2 := by linarith only [h0,h1,h2,h3]
    have hb : b = d := by linarith only [h0,h1,h2,h3]
    have hc : c = e := by linarith only [h0,h1,h2,h3]
    subst a
    subst b
    subst c
    rcases hq with hq | hq
    · have hf : f = 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst f
      have hmarker : thirdMinorSum ⟨2, d, e, d, e, 2⟩ = -4*(d - e)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (d - e)]
    · have hf : f = -2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst f
      have hmarker : thirdMinorSum ⟨2, d, e, d, e, -2⟩ = -4*(d + e)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (d + e)]
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have ha : a = d := by linarith only [h0,h1,h2,h3]
    have hb : b = 2 := by linarith only [h0,h1,h2,h3]
    have hc : c = f := by linarith only [h0,h1,h2,h3]
    subst a
    subst b
    subst c
    rcases hq with hq | hq
    · have he : e = d*f - 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst e
      have hmarker : thirdMinorSum ⟨d, 2, f, d, d*f - 2, f⟩ = -4*(d - f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (d - f)]
    · have he : e = d*f + 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst e
      have hmarker : thirdMinorSum ⟨d, 2, f, d, d*f + 2, f⟩ = -4*(d + f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (d + f)]
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have ha : a = e := by linarith only [h0,h1,h2,h3]
    have hb : b = f := by linarith only [h0,h1,h2,h3]
    have hc : c = 2 := by linarith only [h0,h1,h2,h3]
    subst a
    subst b
    subst c
    rcases hq with hq | hq
    · have hd : d = 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst d
      have hmarker : thirdMinorSum ⟨e, f, 2, 2, e, f⟩ = -4*(e - f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (e - f)]
    · have hd : d = -2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst d
      have hmarker : thirdMinorSum ⟨e, f, 2, -2, e, f⟩ = -4*(e + f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (e + f)]
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have ha : a = b := by linarith only [h0,h1,h2,h3]
    have hd : d = 2 := by linarith only [h0,h1,h2,h3]
    have he : e = f := by linarith only [h0,h1,h2,h3]
    subst a
    subst d
    subst e
    rcases hq with hq | hq
    · have hc : c = 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst c
      have hmarker : thirdMinorSum ⟨b, b, 2, 2, f, f⟩ = -4*(b - f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (b - f)]
    · have hc : c = -2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst c
      have hmarker : thirdMinorSum ⟨b, b, -2, 2, f, f⟩ = -4*(b + f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (b + f)]
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have ha : a = c := by linarith only [h0,h1,h2,h3]
    have hd : d = f := by linarith only [h0,h1,h2,h3]
    have he : e = 2 := by linarith only [h0,h1,h2,h3]
    subst a
    subst d
    subst e
    rcases hq with hq | hq
    · have hb : b = c*f - 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst b
      have hmarker : thirdMinorSum ⟨c, c*f - 2, c, f, 2, f⟩ = -4*(c - f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (c - f)]
    · have hb : b = c*f + 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst b
      have hmarker : thirdMinorSum ⟨c, c*f + 2, c, f, 2, f⟩ = -4*(c + f)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (c + f)]
  · simp [symmetricForm,gram] at h0 h1 h2 h3
    have hb : b = c := by linarith only [h0,h1,h2,h3]
    have hd : d = e := by linarith only [h0,h1,h2,h3]
    have hf : f = 2 := by linarith only [h0,h1,h2,h3]
    subst b
    subst d
    subst f
    rcases hq with hq | hq
    · have ha : a = 2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst a
      have hmarker : thirdMinorSum ⟨2, c, c, e, e, 2⟩ = -4*(c - e)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (c - e)]
    · have ha : a = -2 := by dsimp [q2] at hq; nlinarith only [hq]
      subst a
      have hmarker : thirdMinorSum ⟨-2, c, c, e, e, 2⟩ = -4*(c + e)^2 := by
        dsimp [thirdMinorSum]; ring
      rw [hmarker]
      nlinarith only [sq_nonneg (c + e)]

/-- The same row obstruction without ordering the indices. -/
theorem distinct_rows_of_positive (z : Six) (hz : isSolution z)
    (hpos : 0 < thirdMinorSum z) (i j : Fin 4) (hij : i ≠ j) :
    ¬ (∀ k, symmetricForm z i k = symmetricForm z j k) := by
  intro hrow
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_le_of_gt hpos) (row_equal_nonpositive z hz.2 i j hlt hrow)
  · exact (not_le_of_gt hpos) (row_equal_nonpositive z hz.2 j i hgt (fun k => (hrow k).symm))

/-- A positive Riemann--Roch pair with pairing two has equal rank and degree. -/
theorem RR_pairing_two (A r s d e : ℤ) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hRR : 2*r*s = r^2+s^2+A*(r*e-s*d)^2) : r=s ∧ d=e := by
  have hmul : 0 ≤ A*(r*e-s*d)^2 := mul_nonneg hA.le (sq_nonneg _)
  have hrs : (r-s)^2=0 := by nlinarith only [hRR,hmul,sq_nonneg (r-s)]
  have hrs' : r=s := by nlinarith only [hrs]
  refine ⟨hrs',?_⟩
  have hd : (r*e-s*d)^2=0 := by nlinarith only [hRR,hA,hrs',sq_nonneg (r*e-s*d)]
  have hd' : r*e-s*d=0 := by nlinarith only [hd]
  rw [← hrs'] at hd'
  have heq : r*e = r*d := sub_eq_zero.mp hd'
  exact (mul_left_cancel₀ hr.ne' heq).symm

/-- Distinct positive-rank basis roots of a positive solution have integral
pairing at least three. No geometric distinct-center hypothesis is assumed. -/
theorem positive_basis_pair_ge_three {z : Six} (R : Frame z) (hz : isSolution z)
    (hA : 0 < A R) (i j : Fin 4) (hij : i ≠ j)
    (hri : 0 < basisRank R i) (hrj : 0 < basisRank R j) :
    3 ≤ symmetricForm z i j := by
  have hRR := basis_RiemannRoch R i j
  have hproduct : 0 < basisRank R i*basisRank R j := mul_pos hri hrj
  have hmul : 0 ≤ A R*(basisRank R i*basisDegree R j-basisRank R j*basisDegree R i)^2 :=
    mul_nonneg hA.le (sq_nonneg _)
  have htwo : 2 ≤ symmetricForm z i j := by
    nlinarith only [hRR,hproduct,hmul,sq_nonneg (basisRank R i-basisRank R j)]
  by_contra hthree
  have heq : symmetricForm z i j = 2 := by omega
  rw [heq] at hRR
  obtain ⟨hrank,hdegree⟩ := RR_pairing_two (A R) (basisRank R i) (basisRank R j)
    (basisDegree R i) (basisDegree R j) hA hri hrj hRR
  have hrow : ∀ k, symmetricForm z i k = symmetricForm z j k := by
    intro k
    have hRRi := basis_RiemannRoch R i k
    have hRRj := basis_RiemannRoch R j k
    rw [← hrank,← hdegree] at hRRj
    apply mul_right_cancel₀ (mul_ne_zero hri.ne' ?_)
    · simpa only [mul_assoc] using hRRi.trans hRRj.symm
    · exact frame_positive_rank_ne_zero R hA (Pi.single k 1) (standard_euler_square z k)
  exact distinct_rows_of_positive z hz ((frame_thirdMinorSum_pos_iff R).mpr hA) i j hij hrow

end SerreMarkov.PositiveSeparation
