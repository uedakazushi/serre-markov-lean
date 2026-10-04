import SerreMarkov.Mutations

/-! # A forbidden sign chamber in the integer solution equations

This elementary obstruction uses the actual first polynomial equation.
It is independent of regular classification and of local descent.
-/

namespace SerreMarkov.SignChambers

theorem q1_ge_square_sum_of_negative_tail (z : Six)
    (ha : 0 ≤ z.a) (hb : 0 ≤ z.b) (hc : 0 ≤ z.c)
    (hd : z.d ≤ 0) (he : z.e ≤ 0) (hf : z.f ≤ 0) :
    z.a^2+z.b^2+z.c^2+z.d^2+z.e^2+z.f^2 ≤ q1 z := by
  have hp : 0 ≤ z.a*z.c*z.d*z.f :=
    mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hc) hd) hf
  have h1 : z.a*z.b*z.d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) hd
  have h2 : z.a*z.c*z.e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hc) he
  have h3 : z.b*z.c*z.f ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hc) hf
  have h4 : z.d*z.e*z.f ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos hd he) hf
  dsimp [q1]
  linarith only [hp, h1, h2, h3, h4]

theorem solution_not_all_negative_tail (z : Six) (hz : isSolution z)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : z.e ≤ -2) (hf : z.f ≤ -2) : False := by
  have h := q1_ge_square_sum_of_negative_tail z (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [hz.1] at h
  nlinarith only [h, ha, hb, hc, hd, he, hf,
    sq_nonneg (z.a-2), sq_nonneg (z.b-2), sq_nonneg (z.c-2),
    sq_nonneg (z.d+2), sq_nonneg (z.e+2), sq_nonneg (z.f+2)]

end SerreMarkov.SignChambers
