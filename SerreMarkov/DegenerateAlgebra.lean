import SerreMarkov.Matrix
import SerreMarkov.DegenerateNormalForm

/-!
# Algebraic exclusion of Jordan type [3, 1]

This module gives a polynomial proof that third-order nilpotence for a
three-dimensional-type rank-four Euler matrix already implies square-zero.
The cofactor certificates avoid any classification or geometric assumptions.
-/

namespace SerreMarkov

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply
set_option maxHeartbeats 6000000
set_option maxRecDepth 6000

/-- The explicit adjugate of the symmetric Euler form. -/
def symmetricCofactors (z : Six) : Mat4 :=
  !![-2*z.d^2+2*z.d*z.e*z.f-2*z.e^2-2*z.f^2+8,
     z.a*z.f^2-4*z.a+2*z.b*z.d-z.b*z.e*z.f-z.c*z.d*z.f+2*z.c*z.e,
     2*z.a*z.d-z.a*z.e*z.f+z.b*z.e^2-4*z.b-z.c*z.d*z.e+2*z.c*z.f,
     -z.a*z.d*z.f+2*z.a*z.e-z.b*z.d*z.e+2*z.b*z.f+z.c*z.d^2-4*z.c;
     z.a*z.f^2-4*z.a+2*z.b*z.d-z.b*z.e*z.f-z.c*z.d*z.f+2*z.c*z.e,
     -2*z.b^2+2*z.b*z.c*z.f-2*z.c^2-2*z.f^2+8,
     2*z.a*z.b-z.a*z.c*z.f-z.b*z.c*z.e+z.c^2*z.d-4*z.d+2*z.e*z.f,
     -z.a*z.b*z.f+2*z.a*z.c+z.b^2*z.e-z.b*z.c*z.d+2*z.d*z.f-4*z.e;
     2*z.a*z.d-z.a*z.e*z.f+z.b*z.e^2-4*z.b-z.c*z.d*z.e+2*z.c*z.f,
     2*z.a*z.b-z.a*z.c*z.f-z.b*z.c*z.e+z.c^2*z.d-4*z.d+2*z.e*z.f,
     -2*z.a^2+2*z.a*z.c*z.e-2*z.c^2-2*z.e^2+8,
     z.a^2*z.f-z.a*z.b*z.e-z.a*z.c*z.d+2*z.b*z.c+2*z.d*z.e-4*z.f;
     -z.a*z.d*z.f+2*z.a*z.e-z.b*z.d*z.e+2*z.b*z.f+z.c*z.d^2-4*z.c,
     -z.a*z.b*z.f+2*z.a*z.c+z.b^2*z.e-z.b*z.c*z.d+2*z.d*z.f-4*z.e,
     z.a^2*z.f-z.a*z.b*z.e-z.a*z.c*z.d+2*z.b*z.c+2*z.d*z.e-4*z.f,
     -2*z.a^2+2*z.a*z.b*z.d-2*z.b^2-2*z.d^2+8]

theorem symmetricForm_literal (z : Six) :
    symmetricForm z = !![2,z.a,z.b,z.c; z.a,2,z.d,z.e; z.b,z.d,2,z.f; z.c,z.e,z.f,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [symmetricForm, Matrix.add_apply, Matrix.transpose_apply] <;>
    norm_num [gram]

theorem symmetricCofactors_eq_adjugate (z : Six) :
    symmetricCofactors z = (symmetricForm z).adjugate := by
  rw [symmetricForm_literal]
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j
  · rw [Matrix.det_fin_three]
    change (-2*z.d^2 + 2*z.d*z.e*z.f - 2*z.e^2 - 2*z.f^2 + 8) = (-1 : ℤ)^0 * (2*2*2 - 2*z.f*z.f - z.d*z.d*2 + z.d*z.f*z.e + z.e*z.d*z.f - z.e*2*z.e)
    ring
  · rw [Matrix.det_fin_three]
    change (z.a*z.f^2 - 4*z.a + 2*z.b*z.d - z.b*z.e*z.f - z.c*z.d*z.f + 2*z.c*z.e) = (-1 : ℤ)^1 * (z.a*2*2 - z.a*z.f*z.f - z.b*z.d*2 + z.b*z.f*z.e + z.c*z.d*z.f - z.c*2*z.e)
    ring
  · rw [Matrix.det_fin_three]
    change (2*z.a*z.d - z.a*z.e*z.f + z.b*z.e^2 - 4*z.b - z.c*z.d*z.e + 2*z.c*z.f) = (-1 : ℤ)^2 * (z.a*z.d*2 - z.a*z.e*z.f - z.b*2*2 + z.b*z.e*z.e + z.c*2*z.f - z.c*z.d*z.e)
    ring
  · rw [Matrix.det_fin_three]
    change (-z.a*z.d*z.f + 2*z.a*z.e - z.b*z.d*z.e + 2*z.b*z.f + z.c*z.d^2 - 4*z.c) = (-1 : ℤ)^3 * (z.a*z.d*z.f - z.a*z.e*2 - z.b*2*z.f + z.b*z.e*z.d + z.c*2*2 - z.c*z.d*z.d)
    ring
  · rw [Matrix.det_fin_three]
    change (z.a*z.f^2 - 4*z.a + 2*z.b*z.d - z.b*z.e*z.f - z.c*z.d*z.f + 2*z.c*z.e) = (-1 : ℤ)^1 * (z.a*2*2 - z.a*z.f*z.f - z.d*z.b*2 + z.d*z.f*z.c + z.e*z.b*z.f - z.e*2*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (-2*z.b^2 + 2*z.b*z.c*z.f - 2*z.c^2 - 2*z.f^2 + 8) = (-1 : ℤ)^2 * (2*2*2 - 2*z.f*z.f - z.b*z.b*2 + z.b*z.f*z.c + z.c*z.b*z.f - z.c*2*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (2*z.a*z.b - z.a*z.c*z.f - z.b*z.c*z.e + z.c^2*z.d - 4*z.d + 2*z.e*z.f) = (-1 : ℤ)^3 * (2*z.d*2 - 2*z.e*z.f - z.b*z.a*2 + z.b*z.e*z.c + z.c*z.a*z.f - z.c*z.d*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (-z.a*z.b*z.f + 2*z.a*z.c + z.b^2*z.e - z.b*z.c*z.d + 2*z.d*z.f - 4*z.e) = (-1 : ℤ)^4 * (2*z.d*z.f - 2*z.e*2 - z.b*z.a*z.f + z.b*z.e*z.b + z.c*z.a*2 - z.c*z.d*z.b)
    ring
  · rw [Matrix.det_fin_three]
    change (2*z.a*z.d - z.a*z.e*z.f + z.b*z.e^2 - 4*z.b - z.c*z.d*z.e + 2*z.c*z.f) = (-1 : ℤ)^2 * (z.a*z.d*2 - z.a*z.f*z.e - 2*z.b*2 + 2*z.f*z.c + z.e*z.b*z.e - z.e*z.d*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (2*z.a*z.b - z.a*z.c*z.f - z.b*z.c*z.e + z.c^2*z.d - 4*z.d + 2*z.e*z.f) = (-1 : ℤ)^3 * (2*z.d*2 - 2*z.f*z.e - z.a*z.b*2 + z.a*z.f*z.c + z.c*z.b*z.e - z.c*z.d*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (-2*z.a^2 + 2*z.a*z.c*z.e - 2*z.c^2 - 2*z.e^2 + 8) = (-1 : ℤ)^4 * (2*2*2 - 2*z.e*z.e - z.a*z.a*2 + z.a*z.e*z.c + z.c*z.a*z.e - z.c*2*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (z.a^2*z.f - z.a*z.b*z.e - z.a*z.c*z.d + 2*z.b*z.c + 2*z.d*z.e - 4*z.f) = (-1 : ℤ)^5 * (2*2*z.f - 2*z.e*z.d - z.a*z.a*z.f + z.a*z.e*z.b + z.c*z.a*z.d - z.c*2*z.b)
    ring
  · rw [Matrix.det_fin_three]
    change (-z.a*z.d*z.f + 2*z.a*z.e - z.b*z.d*z.e + 2*z.b*z.f + z.c*z.d^2 - 4*z.c) = (-1 : ℤ)^3 * (z.a*z.d*z.f - z.a*2*z.e - 2*z.b*z.f + 2*2*z.c + z.d*z.b*z.e - z.d*z.d*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (-z.a*z.b*z.f + 2*z.a*z.c + z.b^2*z.e - z.b*z.c*z.d + 2*z.d*z.f - 4*z.e) = (-1 : ℤ)^4 * (2*z.d*z.f - 2*2*z.e - z.a*z.b*z.f + z.a*2*z.c + z.b*z.b*z.e - z.b*z.d*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (z.a^2*z.f - z.a*z.b*z.e - z.a*z.c*z.d + 2*z.b*z.c + 2*z.d*z.e - 4*z.f) = (-1 : ℤ)^5 * (2*2*z.f - 2*z.d*z.e - z.a*z.a*z.f + z.a*z.d*z.c + z.b*z.a*z.e - z.b*2*z.c)
    ring
  · rw [Matrix.det_fin_three]
    change (-2*z.a^2 + 2*z.a*z.b*z.d - 2*z.b^2 - 2*z.d^2 + 8) = (-1 : ℤ)^6 * (2*2*2 - 2*z.d*z.d - z.a*z.a*2 + z.a*z.d*z.b + z.b*z.a*z.d - z.b*2*z.b)
    ring

open Polynomial in
/-- A nilpotent adjugate vanishes as soon as the cube does in dimension four.
The proof uses the polynomial inverse of `tI-A` and evaluation at `t=0`. -/
theorem adjugate_zero_of_cube_charpoly (A : Mat4)
    (hp : A.charpoly = X^4) (h3 : A^3 = 0) : A.adjugate = 0 := by
  let B : Matrix (Fin 4) (Fin 4) ℤ[X] := Polynomial.C.mapMatrix A
  let P : Matrix (Fin 4) (Fin 4) ℤ[X] := A.charmatrix
  let T : Matrix (Fin 4) (Fin 4) ℤ[X] := (X : ℤ[X])^3 • 1 + (X : ℤ[X])^2 • B + (X : ℤ[X]) • (B^2)
  have hB3 : B^3 = 0 := by
    change (Polynomial.C.mapMatrix A)^3 = 0
    rw [← map_pow, h3, map_zero]
  have hP : P = (X : ℤ[X]) • 1 - B := by
    ext i j : 1
    by_cases hij : i = j <;>
      simp [P, B, Matrix.charmatrix, Matrix.scalar_apply, hij]
  have hprod : T * P = (X : ℤ[X])^4 • 1 := by
    rw [hP]
    simp only [T, Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, ← pow_succ, ← pow_two, hB3]
    module
  have hadj : P.adjugate * P = (X : ℤ[X])^4 • 1 := by
    rw [Matrix.adjugate_mul]
    change A.charpoly • 1 = _
    rw [hp]
  have hdet : P.det ≠ 0 := by
    change A.charpoly ≠ 0
    rw [hp]
    simp
  have hreg : IsLeftRegular P.det := by
    intro x y h
    exact mul_left_cancel₀ hdet h
  have heq : P.adjugate = T :=
    (Matrix.isRegular_of_isLeftRegular_det hreg).right (hadj.trans hprod.symm)
  let ev : ℤ[X] →+* ℤ := Polynomial.evalRingHom 0
  have hevP : ev.mapMatrix P = -A := by
    ext i j : 1
    by_cases hij : i = j <;>
      simp [ev, P, Matrix.charmatrix, Matrix.scalar_apply, hij]
  have hevT : ev.mapMatrix T = 0 := by
    ext i j
    by_cases hij : i = j <;>
      simp [ev, T, RingHom.mapMatrix_apply, Matrix.smul_apply, hij]
  have he := congrArg ev.mapMatrix heq
  rw [RingHom.map_adjugate, hevP, hevT] at he
  have hneg : (-A).adjugate = -A.adjugate := by
    have hn := Matrix.adjugate_smul (-1 : ℤ) A
    simpa using hn
  rw [hneg] at he
  exact neg_eq_zero.mp he


theorem cofactor_zero_of_cube_zero (z : Six) (hz : isSolution z)
    (h : shiftedSerre z ^ 3 = 0) : symmetricCofactors z = 0 := by
  have hp : (shiftedSerre z).charpoly = Polynomial.X^4 := by
    rw [shiftedSerre_charpoly, hz.1, hz.2]
    norm_num
  have ha := adjugate_zero_of_cube_charpoly (shiftedSerre z) hp h
  rw [symmetricCofactors_eq_adjugate, symmetricForm_eq,
    Matrix.adjugate_mul_distrib, ha, Matrix.zero_mul]

/-- First sum-of-squares cofactor certificate. -/
theorem cofactor_af_certificate (z : Six) :
    8*(z.a+z.f)^2 =
      -z.c^2*symmetricCofactors z 0 0 -
      (2*z.a+z.c*z.e)*symmetricCofactors z 0 1 +
      (2*z.b-z.c*z.f)*symmetricCofactors z 0 2 -
      4*symmetricCofactors z 1 1 +
      (2*z.a*z.f+2*z.b*z.e-2*z.c*z.d+8)*(q2 z+4) := by
  simp [symmetricCofactors, q2]
  ring

/-- Second sum-of-squares cofactor certificate. -/
theorem cofactor_cd_certificate (z : Six) :
    8*(z.c+z.d)^2 =
      (4-z.c^2)*symmetricCofactors z 0 0 +
      (2*z.a-z.c*z.e)*symmetricCofactors z 0 1 +
      (2*z.b-z.c*z.f)*symmetricCofactors z 0 2 -
      4*symmetricCofactors z 1 1 -
      4*z.d*symmetricCofactors z 1 2 -
      4*symmetricCofactors z 2 2 +
      (-2*z.a*z.f+2*z.b*z.e+2*z.c*z.d+8)*(q2 z+4) := by
  simp [symmetricCofactors, q2]
  ring

/-- The remaining scalar relation is also a sum-of-squares certificate. -/
theorem cofactor_relation_certificate (z : Six)
    (haf : z.f = -z.a) (hcd : z.c = -z.d) :
    2*(z.b-z.e-z.a*z.d)^2 =
      -symmetricCofactors z 1 1 - symmetricCofactors z 0 0 +
      z.d*symmetricCofactors z 0 3 +
      (4-z.d^2)*(q2 z+4) := by
  simp [symmetricCofactors, q2, haf, hcd]
  ring

theorem cofactor_zero_reduced (z : Six)
    (hc : symmetricCofactors z = 0) (hq : q2 z = -4) :
    z = reducedDegenerate z.a z.b z.d := by
  have h1 := cofactor_af_certificate z
  have h2 := cofactor_cd_certificate z
  rw [hc, hq] at h1 h2
  simp at h1 h2
  have haf : z.f = -z.a := by nlinarith [sq_nonneg (z.a+z.f)]
  have hcd : z.c = -z.d := by nlinarith [sq_nonneg (z.c+z.d)]
  have h3 := cofactor_relation_certificate z haf hcd
  rw [hc, hq] at h3
  simp at h3
  have he : z.e = z.b-z.a*z.d := by
    nlinarith [sq_nonneg (z.b-z.e-z.a*z.d)]
  ext <;> simp [reducedDegenerate, haf, hcd, he]

theorem reducedDegenerate_shiftedSerre (a b d : ℤ) :
    shiftedSerre (reducedDegenerate a b d) =
      !![-a^2+a*b*d-b^2-d^2+2, -a, -b, d;
         a, a*b*d-b^2-d^2+2, a*b-d, -b;
         -a*d+b, -a^2*d+a*b+d, 2-a^2, a;
         -d, -a*d+b, -a, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [shiftedSerre, serre, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.transpose_apply] <;>
    norm_num [gram, gramInverse, reducedDegenerate] <;> ring

/-- The square factors by the sole remaining scalar equation. -/
theorem reducedDegenerate_square (a b d : ℤ) :
    shiftedSerre (reducedDegenerate a b d) ^ 2 =
      (q2 (reducedDegenerate a b d)+4) •
      !![-a^2+a*b*d-b^2-d^2+1, -a, -b, d;
         a, a*b*d-b^2-d^2+1, a*b-d, -b;
         -a*d+b, -a^2*d+a*b+d, 1-a^2, a;
         -d, -a*d+b, -a, 1] := by
  rw [reducedDegenerate_shiftedSerre]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reducedDegenerate, q2, pow_two, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem square_zero_of_cofactor_zero_negative (z : Six)
    (hc : symmetricCofactors z = 0) (hq : q2 z = -4) :
    shiftedSerre z ^ 2 = 0 := by
  have hr := cofactor_zero_reduced z hc hq
  conv_lhs => rw [hr]
  rw [reducedDegenerate_square]
  rw [← hr, hq]
  simp

/-- First sign change, as an integral diagonal conjugation. -/
def firstSignMatrix : Mat4 := !![-1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

theorem firstSignMatrix_square : firstSignMatrix * firstSignMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstSignMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem shiftedSerre_eps1 (z : Six) :
    shiftedSerre (eps1 z) = firstSignMatrix * shiftedSerre z * firstSignMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [shiftedSerre, serre, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.transpose_apply] <;>
    simp [firstSignMatrix, gram, gramInverse, eps1] <;> ring

theorem shiftedSerre_eps1_pow (z : Six) (n : ℕ) :
    shiftedSerre (eps1 z) ^ n = firstSignMatrix * shiftedSerre z ^ n * firstSignMatrix := by
  induction n with
  | zero => simp [firstSignMatrix_square]
  | succ n ih =>
    rw [pow_succ, ih, shiftedSerre_eps1]
    calc
      firstSignMatrix * shiftedSerre z ^ n * firstSignMatrix *
        (firstSignMatrix * shiftedSerre z * firstSignMatrix) =
        firstSignMatrix * shiftedSerre z ^ n *
        (firstSignMatrix * firstSignMatrix) * shiftedSerre z * firstSignMatrix := by
          noncomm_ring
      _ = firstSignMatrix * shiftedSerre z ^ (n+1) * firstSignMatrix := by
        rw [firstSignMatrix_square]
        simp [pow_succ, Matrix.mul_assoc]

/-- The general degenerate Jordan-type exclusion from Section 7. -/
theorem cube_zero_implies_square_zero (z : Six) (hz : isSolution z)
    (h : shiftedSerre z ^ 3 = 0) : shiftedSerre z ^ 2 = 0 := by
  have hsign : q2 z = 4 ∨ q2 z = -4 := by
    have hs : q2 z ^ 2 = (4 : ℤ)^2 := by norm_num; exact hz.2
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
  rcases hsign with hq | hq
  · have he : isSolution (eps1 z) := by
      unfold isSolution
      rw [q1_eps1, q2_eps1]
      simpa [neg_sq] using hz
    have heq : q2 (eps1 z) = -4 := by rw [q2_eps1, hq]
    have he3 : shiftedSerre (eps1 z)^3 = 0 := by
      rw [shiftedSerre_eps1_pow, h]
      simp
    have he2 := square_zero_of_cofactor_zero_negative (eps1 z)
      (cofactor_zero_of_cube_zero (eps1 z) he he3) heq
    have hback := congrArg (fun A : Mat4 => firstSignMatrix * A * firstSignMatrix) he2
    rw [shiftedSerre_eps1_pow] at hback
    have hcancel : firstSignMatrix *
        (firstSignMatrix * shiftedSerre z ^ 2 * firstSignMatrix) * firstSignMatrix =
        shiftedSerre z ^ 2 := by
      calc
        _ = (firstSignMatrix * firstSignMatrix) * shiftedSerre z ^ 2 *
            (firstSignMatrix * firstSignMatrix) := by noncomm_ring
        _ = _ := by rw [firstSignMatrix_square]; simp
    simpa [hcancel] using hback
  · exact square_zero_of_cofactor_zero_negative z (cofactor_zero_of_cube_zero z hz h) hq

end SerreMarkov
