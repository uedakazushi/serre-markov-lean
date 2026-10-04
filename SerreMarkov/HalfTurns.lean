import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

namespace SerreMarkov
namespace HalfTurns

open Matrix
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

/-- The rational numerator of a normalized half-turn lift. -/
def numerator (A r d : ℚ) : Mat2 :=
  !![A*d, -(A*d^2+1)/r; A*r, -A*d]

theorem numerator_trace (A r d : ℚ) : (numerator A r d).trace = 0 := by
  simp [numerator, Matrix.trace, Fin.sum_univ_succ]

theorem numerator_det (A r d : ℚ) (hr : r ≠ 0) :
    (numerator A r d).det = A := by
  simp [numerator, Matrix.det_fin_two]
  field_simp
  ring

theorem numerator_square (A r d : ℚ) (hr : r ≠ 0) :
    numerator A r d * numerator A r d = (-A) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numerator, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- The 2-by-2 Clifford anticommutator identity requires only trace zero. -/
theorem anticommutator (U V : Mat2) (hU : U.trace = 0) (hV : V.trace = 0) :
    U*V + V*U = (U*V).trace • (1 : Mat2) := by
  have hu : U 1 1 = - U 0 0 := by
    simp [Matrix.trace, Fin.sum_univ_succ] at hU
    linarith
  have hv : V 1 1 = - V 0 0 := by
    simp [Matrix.trace, Fin.sum_univ_succ] at hV
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, hu, hv] <;> ring

/-- Riemann--Roch's scalar equation gives the integral trace used in the
even Clifford-order construction, without invoking any hyperbolic geometry. -/
theorem even_product_trace (A r s d e h : ℚ)
    (hA : A ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hRR : h*r*s = r^2+s^2+A*(r*e-s*d)^2) :
    ((1/A) • (numerator A r d * numerator A s e)).trace = -h := by
  simp [numerator, Matrix.trace, Fin.sum_univ_succ]
  field_simp
  nlinarith [hRR]

end HalfTurns
end SerreMarkov
