import SerreMarkov.CliffordOrder
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Descent of the integral Clifford order along an injective ring homomorphism

It suffices to lift the eight even basis monomials. The resulting integer
span maps onto the even Clifford order, is closed under multiplication, and
is finite as a module over the integers. The generators themselves need not
lift: this distinction allows rational even words of irrational half-turns.
-/

namespace SerreMarkov.RationalClifford

open CliffordOrder

variable {R S : Type*} [Ring R] [Ring S]

def liftedSpan (v : Fin 8 → R) : Submodule ℤ R :=
  Submodule.span ℤ (Set.range v)

theorem mapped_liftedSpan (f : R →+* S) (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) :
    (liftedSpan v).map f.toIntAlgHom.toLinearMap = evenSpan r := by
  rw [liftedSpan, Submodule.map_span]
  change Submodule.span ℤ (f '' Set.range v) =
    Submodule.span ℤ (Set.range (evenMonomial r))
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hv i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨v i, ⟨i, rfl⟩, hv i⟩

theorem mem_liftedSpan_iff (f : R →+* S) (hf : Function.Injective f)
    (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) (x : R) :
    x ∈ liftedSpan v ↔ f x ∈ evenSpan r := by
  rw [← mapped_liftedSpan f r v hv, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact hf he ▸ hy

theorem liftedSpan_mul_mem (f : R →+* S) (hf : Function.Injective f)
    (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) (x y : R)
    (hx : x ∈ liftedSpan v) (hy : y ∈ liftedSpan v) : x * y ∈ liftedSpan v := by
  apply (mem_liftedSpan_iff f hf r v hv (x*y)).mpr
  rw [map_mul]
  exact evenSpan_mul_mem r _ _
    ((mem_liftedSpan_iff f hf r v hv x).mp hx)
    ((mem_liftedSpan_iff f hf r v hv y).mp hy)

/-- The rational order obtained by descending the eight even monomials. -/
def liftedOrder (f : R →+* S) (hf : Function.Injective f)
    (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) : Subalgebra ℤ R where
  carrier := liftedSpan v
  zero_mem' := (liftedSpan v).zero_mem
  one_mem' := by
    apply (mem_liftedSpan_iff f hf r v hv 1).mpr
    simpa only [map_one] using evenMonomial_mem r 0
  add_mem' := (liftedSpan v).add_mem
  mul_mem' := liftedSpan_mul_mem f hf r v hv _ _
  algebraMap_mem' n := by
    apply (mem_liftedSpan_iff f hf r v hv _).mpr
    change f (n : R) ∈ evenSpan r
    rw [map_intCast]
    simpa only [zsmul_eq_mul, evenMonomial, mul_one] using
      (evenSpan r).smul_mem n (evenMonomial_mem r 0)

theorem liftedSpan_finitely_generated (v : Fin 8 → R) : (liftedSpan v).FG :=
  Submodule.fg_span (Set.finite_range v)

instance liftedOrder_finite (f : R →+* S) (hf : Function.Injective f)
    (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) :
    Module.Finite ℤ (liftedOrder f hf r v hv) := by
  change Module.Finite ℤ (liftedSpan v)
  exact Module.Finite.iff_fg.mpr (liftedSpan_finitely_generated v)

theorem mapped_liftedOrder (f : R →+* S) (hf : Function.Injective f)
    (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i) :
    (liftedOrder f hf r v hv).map f.toIntAlgHom = evenSubalgebra r := by
  apply Subalgebra.toSubmodule_injective
  rw [Subalgebra.map_toSubmodule]
  exact mapped_liftedSpan f r v hv

theorem even_word_has_lift (f : R →+* S) (r : Generators S) (v : Fin 8 → R)
    (hv : ∀ i, f (v i) = evenMonomial r i)
    (w : List (Fin 4)) (hw : Even w.length) :
    ∃ x, x ∈ liftedSpan v ∧ f x = wordProduct r w := by
  have hm := even_word_mem r w hw
  rw [← mapped_liftedSpan f r v hv, Submodule.mem_map] at hm
  exact hm

abbrev RatMat2 := Matrix (Fin 2) (Fin 2) ℚ
abbrev RealMat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The entrywise rational embedding of two-by-two matrices. -/
noncomputable def rationalMatrixCast : RatMat2 →+* RealMat2 := (Rat.castHom ℝ).mapMatrix

theorem rationalMatrixCast_injective : Function.Injective rationalMatrixCast :=
  Matrix.map_injective Rat.cast_injective

@[simp] theorem rationalMatrixCast_apply (B : RatMat2) (i j : Fin 2) :
    rationalMatrixCast B i j = (B i j : ℝ) := rfl

noncomputable abbrev rationalOrder (r : Generators RealMat2) (v : Fin 8 → RatMat2)
    (hv : ∀ i, rationalMatrixCast (v i) = evenMonomial r i) : Subalgebra ℤ RatMat2 :=
  liftedOrder rationalMatrixCast rationalMatrixCast_injective r v hv

end SerreMarkov.RationalClifford
