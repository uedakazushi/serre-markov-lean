import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
Norm-two vectors are determined up to sign by their reflection matrices.
The result does not require the bilinear form to be nondegenerate or symmetric.
-/

namespace SerreMarkov.ReflectionRoots

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def rootNorm {R : Type*} [CommRing R] (G : Matrix n n R) (v : n → R) : R :=
  v ⬝ᵥ (G *ᵥ v)

def reflection {R : Type*} [CommRing R] (G : Matrix n n R) (v : n → R) :
    Matrix n n R :=
  1 - Matrix.vecMulVec v (G *ᵥ v)

omit [DecidableEq n] in
theorem rootNorm_smul {R : Type*} [CommRing R]
    (G : Matrix n n R) (c : R) (v : n → R) :
    rootNorm G (c • v) = c ^ 2 * rootNorm G v := by
  simp only [rootNorm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem reflection_neg {R : Type*} [CommRing R]
    (G : Matrix n n R) (v : n → R) : reflection G (-v) = reflection G v := by
  ext i j
  simp [reflection, Matrix.vecMulVec, Matrix.mulVec_neg]

omit [DecidableEq n] in
theorem rootNorm_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : Matrix n n R) (v : n → R) :
    f (rootNorm G v) = rootNorm (G.map f) (f ∘ v) := by
  rw [rootNorm, f.map_dotProduct]
  congr 1
  funext i
  exact f.map_mulVec G v i

theorem reflection_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : Matrix n n R) (v : n → R) :
    (reflection G v).map f = reflection (G.map f) (f ∘ v) := by
  ext i j
  simp only [reflection, Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec, Matrix.of_apply,
    map_sub, map_mul, Function.comp_apply]
  rw [f.map_mulVec]
  simp [Matrix.one_apply]

omit [DecidableEq n] in
theorem congruence_mulVec {m : Type*} [Fintype m] {R : Type*} [CommRing R]
    (G : Matrix m m R) (H : Matrix n n R) (Q : Matrix m n R)
    (hQ : Qᵀ * G * Q = H) (v : n → R) :
    (G *ᵥ (Q *ᵥ v)) ᵥ* Q = H *ᵥ v := by
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ]

omit [DecidableEq n] in
theorem rootNorm_transport {m : Type*} [Fintype m] {R : Type*} [CommRing R]
    (G : Matrix m m R) (H : Matrix n n R) (Q : Matrix m n R)
    (hQ : Qᵀ * G * Q = H) (v : n → R) :
    rootNorm G (Q *ᵥ v) = rootNorm H v := by
  simp only [rootNorm]
  calc
    (Q *ᵥ v) ⬝ᵥ (G *ᵥ (Q *ᵥ v)) = (G *ᵥ (Q *ᵥ v)) ⬝ᵥ (Q *ᵥ v) :=
      dotProduct_comm _ _
    _ = ((G *ᵥ (Q *ᵥ v)) ᵥ* Q) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
    _ = (H *ᵥ v) ⬝ᵥ v := by rw [congruence_mulVec G H Q hQ]
    _ = v ⬝ᵥ (H *ᵥ v) := dotProduct_comm _ _

theorem reflection_transport {m : Type*} [Fintype m] [DecidableEq m]
    {R : Type*} [CommRing R]
    (G : Matrix m m R) (H : Matrix n n R) (Q : Matrix m n R)
    (hQ : Qᵀ * G * Q = H) (v : n → R) :
    Q * reflection H v = reflection G (Q *ᵥ v) * Q := by
  simp only [reflection, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [congruence_mulVec G H Q hQ]

theorem reflection_mulVec_self {R : Type*} [CommRing R]
    (G : Matrix n n R) (v : n → R) (hv : rootNorm G v = 2) :
    reflection G v *ᵥ v = -v := by
  have hdot : (G *ᵥ v) ⬝ᵥ v = 2 := by
    rw [dotProduct_comm]
    exact hv
  rw [reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, hdot]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  ring

theorem reflection_involution {R : Type*} [CommRing R]
    (G : Matrix n n R) (v : n → R) (hv : rootNorm G v = 2) :
    reflection G v * reflection G v = 1 := by
  have hdot : (G *ᵥ v) ⬝ᵥ v = 2 := by
    rw [dotProduct_comm]
    exact hv
  let A := Matrix.vecMulVec v (G *ᵥ v)
  have hAA : A * A = A + A := by
    dsimp [A]
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot, Matrix.vecMulVec_smul, two_smul]
  change (1 - A) * (1 - A) = 1
  calc
    (1 - A) * (1 - A) = 1 - A - A + A * A := by noncomm_ring
    _ = 1 := by rw [hAA]; abel

theorem reflection_ne_one {R : Type*} [CommRing R] [CharZero R]
    (G : Matrix n n R) (v : n → R) (hv : rootNorm G v = 2) :
    reflection G v ≠ 1 := by
  intro h
  have houter : Matrix.vecMulVec v (G *ᵥ v) = 0 := by
    exact sub_eq_self.mp h
  have hn := congrArg (fun M : Matrix n n R => ∑ i, M i i) houter
  have hz : rootNorm G v = 0 := by
    simpa only [rootNorm, dotProduct, Matrix.vecMulVec_apply,
      Matrix.zero_apply, Finset.sum_const_zero] using hn
  rw [hv] at hz
  norm_num at hz

theorem reflection_isometry {R : Type*} [CommRing R]
    (G : Matrix n n R) (hG : G.IsSymm) (v : n → R) (hv : rootNorm G v = 2) :
    (reflection G v)ᵀ * G * reflection G v = G := by
  have hdot : (G *ᵥ v) ⬝ᵥ v = 2 := by
    rw [dotProduct_comm]
    exact hv
  let A := Matrix.vecMulVec v (G *ᵥ v)
  let B := Matrix.vecMulVec (G *ᵥ v) (G *ᵥ v)
  have hGA : G * A = B := Matrix.mul_vecMulVec _ _ _
  have hAG : Aᵀ * G = B := by
    dsimp [A, B]
    rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul,
      ← Matrix.mulVec_transpose, hG.eq]
  have hAGA : Aᵀ * G * A = B + B := by
    rw [hAG]
    dsimp [A, B]
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot, Matrix.vecMulVec_smul, two_smul]
  change (1 - A)ᵀ * G * (1 - A) = G
  rw [Matrix.transpose_sub, Matrix.transpose_one]
  calc
    (1 - Aᵀ) * G * (1 - A) = G - Aᵀ * G - G * A + Aᵀ * G * A := by
      noncomm_ring
    _ = G := by rw [hAGA, hGA, hAG]; abel

theorem reflection_preserves_rootNorm {R : Type*} [CommRing R]
    (G : Matrix n n R) (hG : G.IsSymm) (v w : n → R)
    (hv : rootNorm G v = 2) :
    rootNorm G (reflection G v *ᵥ w) = rootNorm G w :=
  rootNorm_transport G G (reflection G v) (reflection_isometry G hG v hv) w

theorem reflection_eq_imp_eq_or_neg {K : Type*} [Field K] [CharZero K]
    (G : Matrix n n K) (u v : n → K)
    (hu : rootNorm G u = 2) (hv : rootNorm G v = 2)
    (h : reflection G u = reflection G v) : u = v ∨ u = -v := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  have houter : Matrix.vecMulVec u (G *ᵥ u) = Matrix.vecMulVec v (G *ᵥ v) := by
    simpa only [reflection, sub_right_inj] using h
  have haction := congrArg (fun M : Matrix n n K => M *ᵥ u) houter
  change Matrix.vecMulVec u (G *ᵥ u) *ᵥ u = Matrix.vecMulVec v (G *ᵥ v) *ᵥ u at haction
  rw [Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, op_smul_eq_smul] at haction
  have hdot : (G *ᵥ u) ⬝ᵥ u = 2 := by
    rw [dotProduct_comm]
    exact hu
  rw [hdot] at haction
  let c : K := ((G *ᵥ v) ⬝ᵥ u) / 2
  have hratio : u = c • v := by
    have hs := congrArg (fun w : n → K => (2 : K)⁻¹ • w) haction
    simpa only [smul_smul, inv_mul_cancel₀ htwo, one_smul, c, div_eq_mul_inv,
      mul_comm] using hs
  have hnorm := rootNorm_smul G c v
  rw [← hratio, hu, hv] at hnorm
  have hc : c ^ 2 = 1 := by
    apply mul_right_cancel₀ htwo
    simpa only [one_mul] using hnorm.symm
  rcases (sq_eq_one_iff.mp hc) with hc | hc
  · left
    simpa only [hc, one_smul] using hratio
  · right
    simpa only [hc, neg_one_smul] using hratio

theorem reflection_eq_iff {K : Type*} [Field K] [CharZero K]
    (G : Matrix n n K) (u v : n → K)
    (hu : rootNorm G u = 2) (hv : rootNorm G v = 2) :
    reflection G u = reflection G v ↔ u = v ∨ u = -v := by
  constructor
  · exact reflection_eq_imp_eq_or_neg G u v hu hv
  · rintro (rfl | rfl)
    · rfl
    · exact reflection_neg G v

theorem integer_reflection_eq_imp_eq_or_neg
    (G : Matrix n n ℤ) (u v : n → ℤ)
    (hu : rootNorm G u = 2) (hv : rootNorm G v = 2)
    (h : reflection G u = reflection G v) : u = v ∨ u = -v := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have huq : rootNorm (G.map f) (f ∘ u) = 2 := by
    rw [← rootNorm_map f G u, hu]
    norm_num [f]
  have hvq : rootNorm (G.map f) (f ∘ v) = 2 := by
    rw [← rootNorm_map f G v, hv]
    norm_num [f]
  have hq : reflection (G.map f) (f ∘ u) = reflection (G.map f) (f ∘ v) := by
    rw [← reflection_map, ← reflection_map, h]
  rcases reflection_eq_imp_eq_or_neg (G.map f) (f ∘ u) (f ∘ v) huq hvq hq with he | he
  · left
    funext i
    exact Int.cast_injective (congrFun he i)
  · right
    funext i
    have hi := congrFun he i
    apply Int.cast_injective (α := ℚ)
    simpa [f] using hi

theorem integer_reflection_eq_iff
    (G : Matrix n n ℤ) (u v : n → ℤ)
    (hu : rootNorm G u = 2) (hv : rootNorm G v = 2) :
    reflection G u = reflection G v ↔ u = v ∨ u = -v := by
  constructor
  · exact integer_reflection_eq_imp_eq_or_neg G u v hu hv
  · rintro (rfl | rfl)
    · rfl
    · exact reflection_neg G v

end SerreMarkov.ReflectionRoots
