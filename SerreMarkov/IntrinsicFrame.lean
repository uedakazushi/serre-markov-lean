import SerreMarkov.Intrinsic
import SerreMarkov.AdaptedIntrinsic
import SerreMarkov.Content
import SerreMarkov.NormedClifford
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # An integral frame for the primitive regular Serre flag

The surjective rank and degree coordinates supply `u,v`. Together with the
primitive isotropic flag `(l,p)`, these vectors give an integral unit matrix
and the general Euler form of Section 5.
-/

namespace SerreMarkov.IntrinsicFrame

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply
set_option maxHeartbeats 3000000

structure Frame (z : Six) where
  flag : PrimitiveSerreFlag z
  u : IntVec4
  v : IntVec4
  u_rank : chiVec z u flag.p = 1
  u_degree : chiVec z u flag.l = 0
  v_rank : chiVec z v flag.p = 0
  v_degree : chiVec z v flag.l = 1

theorem frame_of_flag (z : Six) (F : PrimitiveSerreFlag z) : Nonempty (Frame z) := by
  obtain ⟨u, hu⟩ := F.coordinates_surjective (1,0)
  obtain ⟨v, hv⟩ := F.coordinates_surjective (0,1)
  exact ⟨⟨F,u,v,congrArg Prod.fst hu,congrArg Prod.snd hu,
    congrArg Prod.fst hv,congrArg Prod.snd hv⟩⟩

theorem solution_regular_has_frame (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) : Nonempty (Frame z) := by
  obtain ⟨F⟩ := solution_regular_has_primitive_flag z hz hreg
  exact frame_of_flag z F

def columns {z : Six} (R : Frame z) : Mat4 :=
  fun i j => ![R.u,R.v,R.flag.l,R.flag.p] j i

def alpha {z : Six} (R : Frame z) : ℤ := chiVec z R.u R.u

def beta {z : Six} (R : Frame z) : ℤ := chiVec z R.u R.v

def gamma {z : Six} (R : Frame z) : ℤ := chiVec z R.v R.u

def A {z : Six} (R : Frame z) : ℤ := -chiVec z R.v R.v

private theorem congruence_entry {z : Six} (R : Frame z) (i j : Fin 4) :
    ((columns R)ᵀ * gram z * columns R) i j =
      chiVec z (![R.u,R.v,R.flag.l,R.flag.p] i)
        (![R.u,R.v,R.flag.l,R.flag.p] j) := by
  simp [columns, chiVec, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- The four coordinate vectors have exactly the manuscript's Euler matrix. -/
theorem frame_gram {z : Six} (R : Frame z) :
    (columns R)ᵀ * gram z * columns R =
      AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k := by
  have hpu := flag_rank_left z R.flag.p R.u R.flag.first_step
  have hpv := flag_rank_left z R.flag.p R.v R.flag.first_step
  have hlu := flag_degree_left z R.flag.p R.flag.l R.u R.flag.k R.flag.second_step
  have hlv := flag_degree_left z R.flag.p R.flag.l R.v R.flag.k R.flag.second_step
  simp only [R.u_rank,R.u_degree,R.v_rank,R.v_degree,mul_zero,mul_one,neg_zero,sub_zero,zero_sub] at hpu hpv hlu hlv
  ext i j
  rw [congruence_entry]
  fin_cases i <;> fin_cases j <;>
    simp [AdaptedIntrinsic.euler, alpha, beta, gamma, A,
      R.u_rank, R.u_degree, R.v_rank, R.v_degree,
      R.flag.isotropic_pp,R.flag.isotropic_pl,R.flag.isotropic_lp,R.flag.isotropic_ll]
  all_goals linarith

/-- Unimodularity follows from the two Euler determinants, without a
separate basis-extraction argument. -/
theorem frame_determinant {z : Six} (R : Frame z) :
    (columns R).det = 1 ∨ (columns R).det = -1 := by
  have h := congrArg Matrix.det (frame_gram R)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gram_det,
    AdaptedIntrinsic.euler_det] at h
  have hs : (columns R).det ^ 2 = (1 : ℤ)^2 := by nlinarith [h]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hs

theorem frame_isUnit {z : Six} (R : Frame z) : IsUnit (columns R) := by
  apply (Matrix.isUnit_iff_isUnit_det (columns R)).mpr
  rcases frame_determinant R with h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_neg_one

/-- The Serre operator in this integral frame is the universal adapted operator. -/
theorem frame_shifted_intertwine {z : Six} (R : Frame z) :
    shiftedSerre z * columns R = columns R *
      AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k := by
  let E := AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k
  let T := AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k
  have hgram : (columns R)ᵀ * gram z * columns R = E := frame_gram R
  have htranspose : (columns R)ᵀ * (gram z)ᵀ * columns R = Eᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      using congrArg Matrix.transpose hgram
  have hET : E*T = E+Eᵀ := by
    rw [show T = AdaptedIntrinsic.inverse (alpha R) (beta R) (gamma R) (A R) R.flag.k * Eᵀ + 1
      from (AdaptedIntrinsic.shifted_formula _ _ _ _ _).symm]
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    rw [show E * AdaptedIntrinsic.inverse (alpha R) (beta R) (gamma R) (A R) R.flag.k = 1
      from AdaptedIntrinsic.euler_inverse _ _ _ _ _]
    simp only [Matrix.one_mul, Matrix.mul_one]
    exact add_comm _ _
  have huB : IsUnit (columns R)ᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (frame_isUnit R)
  have huM : IsUnit (gram z) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [gram_det]
    exact isUnit_one
  apply (huB.mul huM).isRegular.left
  calc
    ((columns R)ᵀ * gram z) * (shiftedSerre z * columns R) =
        (columns R)ᵀ * (gram z * shiftedSerre z) * columns R := by noncomm_ring
    _ = (columns R)ᵀ * symmetricForm z * columns R := by rw [symmetricForm_eq]
    _ = E+Eᵀ := by
      rw [symmetricForm, Matrix.mul_add, Matrix.add_mul, hgram, htranspose]
    _ = E*T := hET.symm
    _ = ((columns R)ᵀ * gram z) * (columns R * T) := by rw [← hgram]; noncomm_ring

theorem frame_pow_intertwine {z : Six} (R : Frame z) (n : ℕ) :
    shiftedSerre z ^ n * columns R = columns R *
      AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = shiftedSerre z * (shiftedSerre z ^ n * columns R) := by
        rw [pow_succ', Matrix.mul_assoc]
      _ = shiftedSerre z * (columns R *
          AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k ^ n) := by rw [ih]
      _ = (shiftedSerre z * columns R) *
          AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k ^ n := by
        rw [Matrix.mul_assoc]
      _ = _ := by rw [frame_shifted_intertwine, Matrix.mul_assoc, ← pow_succ']

/-- The third power is integrally conjugate to the universal one-entry cube. -/
theorem frame_cube_conjugate {z : Six} (R : Frame z) :
    shiftedSerre z ^ 3 = columns R *
      AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k ^ 3 *
        (columns R)⁻¹ := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (frame_isUnit R)
  calc
    _ = (shiftedSerre z ^ 3 * columns R) * (columns R)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = _ := by rw [frame_pow_intertwine]

theorem columns_mulVec {z : Six} (R : Frame z) (y : IntVec4) :
    columns R *ᵥ y = y 0 • R.u + y 1 • R.v + y 2 • R.flag.l + y 3 • R.flag.p := by
  ext i
  simp [columns, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem rank_columns {z : Six} (R : Frame z) (y : IntVec4) :
    chiVec z (columns R *ᵥ y) R.flag.p = y 0 := by
  rw [columns_mulVec]
  simp only [chiVec_add_left,chiVec_smul_left,R.u_rank,R.v_rank,
    R.flag.isotropic_lp,R.flag.isotropic_pp,mul_zero,mul_one,add_zero]

/-- The intrinsic rank-one cube formula, for every integral vector. -/
theorem frame_cube_action {z : Six} (R : Frame z) (x : IntVec4) :
    (shiftedSerre z ^ 3) *ᵥ x =
      (2*A R*R.flag.k^2*chiVec z x R.flag.p) • R.flag.p := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (frame_isUnit R)
  let y : IntVec4 := (columns R)⁻¹ *ᵥ x
  have hy : columns R *ᵥ y = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hyrank : y 0 = chiVec z x R.flag.p := by
    rw [← hy, rank_columns]
  calc
    _ = (shiftedSerre z ^ 3 * columns R) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec, hy]
    _ = (columns R *
        AdaptedIntrinsic.shifted (alpha R) (beta R) (gamma R) (A R) R.flag.k ^ 3) *ᵥ y := by
      rw [frame_pow_intertwine]
    _ = _ := by
      rw [AdaptedIntrinsic.shifted_cube]
      ext i
      simp [columns,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
      rw [hyrank]
      ring

/-- Matrix form of the intrinsic tensor identity `N³=2 A κ² p⊗r`. -/
theorem frame_cube_tensor {z : Six} (R : Frame z) :
    shiftedSerre z ^ 3 = (2*A R*R.flag.k^2) •
      Matrix.vecMulVec R.flag.p (gram z *ᵥ R.flag.p) := by
  ext i j
  have h := congrFun (frame_cube_action R (Pi.single j 1)) i
  simpa [chiVec,Matrix.mulVec_single_one,Matrix.smul_apply,
    Matrix.vecMulVec_apply,single_dotProduct,mul_assoc,mul_left_comm,mul_comm] using h

/-- The Euler pairing in frame coordinates. -/
theorem frame_chi_coordinates {z : Six} (R : Frame z) (x y : IntVec4) :
    chiVec z (columns R *ᵥ x) (columns R *ᵥ y) =
      x ⬝ᵥ (AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k *ᵥ y) := by
  unfold chiVec
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, frame_gram]

theorem degree_columns {z : Six} (R : Frame z) (y : IntVec4) :
    chiVec z (columns R *ᵥ y) R.flag.l = y 1 := by
  rw [columns_mulVec]
  simp only [chiVec_add_left,chiVec_smul_left,R.u_degree,R.v_degree,
    R.flag.isotropic_ll,R.flag.isotropic_pl,mul_zero,mul_one,add_zero,zero_add]

/-- Content of the intrinsic cube in the original exceptional basis. -/
theorem frame_cube_content {z : Six} (R : Frame z) :
    (matrixContent (shiftedSerre z ^ 3) : ℤ) = 2 * |A R| * R.flag.k^2 := by
  rw [frame_cube_conjugate, AdaptedIntrinsic.shifted_cube]
  change (matrixContent (columns R * intrinsicCube (A R) R.flag.k *
    (columns R)⁻¹) : ℤ) = _
  rw [matrixContent_conjugate_of_det _ _ (frame_determinant R)]
  exact matrixContent_intrinsicCube_int _ _

theorem frame_symmetric_gram {z : Six} (R : Frame z) :
    (columns R)ᵀ * symmetricForm z * columns R =
      AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k +
      (AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k)ᵀ := by
  have ht := congrArg Matrix.transpose (frame_gram R)
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] at ht
  rw [symmetricForm,Matrix.mul_add,Matrix.add_mul,frame_gram]
  rw [Matrix.mul_assoc,ht]

/-- The symmetric pairing transported to frame coordinates. -/
theorem frame_symmetric_coordinates {z : Six} (R : Frame z) (x y : IntVec4) :
    (columns R *ᵥ x) ⬝ᵥ (symmetricForm z *ᵥ (columns R *ᵥ y)) =
      x ⬝ᵥ ((AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k +
      (AdaptedIntrinsic.euler (alpha R) (beta R) (gamma R) (A R) R.flag.k)ᵀ) *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,←Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,frame_symmetric_gram]

/-- On the kernel of the primitive rank, the symmetric form has the sole
term `-2 A d(x)d(y)`. -/
theorem frame_symmetric_rank_kernel {z : Six} (R : Frame z) (x y : IntVec4)
    (hx : chiVec z x R.flag.p = 0) (hy : chiVec z y R.flag.p = 0) :
    x ⬝ᵥ (symmetricForm z *ᵥ y) =
      -2*A R*chiVec z x R.flag.l*chiVec z y R.flag.l := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (frame_isUnit R)
  let qx : IntVec4 := (columns R)⁻¹ *ᵥ x
  let qy : IntVec4 := (columns R)⁻¹ *ᵥ y
  have hqx : columns R *ᵥ qx = x := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
  have hqy : columns R *ᵥ qy = y := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
  have hx0 : qx 0 = 0 := by rw [←rank_columns R qx,hqx,hx]
  have hy0 : qy 0 = 0 := by rw [←rank_columns R qy,hqy,hy]
  have hx1 : qx 1 = chiVec z x R.flag.l := by rw [←degree_columns R qx,hqx]
  have hy1 : qy 1 = chiVec z y R.flag.l := by rw [←degree_columns R qy,hqy]
  calc
    _ = (columns R *ᵥ qx) ⬝ᵥ (symmetricForm z *ᵥ (columns R *ᵥ qy)) := by rw [hqx,hqy]
    _ = _ := by
      rw [frame_symmetric_coordinates,
        AdaptedIntrinsic.symmetric_on_rank_kernel _ _ _ _ _ qx qy hx0 hy0,hx1,hy1]

private theorem chiVec_sub_left (z : Six) (x y v : IntVec4) :
    chiVec z (x-y) v = chiVec z x v - chiVec z y v := by
  simp [chiVec,sub_dotProduct]

theorem symmetric_pairing (z : Six) (x y : IntVec4) :
    x ⬝ᵥ (symmetricForm z *ᵥ y) = chiVec z x y + chiVec z y x := by
  unfold symmetricForm chiVec
  rw [Matrix.add_mulVec,dotProduct_add]
  congr 1
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]

/-- The universal Riemann--Roch identity for two vectors of Euler square one.
No sign or nonzero-rank hypothesis is needed for this algebraic identity. -/
theorem frame_RiemannRoch {z : Six} (R : Frame z) (x y : IntVec4)
    (hx : chiVec z x x = 1) (hy : chiVec z y y = 1) :
    (chiVec z x y+chiVec z y x)*chiVec z x R.flag.p*chiVec z y R.flag.p =
      (chiVec z x R.flag.p)^2+(chiVec z y R.flag.p)^2+
      A R*(chiVec z x R.flag.p*chiVec z y R.flag.l-
        chiVec z y R.flag.p*chiVec z x R.flag.l)^2 := by
  let q : IntVec4 := chiVec z y R.flag.p • x - chiVec z x R.flag.p • y
  have hr : chiVec z q R.flag.p = 0 := by
    dsimp [q]
    rw [chiVec_sub_left,chiVec_smul_left,chiVec_smul_left]
    ring
  have hd : chiVec z q R.flag.l =
      chiVec z y R.flag.p*chiVec z x R.flag.l-
        chiVec z x R.flag.p*chiVec z y R.flag.l := by
    dsimp [q]
    rw [chiVec_sub_left,chiVec_smul_left,chiVec_smul_left]
  have hqq : chiVec z q q =
      (chiVec z y R.flag.p)^2*chiVec z x x-
      chiVec z y R.flag.p*chiVec z x R.flag.p*(chiVec z x y+chiVec z y x)+
      (chiVec z x R.flag.p)^2*chiVec z y y := by
    dsimp [q]
    simp only [chiVec_sub_left,chiVec_sub_right,chiVec_smul_left,chiVec_smul_right]
    ring
  have h := frame_symmetric_rank_kernel R q q hr hr
  rw [symmetric_pairing,hqq,hx,hy,hd] at h
  nlinarith only [h]

/-- Positive `A` excludes rank-zero exceptional vectors. -/
theorem frame_positive_rank_ne_zero {z : Six} (R : Frame z) (hA : 0 < A R)
    (x : IntVec4) (hx : chiVec z x x = 1) : chiVec z x R.flag.p ≠ 0 := by
  intro hr
  have h := frame_symmetric_rank_kernel R x x hr hr
  rw [symmetric_pairing,hx] at h
  have hn := mul_nonneg hA.le (sq_nonneg (chiVec z x R.flag.l))
  nlinarith only [h,hn]

def basisRank {z : Six} (R : Frame z) (i : Fin 4) : ℤ :=
  chiVec z (Pi.single i 1) R.flag.p

def basisDegree {z : Six} (R : Frame z) (i : Fin 4) : ℤ :=
  chiVec z (Pi.single i 1) R.flag.l

theorem standard_euler_square (z : Six) (i : Fin 4) :
    chiVec z (Pi.single i 1) (Pi.single i 1) = 1 := by
  simp only [chiVec,Matrix.mulVec_single_one,single_dotProduct,one_mul,Matrix.col_apply]
  fin_cases i <;> simp [gram]

theorem basis_RiemannRoch {z : Six} (R : Frame z) (i j : Fin 4) :
    symmetricForm z i j*basisRank R i*basisRank R j =
      (basisRank R i)^2+(basisRank R j)^2+
      A R*(basisRank R i*basisDegree R j-basisRank R j*basisDegree R i)^2 := by
  have h := frame_RiemannRoch R (Pi.single i 1) (Pi.single j 1)
    (standard_euler_square z i) (standard_euler_square z j)
  simpa [basisRank,basisDegree,chiVec,Matrix.mulVec_single_one,single_dotProduct,
    symmetricForm,Matrix.add_apply,Matrix.transpose_apply] using h

/-- The rational half-turn input is extracted from every positive intrinsic
frame, with the actual exceptional-basis Euler pairings. -/
noncomputable def positiveHalfTurnData {z : Six} (R : Frame z) (hA : 0 < A R) :
    NormedClifford.Data :=
  NormedClifford.ofNumerators (A R : ℚ) (by exact_mod_cast hA)
    (fun i => (basisRank R i : ℚ)) (fun i => (basisDegree R i : ℚ))
    (fun i j => symmetricForm z i j)
    (fun i => by
      dsimp only
      have h : basisRank R i ≠ 0 := frame_positive_rank_ne_zero R hA (Pi.single i 1) (standard_euler_square z i)
      exact_mod_cast h)
    (fun i j => by
      dsimp only
      exact_mod_cast basis_RiemannRoch R i j)

/-- Regularity forces the intrinsic integer `A` to be nonzero. -/
theorem frame_A_ne_zero {z : Six} (R : Frame z) (hreg : shiftedSerre z ^ 3 ≠ 0) :
    A R ≠ 0 := by
  intro hA
  apply hreg
  have ht := (AdaptedIntrinsic.shifted_cube_zero_iff (alpha R) (beta R) (gamma R) (A R) R.flag.k).mpr (Or.inl hA)
  rw [frame_cube_conjugate, ht]
  simp

theorem solution_regular_frame_nonzero (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z ^ 3 ≠ 0) : ∃ R : Frame z, A R ≠ 0 := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  exact ⟨R,frame_A_ne_zero R hreg⟩

end SerreMarkov.IntrinsicFrame
