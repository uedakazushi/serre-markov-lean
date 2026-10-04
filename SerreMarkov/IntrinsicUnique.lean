import SerreMarkov.IntrinsicFrame
import SerreMarkov.SerreInvariant

/-! # Independence of the primitive intrinsic parameters

Rank and degree surjectivity force the changes of primitive flag generators
to have unit coefficients. Positivity of the first-step coefficient makes
`κ` independent of the flag; the symmetric form on the rank kernel then
makes `A` independent of the chosen integral frame.
-/

namespace SerreMarkov.IntrinsicUnique

open Matrix IntrinsicFrame
set_option maxHeartbeats 2000000

private theorem flag_coefficients {z : Six} (R S : Frame z) :
    ∃ ε a t : ℤ,
      S.flag.p = ε • R.flag.p ∧
      S.flag.l = a • R.flag.p + t • R.flag.l ∧
      (ε = 1 ∨ ε = -1) ∧ (t = 1 ∨ t = -1) ∧
      S.flag.k*ε = t*R.flag.k := by
  obtain ⟨ε,hp⟩ := R.flag.first_generator S.flag.p S.flag.first_step
  have he : ε*chiVec z S.u R.flag.p = 1 := by
    have h := S.u_rank
    rw [hp,chiVec_smul_right] at h
    exact h
  have heunit : ε = 1 ∨ ε = -1 :=
    Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ he)
  have he0 : ε ≠ 0 := by rcases heunit with h | h <;> omega
  have hl2 : (shiftedSerre z^2) *ᵥ S.flag.l = 0 := by
    rw [pow_two,←Matrix.mulVec_mulVec,S.flag.second_step,
      Matrix.mulVec_neg,Matrix.mulVec_smul,S.flag.first_step]
    simp
  obtain ⟨a,t,hl⟩ := (R.flag.second_span S.flag.l).mp hl2
  have hv0 : chiVec z S.v R.flag.p = 0 := by
    have h := S.v_rank
    rw [hp,chiVec_smul_right] at h
    exact (mul_eq_zero.mp h).resolve_left he0
  have ht : t*chiVec z S.v R.flag.l = 1 := by
    have h := S.v_degree
    rw [hl,chiVec_add_right,chiVec_smul_right,chiVec_smul_right,hv0] at h
    simpa only [mul_zero,zero_add] using h
  have htunit : t = 1 ∨ t = -1 :=
    Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ ht)
  have hk := congrArg (fun x : IntVec4 => chiVec z R.u x) S.flag.second_step
  rw [hl,hp] at hk
  simp only [Matrix.mulVec_add,Matrix.mulVec_smul,R.flag.first_step,R.flag.second_step,
    smul_zero,zero_add,chiVec_smul_right,chiVec_neg_right,R.u_rank,mul_one] at hk
  have hkeq : S.flag.k*ε = t*R.flag.k := by nlinarith [hk]
  exact ⟨ε,a,t,hp,hl,heunit,htunit,hkeq⟩

/-- The positive integer first-step coefficient is independent of the frame. -/
theorem frame_k_unique {z : Six} (R S : Frame z) : R.flag.k = S.flag.k := by
  obtain ⟨ε,a,t,hp,hl,he,ht,hk⟩ := flag_coefficients R S
  have hr := R.flag.k_pos
  have hs := S.flag.k_pos
  rcases he with he | he <;> rcases ht with ht | ht <;>
    rw [he,ht] at hk <;> nlinarith [hk]

/-- The intrinsic symmetric-form parameter is independent of all choices. -/
theorem frame_A_unique {z : Six} (R S : Frame z) : A R = A S := by
  obtain ⟨ε,a,t,hp,hl,he,ht,hk⟩ := flag_coefficients R S
  have he0 : ε ≠ 0 := by rcases he with he | he <;> omega
  have hr0 : chiVec z S.v R.flag.p = 0 := by
    have h := S.v_rank
    rw [hp,chiVec_smul_right] at h
    exact (mul_eq_zero.mp h).resolve_left he0
  have hd : t*chiVec z S.v R.flag.l = 1 := by
    have h := S.v_degree
    rw [hl,chiVec_add_right,chiVec_smul_right,chiVec_smul_right,hr0] at h
    simpa only [mul_zero,zero_add] using h
  have hd2 : chiVec z S.v R.flag.l ^ 2 = 1 := by
    rcases ht with h | h <;> rw [h] at hd <;> nlinarith [hd]
  have h := frame_symmetric_rank_kernel R S.v S.v hr0 hr0
  rw [symmetric_pairing] at h
  have hdef : chiVec z S.v S.v = -A S := by simp [A]
  rw [hdef] at h
  nlinarith only [h,congrArg (fun q : ℤ => A R*q) hd2]

/-- The primitive coefficient is independent even before choosing `u,v`. -/
theorem flag_k_unique {z : Six} (F G : PrimitiveSerreFlag z) : F.k = G.k := by
  obtain ⟨u,hu⟩ := F.coordinates_surjective (1,0)
  obtain ⟨v,hv⟩ := F.coordinates_surjective (0,1)
  let R : Frame z := ⟨F,u,v,congrArg Prod.fst hu,congrArg Prod.snd hu,
    congrArg Prod.fst hv,congrArg Prod.snd hv⟩
  obtain ⟨u',hu'⟩ := G.coordinates_surjective (1,0)
  obtain ⟨v',hv'⟩ := G.coordinates_surjective (0,1)
  let S : Frame z := ⟨G,u',v',congrArg Prod.fst hu',congrArg Prod.snd hu',
    congrArg Prod.fst hv',congrArg Prod.snd hv'⟩
  exact frame_k_unique R S

private theorem unit_congruence_pairing {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (x y : IntVec4) :
    chiVec z ((B : Mat4) *ᵥ x) ((B : Mat4) *ᵥ y) = chiVec w x y := by
  unfold chiVec
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,←Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec,h]

private theorem unit_power_intertwine {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (n : ℕ) :
    shiftedSerre z ^ n * (B : Mat4) = (B : Mat4) * shiftedSerre w ^ n := by
  rw [shiftedSerre_unit_conjugate_pow B h n]
  simp [←Matrix.mul_assoc]

private theorem unit_power_action {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (n : ℕ) (x : IntVec4) :
    (shiftedSerre z ^ n) *ᵥ ((B : Mat4) *ᵥ x) =
      (B : Mat4) *ᵥ ((shiftedSerre w ^ n) *ᵥ x) := by
  rw [Matrix.mulVec_mulVec,unit_power_intertwine B h n,←Matrix.mulVec_mulVec]

private theorem unit_kernel_transport {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (n : ℕ) (x : IntVec4) :
    (shiftedSerre z ^ n) *ᵥ ((B : Mat4) *ᵥ x) = 0 ↔
      (shiftedSerre w ^ n) *ᵥ x = 0 := by
  rw [unit_power_action B h n]
  constructor
  · intro hx
    have he := congrArg (fun y : IntVec4 => (↑B⁻¹ : Mat4) *ᵥ y) hx
    simpa [Matrix.mulVec_mulVec] using he
  · intro hx
    rw [hx,Matrix.mulVec_zero]

/-- Transport of the entire primitive flag along an actual integral Euler
isomorphism, retaining its positive step coefficient. -/
def unit_transportFlag {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (G : PrimitiveSerreFlag w) :
    PrimitiveSerreFlag z where
  p := (B : Mat4) *ᵥ G.p
  l := (B : Mat4) *ᵥ G.l
  k := G.k
  k_pos := G.k_pos
  first_step := by
    have he := unit_power_action B h 1 G.p
    simpa only [pow_one,G.first_step,Matrix.mulVec_zero] using he
  second_step := by
    have he := unit_power_action B h 1 G.l
    simpa only [pow_one,G.second_step,Matrix.mulVec_neg,Matrix.mulVec_smul] using he
  first_generator x hx := by
    let y : IntVec4 := (↑B⁻¹ : Mat4) *ᵥ x
    have hy : (B : Mat4) *ᵥ y = x := by
      simp [y,Matrix.mulVec_mulVec]
    have hyker : shiftedSerre w *ᵥ y = 0 := by
      have he := (unit_kernel_transport B h 1 y).mp (by simpa only [pow_one,hy] using hx)
      simpa only [pow_one] using he
    obtain ⟨n,hn⟩ := G.first_generator y hyker
    refine ⟨n,?_⟩
    rw [←hy,hn,Matrix.mulVec_smul]
  second_span x := by
    constructor
    · intro hx
      let y : IntVec4 := (↑B⁻¹ : Mat4) *ᵥ x
      have hy : (B : Mat4) *ᵥ y = x := by
        simp [y,Matrix.mulVec_mulVec]
      have hyker := (unit_kernel_transport B h 2 y).mp (by rw [hy]; exact hx)
      obtain ⟨n,t,hn⟩ := (G.second_span y).mp hyker
      refine ⟨n,t,?_⟩
      rw [←hy,hn,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul]
    · rintro ⟨n,t,rfl⟩
      rw [←Matrix.mulVec_smul,←Matrix.mulVec_smul,←Matrix.mulVec_add]
      apply (unit_kernel_transport B h 2 _).mpr
      exact (G.second_span _).mpr ⟨n,t,rfl⟩
  coordinates_surjective q := by
    obtain ⟨x,hx⟩ := G.coordinates_surjective q
    refine ⟨(B : Mat4) *ᵥ x,?_⟩
    dsimp only
    rw [unit_congruence_pairing B h,unit_congruence_pairing B h]
    exact hx
  isotropic_pp := by rw [unit_congruence_pairing B h]; exact G.isotropic_pp
  isotropic_pl := by rw [unit_congruence_pairing B h]; exact G.isotropic_pl
  isotropic_lp := by rw [unit_congruence_pairing B h]; exact G.isotropic_lp
  isotropic_ll := by rw [unit_congruence_pairing B h]; exact G.isotropic_ll

/-- Transport all four coordinate vectors by the same integral isomorphism. -/
def unit_transportFrame {z w : Six} (B : Mat4ˣ)
    (h : (B : Mat4)ᵀ * gram z * (B : Mat4) = gram w) (S : Frame w) : Frame z where
  flag := unit_transportFlag B h S.flag
  u := (B : Mat4) *ᵥ S.u
  v := (B : Mat4) *ᵥ S.v
  u_rank := by exact (unit_congruence_pairing B h S.u S.flag.p).trans S.u_rank
  u_degree := by exact (unit_congruence_pairing B h S.u S.flag.l).trans S.u_degree
  v_rank := by exact (unit_congruence_pairing B h S.v S.flag.p).trans S.v_rank
  v_degree := by exact (unit_congruence_pairing B h S.v S.flag.l).trans S.v_degree

/-- Both primitive parameters are preserved by arbitrary integral Euler
isomorphisms, without requiring a mutation word. -/
theorem latticeEquivalent_frame_invariants {z w : Six}
    (R : Frame z) (S : Frame w) (h : LatticeEquivalent z w) :
    R.flag.k = S.flag.k ∧ A R = A S := by
  obtain ⟨B,hB⟩ := h
  have hk := frame_k_unique R (unit_transportFrame B hB S)
  have hA := frame_A_unique R (unit_transportFrame B hB S)
  refine ⟨hk,?_⟩
  calc
    A R = A (unit_transportFrame B hB S) := hA
    _ = A S := by
      unfold A
      exact congrArg Neg.neg (unit_congruence_pairing B hB S.v S.v)

theorem reachable_frame_invariants {z w : Six}
    (R : Frame z) (S : Frame w) (h : Reachable z w) :
    R.flag.k = S.flag.k ∧ A R = A S :=
  latticeEquivalent_frame_invariants R S (reachable_latticeEquivalent h)

/-- A regular solution has one intrinsic pair `(A,κ)`, independently of all
flag and integral-frame choices. -/
theorem solution_regular_unique_parameters (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z^3 ≠ 0) :
    ∃! q : ℤ×ℤ, ∃ R : Frame z, q = (A R,R.flag.k) := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  refine ⟨(A R,R.flag.k),⟨R,rfl⟩,?_⟩
  intro q hq
  obtain ⟨S,rfl⟩ := hq
  exact Prod.ext (frame_A_unique S R) (frame_k_unique S R)

end SerreMarkov.IntrinsicUnique
