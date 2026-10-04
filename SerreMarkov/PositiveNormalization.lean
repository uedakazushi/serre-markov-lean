import SerreMarkov.PositiveSeparation
import SerreMarkov.IntrinsicUnique

/-! # Actual sign normalization of a positive intrinsic frame

The four signs are chosen from the actual primitive ranks. An integral
involutive diagonal basis change transports the complete frame, and an
explicit sign-mutation word realizes its Euler matrix.
-/

namespace SerreMarkov.PositiveNormalization

open Matrix IntrinsicFrame IntrinsicUnique IntrinsicSigns
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- Change the signs of the four exceptional basis vectors. -/
def signedSix (z : Six) (s : Fin 4 → ℤ) : Six :=
  ⟨s 0*s 1*z.a, s 0*s 2*z.b, s 0*s 3*z.c,
    s 1*s 2*z.d, s 1*s 3*z.e, s 2*s 3*z.f⟩

private theorem diagonal_square (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) :
    (Matrix.diagonal s : Mat4)*(Matrix.diagonal s : Mat4)=1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simpa only [pow_two] using hs i

/-- The genuine integral basis isomorphism underlying the signs. -/
def signUnit (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) : Mat4ˣ :=
  ⟨Matrix.diagonal s,Matrix.diagonal s,diagonal_square s hs,diagonal_square s hs⟩

theorem signed_gram (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) :
    (Matrix.diagonal s : Mat4)ᵀ * gram z * Matrix.diagonal s = gram (signedSix z s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_transpose,Matrix.diagonal_mul,Matrix.mul_diagonal,gram,signedSix]
  all_goals nlinarith only [hs 0,hs 1,hs 2,hs 3]

private theorem signed_gram_back (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) :
    (Matrix.diagonal s : Mat4)ᵀ * gram (signedSix z s) * Matrix.diagonal s = gram z := by
  rw [← signed_gram z s hs, Matrix.diagonal_transpose]
  calc
    _ = (Matrix.diagonal s * Matrix.diagonal s) * gram z *
      (Matrix.diagonal s * Matrix.diagonal s) := by noncomm_ring
    _ = _ := by rw [diagonal_square s hs]; simp

/-- Transport the original frame, retaining all primitive-flag conditions. -/
def signedFrame {z : Six} (R : Frame z) (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) :
    Frame (signedSix z s) :=
  unit_transportFrame (signUnit s hs) (signed_gram_back z s hs) R

theorem signedFrame_rank {z : Six} (R : Frame z) (s : Fin 4 → ℤ)
    (hs : ∀ i, (s i)^2=1) (i : Fin 4) :
    basisRank (signedFrame R s hs) i = s i*basisRank R i := by
  change (Pi.single i 1) ⬝ᵥ (gram (signedSix z s) *ᵥ ((Matrix.diagonal s : Mat4) *ᵥ R.flag.p)) = _
  rw [← signed_gram z s hs,Matrix.diagonal_transpose]
  rw [← Matrix.mulVec_mulVec ((Matrix.diagonal s : Mat4) *ᵥ R.flag.p)
    (Matrix.diagonal s * gram z) (Matrix.diagonal s)]
  rw [Matrix.mulVec_mulVec R.flag.p (Matrix.diagonal s) (Matrix.diagonal s),
    diagonal_square s hs,Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec R.flag.p (Matrix.diagonal s) (gram z)]
  simp only [basisRank,chiVec,single_dotProduct,one_mul,Matrix.mulVec_diagonal]

theorem signedFrame_parameters {z : Six} (R : Frame z) (s : Fin 4 → ℤ)
    (hs : ∀ i, (s i)^2=1) :
    (signedFrame R s hs).flag.k=R.flag.k ∧ A (signedFrame R s hs)=A R := by
  have h := latticeEquivalent_frame_invariants R (signedFrame R s hs)
    (show LatticeEquivalent z (signedSix z s) from ⟨signUnit s hs,signed_gram z s hs⟩)
  exact ⟨h.1.symm,h.2.symm⟩

/-- The diagonal normalization is an actual signed-mutation word. -/
theorem signedSix_reachable (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i, (s i)^2=1) :
    Reachable z (signedSix z s) := by
  have h0 : s 0 = 1 ∨ s 0 = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs 0)
  have h1 : s 1 = 1 ∨ s 1 = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs 1)
  have h2 : s 2 = 1 ∨ s 2 = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs 2)
  have h3 : s 3 = 1 ∨ s 3 = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs 3)
  rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;>
    rcases h2 with h2|h2 <;> rcases h3 with h3|h3
  · refine ⟨[],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s3],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s3, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s2],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s2, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s2, .s3],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s2, .s3, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s3],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s3, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s2],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s2, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s2, .s3],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]
  · refine ⟨[.s1, .s2, .s3, .s4],?_⟩
    ext <;> simp [applyWord,step,eps1,eps2,eps3,eps4,signedSix,h0,h1,h2,h3]

/-- Choose each basis sign from its primitive rank. -/
def rankSigns {z : Six} (R : Frame z) (i : Fin 4) : ℤ :=
  if 0 < basisRank R i then 1 else -1

theorem rankSigns_square {z : Six} (R : Frame z) (i : Fin 4) :
    (rankSigns R i)^2=1 := by unfold rankSigns; split_ifs <;> norm_num

theorem signedFrame_rank_positive {z : Six} (R : Frame z) (hA : 0 < A R) (i : Fin 4) :
    0 < basisRank (signedFrame R (rankSigns R) (rankSigns_square R)) i := by
  rw [signedFrame_rank]
  have hn : basisRank R i ≠ 0 :=
    frame_positive_rank_ne_zero R hA (Pi.single i 1) (standard_euler_square z i)
  unfold rankSigns
  split_ifs with h
  · simpa using h
  · simp only [neg_one_mul]
    omega

/-- Every positive frame has an actual reachable solution whose complete
intrinsic frame has positive primitive ranks and all pairings at least three. -/
theorem positive_frame_normalization {z : Six} (R : Frame z) (hz : isSolution z)
    (hA : 0 < A R) :
    ∃ (w : Six) (S : Frame w), Reachable z w ∧ isSolution w ∧
      A S=A R ∧ S.flag.k=R.flag.k ∧
      (∀ i, 0 < basisRank S i) ∧
      (∀ i j, i ≠ j → 3 ≤ symmetricForm w i j) := by
  let w := signedSix z (rankSigns R)
  let S := signedFrame R (rankSigns R) (rankSigns_square R)
  have hr : Reachable z w := signedSix_reachable z (rankSigns R) (rankSigns_square R)
  have hw : isSolution w := by
    obtain ⟨word,hword⟩ := hr
    rw [← hword]
    exact applyWord_preserves_solution word z hz
  have hpar : S.flag.k=R.flag.k ∧ A S=A R := signedFrame_parameters R _ _
  have hAS : 0 < A S := by rw [hpar.2]; exact hA
  have hri : ∀ i, 0 < basisRank S i := signedFrame_rank_positive R hA
  refine ⟨w,S,hr,hw,hpar.2,hpar.1,hri,?_⟩
  intro i j hij
  exact PositiveSeparation.positive_basis_pair_ge_three S hw hAS i j hij (hri i) (hri j)

/-- The solution-level version extracts the frame rather than assuming it. -/
theorem positive_solution_normalization (z : Six) (hz : isSolution z)
    (hreg : shiftedSerre z^3 ≠ 0) (hpos : 0 < thirdMinorSum z) :
    ∃ (w : Six) (S : Frame w), Reachable z w ∧ isSolution w ∧ 0 < A S ∧
      (∀ i, 0 < basisRank S i) ∧
      (∀ i j, i ≠ j → 3 ≤ symmetricForm w i j) := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz hreg
  have hA : 0 < A R := (frame_thirdMinorSum_pos_iff R).mp hpos
  obtain ⟨w,S,hr,hw,hAS,hk,hri,hpair⟩ := positive_frame_normalization R hz hA
  exact ⟨w,S,hr,hw,by rw [hAS]; exact hA,hri,hpair⟩

end SerreMarkov.PositiveNormalization

