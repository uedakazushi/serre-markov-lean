import SerreMarkov.PositiveHeightNormalization

/-! # The positive integral chamber is closed under actual braid mutations

Positive intrinsic solutions have absolute pairings at least three. Their
principal third minors are nonnegative. The resulting triangle inequality
makes each Vieta coordinate positive, and the integral absolute bound improves
it to at least three. This applies to every braid word without a length bound.
-/

namespace SerreMarkov.PositiveChamber

open IntrinsicFrame IntrinsicSigns PositiveNormalization NegativeDescent
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
set_option maxHeartbeats 3000000

def Coordinates (z : Six) : Prop :=
  3 ≤ z.a ∧ 3 ≤ z.b ∧ 3 ≤ z.c ∧ 3 ≤ z.d ∧ 3 ≤ z.e ∧ 3 ≤ z.f

def Chamber (z : Six) : Prop := isSolution z ∧ 0 < thirdMinorSum z ∧ Coordinates z

def IsBraid : Generator → Prop
  | .m1 | .m2 | .m3 | .i1 | .i2 | .i3 => True
  | .s1 | .s2 | .s3 | .s4 => False

def triangleDefect (u v w : ℤ) : ℤ := u^2+v^2+w^2-u*v*w

theorem positive_solution_regular (z : Six) (hz : isSolution z)
    (hpos : 0 < thirdMinorSum z) : shiftedSerre z^3 ≠ 0 := by
  intro hzero
  have h := (solution_cube_zero_iff_thirdMinorSum_zero z hz).mp hzero
  omega

/-- The original, arbitrarily signed coordinates themselves have absolute
value at least three; the ranks and the sign word are constructed internally. -/
theorem positive_solution_absolute_bounds (z : Six) (hz : isSolution z)
    (hpos : 0 < thirdMinorSum z) :
    3 ≤ |z.a| ∧ 3 ≤ |z.b| ∧ 3 ≤ |z.c| ∧ 3 ≤ |z.d| ∧ 3 ≤ |z.e| ∧ 3 ≤ |z.f| := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz (positive_solution_regular z hz hpos)
  have hA := (frame_thirdMinorSum_pos_iff R).mp hpos
  let w := signedSix z (rankSigns R)
  let S := signedFrame R (rankSigns R) (rankSigns_square R)
  have hr : Reachable z w := signedSix_reachable z _ (rankSigns_square R)
  have hw : isSolution w := by
    obtain ⟨word,hword⟩ := hr
    rw [← hword]
    exact applyWord_preserves_solution word z hz
  have hS : 0 < A S := by rw [(signedFrame_parameters R _ _).2]; exact hA
  have hri : ∀ i, 0 < basisRank S i := signedFrame_rank_positive R hA
  have hp : ∀ i j : Fin 4, i ≠ j → 3 ≤ symmetricForm w i j := by
    intro i j hij
    exact PositiveSeparation.positive_basis_pair_ge_three S hw hS i j hij (hri i) (hri j)
  have hc : Coordinates w := by
    simpa [Coordinates,symmetricForm,gram] using
      And.intro (hp 0 1 (by decide))
        (And.intro (hp 0 2 (by decide))
          (And.intro (hp 0 3 (by decide))
            (And.intro (hp 1 2 (by decide))
              (And.intro (hp 1 3 (by decide)) (hp 2 3 (by decide))))))
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hc
  have hwa : 3 ≤ |w.a| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.a)] using ha
  have hwb : 3 ≤ |w.b| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.b)] using hb
  have hwc : 3 ≤ |w.c| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.c)] using hc
  have hwd : 3 ≤ |w.d| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.d)] using hd
  have hwe : 3 ≤ |w.e| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.e)] using he
  have hwf : 3 ≤ |w.f| := by simpa only [abs_of_nonneg (by omega : 0 ≤ w.f)] using hf
  obtain ⟨hea,heb,hec,hed,hee,hef⟩ :=
    SignGaugeDescent.signedSix_abs z (rankSigns R) (rankSigns_square R)
  exact ⟨hea ▸ hwa,heb ▸ hwb,hec ▸ hwc,hed ▸ hwd,hee ▸ hwe,hef ▸ hwf⟩

/-- Every principal symmetric third minor is nonnegative on the positive
intrinsic branch, without a hypothesis on the coordinate signs. -/
theorem positive_triangle_bounds (z : Six) (hz : isSolution z)
    (hpos : 0 < thirdMinorSum z) :
    triangleDefect z.a z.b z.d ≤ 4 ∧ triangleDefect z.a z.c z.e ≤ 4 ∧
      triangleDefect z.b z.c z.f ≤ 4 ∧ triangleDefect z.d z.e z.f ≤ 4 := by
  obtain ⟨R⟩ := solution_regular_has_frame z hz (positive_solution_regular z hz hpos)
  have hA := (frame_thirdMinorSum_pos_iff R).mp hpos
  have hdiag (i : Fin 4) : 0 ≤ symmetricCofactors z i i := by
    rw [symmetricCofactors_eq_adjugate,frame_symmetric_adjugate R]
    change 0 ≤ 2*A R*R.flag.k^2*(R.flag.p i*R.flag.p i)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le) (sq_nonneg _))
      (by simpa only [pow_two] using sq_nonneg (R.flag.p i))
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  have h3 := hdiag 3
  change 0 ≤ -2*z.d^2+2*z.d*z.e*z.f-2*z.e^2-2*z.f^2+8 at h0
  change 0 ≤ -2*z.b^2+2*z.b*z.c*z.f-2*z.c^2-2*z.f^2+8 at h1
  change 0 ≤ -2*z.a^2+2*z.a*z.c*z.e-2*z.c^2-2*z.e^2+8 at h2
  change 0 ≤ -2*z.a^2+2*z.a*z.b*z.d-2*z.b^2-2*z.d^2+8 at h3
  dsimp [triangleDefect]
  constructor
  · nlinarith only [h3]
  constructor
  · nlinarith only [h2]
  constructor
  · nlinarith only [h1]
  · nlinarith only [h0]

theorem triangle_vieta_positive (u v w : ℤ) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hw : 3 ≤ w) (hdef : triangleDefect u v w ≤ 4) : 0 < u*v-w := by
  by_contra hn
  have hs : 0 ≤ w*(w-u*v) := mul_nonneg (by omega) (by omega)
  have hu2 : 9 ≤ u^2 := by nlinarith only [hu,sq_nonneg (u-3)]
  have hv2 : 9 ≤ v^2 := by nlinarith only [hv,sq_nonneg (v-3)]
  dsimp [triangleDefect] at hdef
  nlinarith only [hs,hu2,hv2,hdef]

/-- Actual braid and inverse-braid moves preserve all six lower bounds. -/
theorem step_preserves_chamber (g : Generator) (hg : IsBraid g) (z : Six)
    (hz : Chamber z) : Chamber (step g z) := by
  obtain ⟨hsol,hpos,ha,hb,hc,hd,he,hf⟩ := hz
  obtain ⟨ht1,ht2,ht3,ht4⟩ := positive_triangle_bounds z hsol hpos
  have habd := triangle_vieta_positive z.a z.b z.d ha hb hd ht1
  have hadb := triangle_vieta_positive z.a z.d z.b ha hd hb
    (by dsimp [triangleDefect] at *; nlinarith only [ht1])
  have hbda := triangle_vieta_positive z.b z.d z.a hb hd ha
    (by dsimp [triangleDefect] at *; nlinarith only [ht1])
  have hace := triangle_vieta_positive z.a z.c z.e ha hc he ht2
  have haec := triangle_vieta_positive z.a z.e z.c ha he hc
    (by dsimp [triangleDefect] at *; nlinarith only [ht2])
  have hfbc := triangle_vieta_positive z.f z.b z.c hf hb hc
    (by dsimp [triangleDefect] at *; nlinarith only [ht3])
  have hfcb := triangle_vieta_positive z.f z.c z.b hf hc hb
    (by dsimp [triangleDefect] at *; nlinarith only [ht3])
  have hdef := triangle_vieta_positive z.d z.e z.f hd he hf ht4
  have hdfe := triangle_vieta_positive z.d z.f z.e hd hf he
    (by dsimp [triangleDefect] at *; nlinarith only [ht4])
  have hfde := triangle_vieta_positive z.f z.d z.e hf hd he
    (by dsimp [triangleDefect] at *; nlinarith only [ht4])
  have hfed := triangle_vieta_positive z.f z.e z.d hf he hd
    (by dsimp [triangleDefect] at *; nlinarith only [ht4])
  have hr : Reachable z (step g z) := ⟨[g],rfl⟩
  have hsol' : isSolution (step g z) := applyWord_preserves_solution [g] z hsol
  have hpos' : 0 < thirdMinorSum (step g z) :=
    (latticeEquivalent_regular_signs hsol (positive_solution_regular z hsol hpos)
      (reachable_latticeEquivalent hr)).1.mp hpos
  obtain ⟨habs1,habs2,habs3,habs4,habs5,habs6⟩ :=
    positive_solution_absolute_bounds (step g z) hsol' hpos'
  have hpositive : 0 < (step g z).a ∧ 0 < (step g z).b ∧ 0 < (step g z).c ∧
      0 < (step g z).d ∧ 0 < (step g z).e ∧ 0 < (step g z).f := by
    cases g <;> simp only [IsBraid] at hg
    all_goals first | contradiction | (simp only [step,mu1,mu2,mu3,inv1,inv2,inv3]; omega)
  obtain ⟨hpa,hpb,hpc,hpd,hpe,hpf⟩ := hpositive
  refine ⟨hsol',hpos',?_⟩
  simpa only [Coordinates,abs_of_nonneg hpa.le,abs_of_nonneg hpb.le,abs_of_nonneg hpc.le,
    abs_of_nonneg hpd.le,abs_of_nonneg hpe.le,abs_of_nonneg hpf.le] using
      And.intro habs1 (And.intro habs2 (And.intro habs3 (And.intro habs4 (And.intro habs5 habs6))))

/-- Every finite braid word, of arbitrary length, stays in the chamber. -/
theorem applyWord_preserves_chamber (z : Six) (hz : Chamber z) (word : List Generator)
    (hword : ∀ g ∈ word, IsBraid g) : Chamber (applyWord z word) := by
  induction word generalizing z with
  | nil => exact hz
  | cons g word ih =>
      exact ih (step g z) (step_preserves_chamber g (hword g (by simp)) z hz)
        (fun k hk => hword k (by simp [hk]))

theorem braid_word_integerL1_eq_sum (z : Six) (hz : Chamber z) (word : List Generator)
    (hword : ∀ g ∈ word, IsBraid g) :
    integerL1 (applyWord z word) =
      (applyWord z word).a+(applyWord z word).b+(applyWord z word).c+
        (applyWord z word).d+(applyWord z word).e+(applyWord z word).f := by
  obtain ⟨_,_,ha,hb,hc,hd,he,hf⟩ := applyWord_preserves_chamber z hz word hword
  simp only [integerL1,abs_of_nonneg (by omega : 0 ≤ (applyWord z word).a),
    abs_of_nonneg (by omega : 0 ≤ (applyWord z word).b),
    abs_of_nonneg (by omega : 0 ≤ (applyWord z word).c),
    abs_of_nonneg (by omega : 0 ≤ (applyWord z word).d),
    abs_of_nonneg (by omega : 0 ≤ (applyWord z word).e),
    abs_of_nonneg (by omega : 0 ≤ (applyWord z word).f)]

end SerreMarkov.PositiveChamber
