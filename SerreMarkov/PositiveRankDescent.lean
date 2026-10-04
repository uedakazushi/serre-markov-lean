import SerreMarkov.PositiveChamber

/-! # Pure integral rank identities on the positive branch
These identities expose the alternating primitive Serre dependence before
any fundamental-domain or mapping-degree argument.
-/
namespace SerreMarkov.PositiveRankDescent
open Matrix IntrinsicFrame
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

private theorem rank_eq_mulVec {z : Six} (R : Frame z) (i : Fin 4) :
    basisRank R i=(gram z *ᵥ R.flag.p) i := by
  simp [basisRank,chiVec,single_dotProduct]

theorem flag_coordinate_first {z : Six} (R : Frame z) : R.flag.p 0= -basisRank R 0 := by
  have h := flag_rank_left z R.flag.p (Pi.single 0 1) R.flag.first_step
  change chiVec z R.flag.p (Pi.single 0 1)= -basisRank R 0 at h
  simpa [chiVec,Matrix.mulVec_single_one,Matrix.col_apply,dotProduct,
    Fin.sum_univ_four,gram] using h

theorem flag_coordinate_last {z : Six} (R : Frame z) : R.flag.p 3=basisRank R 3 := by
  rw [rank_eq_mulVec]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,gram]

theorem flag_coordinate_second {z : Six} (R : Frame z) :
    R.flag.p 1=z.a*basisRank R 0-basisRank R 1 := by
  have h := flag_rank_left z R.flag.p (Pi.single 1 1) R.flag.first_step
  change chiVec z R.flag.p (Pi.single 1 1)= -basisRank R 1 at h
  have h0 := flag_coordinate_first R
  have hx : z.a*R.flag.p 0+R.flag.p 1= -basisRank R 1 := by
    simpa [chiVec,Matrix.mulVec_single_one,Matrix.col_apply,dotProduct,
      Fin.sum_univ_four,gram,mul_comm] using h
  rw [h0] at hx
  nlinarith only [hx]

theorem flag_coordinate_third {z : Six} (R : Frame z) :
    R.flag.p 2=basisRank R 2-z.f*basisRank R 3 := by
  have h3 := flag_coordinate_last R
  have hx : basisRank R 2=R.flag.p 2+z.f*R.flag.p 3 := by
    rw [rank_eq_mulVec]
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,gram]
  rw [h3] at hx
  nlinarith only [hx]

/-- Riemann--Roch makes every positive-rank Vieta rank strictly positive. -/
theorem RR_vieta_rank_positive (A h r s C : ℤ) (hA : 0 ≤ A) (hr : 0<r) (hs : 0<s)
    (hRR : h*r*s=r^2+s^2+A*C^2) : 0<h*r-s := by
  have hAC : 0 ≤ A*C^2 := mul_nonneg hA (sq_nonneg C)
  by_contra hn
  have hm := mul_nonpos_of_nonpos_of_nonneg (by omega : h*r-s ≤ 0) hs.le
  nlinarith [sq_pos_of_pos hr]

/-- The primitive Serre kernel has alternating signs in every positive-rank
exceptional basis, using only the Euler flag and rank-degree identity. -/
theorem positive_frame_flag_alternating {z : Six} (R : Frame z) (hA : 0<A R)
    (hr : ∀ i : Fin 4,0<basisRank R i) :
    R.flag.p 0<0 ∧ 0<R.flag.p 1 ∧ R.flag.p 2<0 ∧ 0<R.flag.p 3 := by
  have h01 := basis_RiemannRoch R 0 1
  have h32 := basis_RiemannRoch R 3 2
  simp [symmetricForm,gram] at h01 h32
  have hsecond := RR_vieta_rank_positive (A R) z.a (basisRank R 0) (basisRank R 1)
    (basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0) hA.le (hr 0) (hr 1) h01
  have hthird := RR_vieta_rank_positive (A R) z.f (basisRank R 3) (basisRank R 2)
    (basisRank R 3*basisDegree R 2-basisRank R 2*basisDegree R 3) hA.le (hr 3) (hr 2) h32
  rw [flag_coordinate_first,flag_coordinate_second,flag_coordinate_third,flag_coordinate_last]
  exact ⟨by linarith [hr 0],hsecond,by linarith,hr 3⟩

/-- The two endpoint rank quadratics agree identically in a primitive frame. -/
theorem endpoint_rank_quadratics_equal {z : Six} (R : Frame z) :
    (basisRank R 0)^2+(basisRank R 1)^2-z.a*basisRank R 0*basisRank R 1 =
      (basisRank R 2)^2+(basisRank R 3)^2-z.f*basisRank R 2*basisRank R 3 := by
  have h := R.flag.isotropic_pp
  have hsum : ∑ i : Fin 4,R.flag.p i*basisRank R i=0 := by
    simpa only [chiVec,dotProduct,← rank_eq_mulVec] using h
  rw [Fin.sum_univ_four] at hsum
  rw [flag_coordinate_first,flag_coordinate_second,flag_coordinate_third,flag_coordinate_last] at hsum
  nlinarith only [hsum]

/-- The two endpoint rank-degree determinants have the same square without
any slope ordering or global geometric hypothesis. -/
theorem endpoint_wedge_squares_equal {z : Six} (R : Frame z) (hA : A R≠0) :
    (basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2 =
      (basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2)^2 := by
  have h01 := basis_RiemannRoch R 0 1
  have h23 := basis_RiemannRoch R 2 3
  simp [symmetricForm,gram] at h01 h23
  have hquad := endpoint_rank_quadratics_equal R
  apply mul_left_cancel₀ hA
  nlinarith only [h01,h23,hquad]

private theorem degree_eq_mulVec {z : Six} (R : Frame z) (i : Fin 4) :
    basisDegree R i=(gram z *ᵥ R.flag.l) i := by
  simp [basisDegree,chiVec,single_dotProduct]

theorem degree_flag_coordinate_first {z : Six} (R : Frame z) :
    R.flag.l 0= -basisDegree R 0-R.flag.k*basisRank R 0 := by
  have h := flag_degree_left z R.flag.p R.flag.l (Pi.single 0 1) R.flag.k R.flag.second_step
  change chiVec z R.flag.l (Pi.single 0 1)=
    -basisDegree R 0-R.flag.k*basisRank R 0 at h
  simpa [chiVec,Matrix.mulVec_single_one,Matrix.col_apply,dotProduct,
    Fin.sum_univ_four,gram] using h

theorem degree_flag_coordinate_second {z : Six} (R : Frame z) :
    R.flag.l 1=z.a*basisDegree R 0-basisDegree R 1+R.flag.k*R.flag.p 1 := by
  have h := flag_degree_left z R.flag.p R.flag.l (Pi.single 1 1) R.flag.k R.flag.second_step
  change chiVec z R.flag.l (Pi.single 1 1)=
    -basisDegree R 1-R.flag.k*basisRank R 1 at h
  have hx : z.a*R.flag.l 0+R.flag.l 1=
      -basisDegree R 1-R.flag.k*basisRank R 1 := by
    simpa [chiVec,Matrix.mulVec_single_one,Matrix.col_apply,dotProduct,
      Fin.sum_univ_four,gram,mul_comm] using h
  rw [flag_coordinate_second]
  rw [degree_flag_coordinate_first] at hx
  nlinarith only [hx]

theorem degree_flag_coordinate_last {z : Six} (R : Frame z) :
    R.flag.l 3=basisDegree R 3 := by
  rw [degree_eq_mulVec]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,gram]

theorem degree_flag_coordinate_third {z : Six} (R : Frame z) :
    R.flag.l 2=basisDegree R 2-z.f*basisDegree R 3 := by
  have hx : basisDegree R 2=R.flag.l 2+z.f*R.flag.l 3 := by
    rw [degree_eq_mulVec]
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,gram]
  rw [degree_flag_coordinate_last] at hx
  nlinarith only [hx]

/-- The primitive translation parameter is controlled by the two endpoint
rank-degree determinants, with their signs retained. -/
theorem endpoint_wedge_translation {z : Six} (R : Frame z) :
    z.a*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)+
      z.f*(basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2)=
    R.flag.k*A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2 := by
  have hpl := R.flag.isotropic_pl
  have hlp := R.flag.isotropic_lp
  have hpl' : ∑ i : Fin 4,R.flag.p i*basisDegree R i=0 := by
    simpa only [chiVec,dotProduct,← degree_eq_mulVec] using hpl
  have hlp' : ∑ i : Fin 4,R.flag.l i*basisRank R i=0 := by
    simpa only [chiVec,dotProduct,← rank_eq_mulVec] using hlp
  rw [Fin.sum_univ_four] at hpl' hlp'
  rw [degree_flag_coordinate_first,degree_flag_coordinate_second,
    degree_flag_coordinate_third,degree_flag_coordinate_last] at hlp'
  rw [flag_coordinate_first,flag_coordinate_second,flag_coordinate_third,
    flag_coordinate_last] at hpl'
  rw [flag_coordinate_second] at hlp'
  have hRR := basis_RiemannRoch R 0 1
  simp [symmetricForm,gram] at hRR
  have hkRR := congrArg (fun t : ℤ => R.flag.k*t) hRR
  nlinarith only [hpl',hlp',hkRR]

private theorem alternating_rank {z : Six} (R : Frame z) (i : Fin 4) :
    (alternatingForm z *ᵥ R.flag.p) i=2*basisRank R i := by
  have h := flag_rank_left z R.flag.p (Pi.single i 1) R.flag.first_step
  change chiVec z R.flag.p (Pi.single i 1)= -basisRank R i at h
  have hx : ((gram z)ᵀ *ᵥ R.flag.p) i= -basisRank R i := by
    rw [chiVec,Matrix.mulVec_single_one] at h
    simpa only [Matrix.col_apply,dotProduct,Matrix.mulVec,Matrix.transpose_apply,mul_comm] using h
  simp only [alternatingForm,Matrix.sub_mulVec,Pi.sub_apply,hx,← rank_eq_mulVec]
  ring

private theorem alternating_degree {z : Six} (R : Frame z) (i : Fin 4) :
    (alternatingForm z *ᵥ R.flag.l) i=2*basisDegree R i+R.flag.k*basisRank R i := by
  have h := flag_degree_left z R.flag.p R.flag.l (Pi.single i 1) R.flag.k R.flag.second_step
  change chiVec z R.flag.l (Pi.single i 1)=
    -basisDegree R i-R.flag.k*basisRank R i at h
  have hx : ((gram z)ᵀ *ᵥ R.flag.l) i=
      -basisDegree R i-R.flag.k*basisRank R i := by
    rw [chiVec,Matrix.mulVec_single_one] at h
    simpa only [Matrix.col_apply,dotProduct,Matrix.mulVec,Matrix.transpose_apply,mul_comm] using h
  simp only [alternatingForm,Matrix.sub_mulVec,Pi.sub_apply,hx,← degree_eq_mulVec]
  ring

private theorem alternating_plucker (z : Six) (p l : IntVec4) :
    (alternatingForm z *ᵥ p) 0*(alternatingForm z *ᵥ l) 1-
      (alternatingForm z *ᵥ p) 1*(alternatingForm z *ᵥ l) 0 =
    z.a*(dotProduct p (alternatingForm z *ᵥ l))-q2 z*(p 2*l 3-p 3*l 2) := by
  simp [alternatingForm,gram,Matrix.mulVec,dotProduct,Fin.sum_univ_four,q2]
  ring

/-- The Pfaffian determines the relative sign of the endpoint determinants.
In particular q₂=-4 gives equal determinants and q₂=4 gives opposite ones. -/
theorem endpoint_wedge_pfaffian {z : Six} (R : Frame z) :
    4*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)=
      -q2 z*(basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2) := by
  have h := alternating_plucker z R.flag.p R.flag.l
  have hdot : dotProduct R.flag.p (alternatingForm z *ᵥ R.flag.l)=0 := by
    rw [alternatingForm,Matrix.sub_mulVec,dotProduct_sub]
    have hleft : dotProduct R.flag.p ((gram z)ᵀ *ᵥ R.flag.l)=chiVec z R.flag.l R.flag.p := by
      simp [chiVec,Matrix.mulVec,dotProduct,Fin.sum_univ_four,gram]
      ring
    rw [hleft]
    change chiVec z R.flag.p R.flag.l-chiVec z R.flag.l R.flag.p=0
    rw [R.flag.isotropic_pl,R.flag.isotropic_lp]
    ring
  rw [alternating_rank,alternating_rank,alternating_degree,alternating_degree,hdot,
    flag_coordinate_third,flag_coordinate_last,degree_flag_coordinate_third,
    degree_flag_coordinate_last] at h
  nlinarith only [h]

/-- A positive integral zero-defect two-rank equation has pairing exactly two.
The proof is a genuine unbounded Euclidean descent on the sum of the ranks. -/
theorem integral_zero_defect_pair (h r s : ℤ) (hh : 3 ≤ h) (hr : 0<r) (hs : 0<s)
    (heq : h*r*s=r^2+s^2) : False := by
  generalize hn : (r+s).toNat=n
  induction n using Nat.strong_induction_on generalizing r s with
  | h n ih =>
      have descend (r s : ℤ) (hr : 0<r) (hs : 0<s) (hrs : r≤s)
          (heq : h*r*s=r^2+s^2) (hn : (r+s).toNat=n) : False := by
        have hrs' : r<s := by
          by_contra hne
          have hrsEq : r=s := by omega
          rw [hrsEq] at heq
          have hmul : 0 ≤ (h-3)*s^2 := mul_nonneg (by omega) (sq_nonneg _)
          nlinarith only [heq,hmul,sq_pos_of_pos hs]
        let t := h*r-s
        have ht : 0<t := RR_vieta_rank_positive 0 h r s 0 (by omega) hr hs
          (by nlinarith only [heq])
        have hprod : t*s=r^2 := by dsimp [t]; nlinarith only [heq]
        have htr : t<r := by
          by_contra hnot
          have hmult : 0 ≤ (t-r)*s := mul_nonneg (by omega) hs.le
          have hmult' : 0 < r*(s-r) := mul_pos hr (by omega)
          nlinarith only [hprod,hmult,hmult']
        have hnew : h*t*r=t^2+r^2 := by
          dsimp [t]
          have hmul := congrArg (fun u : ℤ => (h*r-s)*u) heq
          nlinarith only [heq,hmul]
        have hsize : (t+r).toNat<n := by rw [←hn]; omega
        exact ih _ hsize t r ht hr hnew rfl
      rcases le_total r s with hrs | hsr
      · exact descend r s hr hs hrs heq hn
      · exact descend s r hs hr hsr (by nlinarith only [heq]) (by omega)

/-- Integral Riemann--Roch forbids equal slopes once the pairing is at least
three. This is a rank descent statement, without any slope-order hypothesis. -/
theorem positive_integral_wedge_ne_zero (A h r s d e : ℤ)
    (hh : 3 ≤ h) (hr : 0<r) (hs : 0<s)
    (hRR : h*r*s=r^2+s^2+A*(r*e-s*d)^2) : r*e-s*d≠0 := by
  intro hzero
  apply integral_zero_defect_pair h r s hh hr hs
  simpa only [hzero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using hRR

/-- The negative Pfaffian component carries an integral endpoint sum formula. -/
theorem endpoint_sum_formula {z : Six} (R : Frame z) (hq : q2 z= -4)
    (hC : basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0≠0) :
    z.a+z.f=R.flag.k*A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0) := by
  have hpf := endpoint_wedge_pfaffian R
  rw [hq] at hpf
  have hCeq : basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2=
      basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0 := by
    nlinarith only [hpf]
  have htr := endpoint_wedge_translation R
  rw [hCeq] at htr
  apply mul_right_cancel₀ hC
  nlinarith only [htr]

/-- The positive Pfaffian component carries the corresponding difference
formula. The signs are retained rather than assuming a geometric ordering. -/
theorem endpoint_difference_formula {z : Six} (R : Frame z) (hq : q2 z=4)
    (hC : basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0≠0) :
    z.a-z.f=R.flag.k*A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0) := by
  have hpf := endpoint_wedge_pfaffian R
  rw [hq] at hpf
  have hCeq : basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2=
      -(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0) := by
    nlinarith only [hpf]
  have htr := endpoint_wedge_translation R
  rw [hCeq] at htr
  apply mul_right_cancel₀ hC
  nlinarith only [htr]

/-- The same primitive integral coefficient occurs in all four generalized
Markov equations. This retains the square restrictions beyond the inequalities
on the principal triangle defects. -/
theorem primitive_generalized_markov_equations {z : Six} (R : Frame z) :
    4-PositiveChamber.triangleDefect z.a z.b z.d=A R*R.flag.k^2*(R.flag.p 3)^2 ∧
    4-PositiveChamber.triangleDefect z.a z.c z.e=A R*R.flag.k^2*(R.flag.p 2)^2 ∧
    4-PositiveChamber.triangleDefect z.b z.c z.f=A R*R.flag.k^2*(R.flag.p 1)^2 ∧
    4-PositiveChamber.triangleDefect z.d z.e z.f=A R*R.flag.k^2*(R.flag.p 0)^2 := by
  have hh : symmetricCofactors z=fun i j =>
      2*A R*R.flag.k^2*(R.flag.p i*R.flag.p j) := by
    rw [symmetricCofactors_eq_adjugate,IntrinsicSigns.frame_symmetric_adjugate R]
    rfl
  have h3 := congrArg (fun M : Mat4 => M 3 3) hh
  have h2 := congrArg (fun M : Mat4 => M 2 2) hh
  have h1 := congrArg (fun M : Mat4 => M 1 1) hh
  have h0 := congrArg (fun M : Mat4 => M 0 0) hh
  change -2*z.a^2+2*z.a*z.b*z.d-2*z.b^2-2*z.d^2+8=
    2*A R*R.flag.k^2*(R.flag.p 3*R.flag.p 3) at h3
  change -2*z.a^2+2*z.a*z.c*z.e-2*z.c^2-2*z.e^2+8=
    2*A R*R.flag.k^2*(R.flag.p 2*R.flag.p 2) at h2
  change -2*z.b^2+2*z.b*z.c*z.f-2*z.c^2-2*z.f^2+8=
    2*A R*R.flag.k^2*(R.flag.p 1*R.flag.p 1) at h1
  change -2*z.d^2+2*z.d*z.e*z.f-2*z.e^2-2*z.f^2+8=
    2*A R*R.flag.k^2*(R.flag.p 0*R.flag.p 0) at h0
  dsimp [PositiveChamber.triangleDefect]
  exact ⟨by nlinarith only [h3],by nlinarith only [h2],by nlinarith only [h1],by nlinarith only [h0]⟩

/-- Endpoint determinant nonvanishing follows from integer rank descent. -/
theorem positive_frame_endpoint_wedge_ne_zero {z : Six} (R : Frame z)
    (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) :
    basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0≠0 := by
  apply positive_integral_wedge_ne_zero (A R) z.a (basisRank R 0) (basisRank R 1)
    (basisDegree R 0) (basisDegree R 1) ha (hr 0) (hr 1)
  simpa [symmetricForm,gram] using basis_RiemannRoch R 0 1

/-- A frame supplies an additional integral divisibility condition on the
endpoint sum or difference, according to its Pfaffian sign. -/
theorem positive_frame_endpoint_divisibility {z : Six} (R : Frame z)
    (hz : isSolution z) (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) :
    (q2 z= -4 ∧ R.flag.k*A R ∣ z.a+z.f) ∨
      (q2 z=4 ∧ R.flag.k*A R ∣ z.a-z.f) := by
  have hC := positive_frame_endpoint_wedge_ne_zero R hr ha
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  rcases hq with hq | hq
  · exact Or.inr ⟨hq,⟨_,endpoint_difference_formula R hq hC⟩⟩
  · exact Or.inl ⟨hq,⟨_,endpoint_sum_formula R hq hC⟩⟩

/-- On the negative Pfaffian component the two endpoint slopes have the
positive order forced by the primitive translation, before any degree theorem. -/
theorem negative_pfaffian_endpoint_wedges_positive {z : Six} (R : Frame z)
    (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i)
    (ha : 3≤z.a) (hf : 3≤z.f) (hq : q2 z= -4) :
    0<basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0 ∧
      0<basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2 := by
  have hC := positive_frame_endpoint_wedge_ne_zero R hr ha
  have hs := endpoint_sum_formula R hq hC
  have hpf := endpoint_wedge_pfaffian R
  rw [hq] at hpf
  have hkA : 0<R.flag.k*A R := mul_pos R.flag.k_pos hA
  have hCp : 0<basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0 := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hkA.le (by omega :
      basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0≤0)
    nlinarith only [hs,hm,ha,hf]
  exact ⟨hCp,by nlinarith only [hpf,hCp]⟩

/-- Coordinates of a general lattice vector are the integral linear
combinations of the four basis rank and degree coordinates. -/
theorem rank_degree_linear_combination {z : Six} (R : Frame z) (x : IntVec4) :
    chiVec z x R.flag.p=∑ i : Fin 4,x i*basisRank R i ∧
      chiVec z x R.flag.l=∑ i : Fin 4,x i*basisDegree R i := by
  constructor
  · simp only [chiVec,dotProduct,rank_eq_mulVec]
  · simp only [chiVec,dotProduct,degree_eq_mulVec]

/-- The integral rank coordinates are primitive. -/
theorem frame_rank_primitive_divisor {z : Six} (R : Frame z) (n : ℤ)
    (hn : ∀ i : Fin 4,n ∣ basisRank R i) : n ∣ 1 := by
  have h := (rank_degree_linear_combination R R.u).1
  rw [R.u_rank] at h
  rw [h]
  exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hn i) (R.u i))

/-- Surjectivity onto the rank-degree plane forces its six pair determinants
to have common divisor one. No individual determinant is assumed to be a unit. -/
theorem frame_wedge_primitive_divisor {z : Six} (R : Frame z) (n : ℤ)
    (hn : ∀ i j : Fin 4,n ∣ basisRank R i*basisDegree R j-basisRank R j*basisDegree R i) :
    n ∣ 1 := by
  have hu := rank_degree_linear_combination R R.u
  have hv := rank_degree_linear_combination R R.v
  rw [R.u_rank,R.u_degree] at hu
  rw [R.v_rank,R.v_degree] at hv
  have hsum : (∑ i : Fin 4,∑ j : Fin 4,
      R.u i*R.v j*(basisRank R i*basisDegree R j-basisRank R j*basisDegree R i))=1 := by
    calc
      _ = (∑ i : Fin 4,R.u i*basisRank R i)*(∑ j : Fin 4,R.v j*basisDegree R j)-
          (∑ i : Fin 4,R.u i*basisDegree R i)*(∑ j : Fin 4,R.v j*basisRank R j) := by
        simp only [Fin.sum_univ_four]
        ring
      _ = 1 := by rw [←hu.1,←hu.2,←hv.1,←hv.2]; norm_num
  rw [←hsum]
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right (hn i j) (R.u i*R.v j)

/-- The algebraic middle-vertex identity retains the sign of the Pfaffian.
Together with the endpoint identity this gives the exact ordering information
on the q₂=-4 component, without a global fundamental-domain argument. -/
theorem middle_wedge_identity {z : Six} (R : Frame z) (hz : isSolution z) (hA : A R≠0)
    (hC : basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0≠0) :
    4*A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)*
      (basisRank R 1*basisDegree R 2-basisRank R 2*basisDegree R 1)=
    4*basisRank R 0*basisRank R 2-q2 z*basisRank R 1*basisRank R 3 := by
  have hpl := R.flag.isotropic_pl
  have hpl' : ∑ i : Fin 4,R.flag.p i*basisDegree R i=0 := by
    simpa only [chiVec,dotProduct,← degree_eq_mulVec] using hpl
  rw [Fin.sum_univ_four,flag_coordinate_first,flag_coordinate_second,
    flag_coordinate_third,flag_coordinate_last] at hpl'
  have hRR01 := basis_RiemannRoch R 0 1
  have hRR23 := basis_RiemannRoch R 2 3
  simp [symmetricForm,gram] at hRR01 hRR23
  have hsquare := endpoint_wedge_squares_equal R hA
  have hp := congrArg (fun t : ℤ => t*basisRank R 1*basisRank R 2) hpl'
  have h01 := congrArg (fun t : ℤ => t*basisRank R 2*basisDegree R 1) hRR01
  have h23 := congrArg (fun t : ℤ => t*basisRank R 1*basisDegree R 2) hRR23
  have heq := congrArg (fun t : ℤ => t*A R*basisRank R 1*basisDegree R 2) hsquare
  have hpre :
      A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2*
        (basisRank R 1*basisDegree R 2-basisRank R 2*basisDegree R 1)=
      basisRank R 0*basisRank R 2*
        (basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)+
      basisRank R 1*basisRank R 3*
        (basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2) := by
    nlinarith only [hp,h01,h23,heq]
  have hpforiginal := endpoint_wedge_pfaffian R
  have hqmul := congrArg (fun t : ℤ => t*
    (basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2)) hz.2
  have hpfmul := congrArg (fun t : ℤ => q2 z*t) hpforiginal
  have hpfreverse : 4*(basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2)=
      -q2 z*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0) := by
    nlinarith only [hqmul,hpfmul]
  have hpf := congrArg (fun t : ℤ => t*basisRank R 1*basisRank R 3) hpfreverse
  apply mul_right_cancel₀ hC
  nlinarith only [hpre,hpf]

/-- Conditional on q₂=-4, all six pairwise degree determinants are strictly
positive. Thus the four slopes are ordered by exact integral identities. -/
theorem negative_pfaffian_all_wedges_positive {z : Six} (R : Frame z) (hz : isSolution z)
    (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i)
    (ha : 3≤z.a) (hf : 3≤z.f) (hq : q2 z= -4) :
    ∀ i j : Fin 4,i<j →
      0<basisRank R i*basisDegree R j-basisRank R j*basisDegree R i := by
  obtain ⟨h01,h23⟩ := negative_pfaffian_endpoint_wedges_positive R hA hr ha hf hq
  have h12 : 0<basisRank R 1*basisDegree R 2-basisRank R 2*basisDegree R 1 := by
    have hm := middle_wedge_identity R hz hA.ne' h01.ne'
    rw [hq] at hm
    have hprod := mul_pos (hr 0) (hr 2)
    have hprod' := mul_pos (hr 1) (hr 3)
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℤ)≤4) hA.le) h01.le)
      (by omega : basisRank R 1*basisDegree R 2-basisRank R 2*basisDegree R 1≤0)
    nlinarith only [hm,hprod,hprod',hh]
  have h02 : 0<basisRank R 0*basisDegree R 2-basisRank R 2*basisDegree R 0 := by
    have hh01 := mul_pos (hr 2) h01
    have hh12 := mul_pos (hr 0) h12
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (hr 1).le
      (by omega : basisRank R 0*basisDegree R 2-basisRank R 2*basisDegree R 0≤0)
    nlinarith only [hh01,hh12,hh]
  have h13 : 0<basisRank R 1*basisDegree R 3-basisRank R 3*basisDegree R 1 := by
    have hh12 := mul_pos (hr 3) h12
    have hh23 := mul_pos (hr 1) h23
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (hr 2).le
      (by omega : basisRank R 1*basisDegree R 3-basisRank R 3*basisDegree R 1≤0)
    nlinarith only [hh12,hh23,hh]
  have h03 : 0<basisRank R 0*basisDegree R 3-basisRank R 3*basisDegree R 0 := by
    have hh02 := mul_pos (hr 3) h02
    have hh23 := mul_pos (hr 0) h23
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (hr 2).le
      (by omega : basisRank R 0*basisDegree R 3-basisRank R 3*basisDegree R 0≤0)
    nlinarith only [hh02,hh23,hh]
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals assumption

/-- The height uses absolute values so it is a natural number for every
integral frame, and is the sum of the positive ranks on the positive leaf. -/
def rankHeight {z : Six} (R : Frame z) : ℕ :=
  ∑ i : Fin 4,(basisRank R i).natAbs

/-- Every positive frame orbit contains a genuine minimum of integral rank
height. The minimum ranges over actual reachable chambers and their positive
primitive frames, without any bound on braid-word length. -/
theorem positive_frame_reachable_minimal_rank {z : Six} (R : Frame z)
    (hz : PositiveChamber.Chamber z) (hA : 0<A R)
    (hr : ∀ i : Fin 4,0<basisRank R i) :
    ∃ (w : Six) (S : Frame w), PositiveChamber.Chamber w ∧ Reachable z w ∧
      0<A S ∧ (∀ i : Fin 4,0<basisRank S i) ∧
      ∀ (v : Six) (T : Frame v), PositiveChamber.Chamber v → Reachable z v →
        0<A T → (∀ i : Fin 4,0<basisRank T i) → rankHeight S≤rankHeight T := by
  classical
  let P : ℕ → Prop := fun n => ∃ (w : Six) (S : Frame w),
    PositiveChamber.Chamber w ∧ Reachable z w ∧ 0<A S ∧
      (∀ i : Fin 4,0<basisRank S i) ∧ rankHeight S=n
  have hex : ∃ n,P n :=
    ⟨rankHeight R,z,R,hz,reachable_refl z,hA,hr,rfl⟩
  obtain ⟨w,S,hw,hreach,hAS,hrs,heq⟩ := Nat.find_spec hex
  refine ⟨w,S,hw,hreach,hAS,hrs,?_⟩
  intro v T hv hrv hAT hrt
  rw [heq]
  exact Nat.find_min' hex ⟨v,T,hv,hrv,hAT,hrt,rfl⟩

end SerreMarkov.PositiveRankDescent
