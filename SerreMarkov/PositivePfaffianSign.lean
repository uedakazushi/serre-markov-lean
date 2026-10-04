import SerreMarkov.PositiveRankDescent

/-!
# Integer restrictions on the positive Pfaffian component

The Vieta descent in this file concerns integer rank pairs with a fixed
quadratic defect. It is unbounded and does not use a finite search.
The resulting restrictions do not assert that the entire q₂=4 component is
empty: they rule out a unit endpoint determinant and bound its absolute value
strictly above the primitive translation parameter.
-/

namespace SerreMarkov.PositivePfaffianSign

open IntrinsicFrame PositiveRankDescent
set_option maxHeartbeats 3000000

/-- A fixed nonnegative defect bounds an integral pairing. Positive integral
rank pairs reduce by a Vieta move until the larger rank is at most half its
Vieta sum; the bound at that terminal pair is elementary. -/
theorem integral_pair_defect_bound (h r s Q : ℤ) (hh : 3≤h)
    (hr : 0<r) (hs : 0<s) (hQ : 0≤Q)
    (heq : h*r*s=r^2+s^2+Q) : h≤Q+2 := by
  generalize hn : (r+s).toNat=n
  induction n using Nat.strong_induction_on generalizing r s with
  | h n ih =>
      have ordered (r s : ℤ) (hr : 0<r) (hs : 0<s) (hrs : r≤s)
          (heq : h*r*s=r^2+s^2+Q) (hn : (r+s).toNat=n) : h≤Q+2 := by
        by_cases ht : 2*s≤h*r
        · have hsecond : 0≤(h-1)*r-s := by
            have hprod : 0≤(h-2)*r := mul_nonneg (by omega) hr.le
            nlinarith only [ht,hprod]
          have hp := mul_nonneg (by omega : 0≤s-r) hsecond
          have hrone : 1≤r^2 := by nlinarith [sq_nonneg (r-1)]
          have hpone := mul_nonneg (by omega : 0≤h-2) (by omega : 0≤r^2-1)
          nlinarith only [heq,hp,hpone]
        · let t := h*r-s
          have htpos : 0<t := RR_vieta_rank_positive Q h r s 1
            hQ hr hs (by nlinarith only [heq])
          have hts : t<s := by dsimp [t]; omega
          have hnew : h*t*r=t^2+r^2+Q := by
            dsimp [t]
            have hmul := congrArg (fun u : ℤ => h*u) heq
            nlinarith only [heq,hmul]
          have hsize : (t+r).toNat<n := by rw [←hn]; omega
          exact ih _ hsize t r htpos hr hnew rfl
      rcases le_total r s with hrs | hsr
      · exact ordered r s hr hs hrs heq hn
      · exact ordered s r hs hr hsr (by nlinarith only [heq]) (by omega)

/- The two endpoint bounds use the same quadratic defect, with their integer
rank pairs reduced independently. No minimum of the whole frame is assumed. -/
theorem endpoint_pairing_bounds {z : Six} (R : Frame z) (hA : 0<A R)
    (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) (hf : 3≤z.f) :
    z.a≤A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2+2 ∧
    z.f≤A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2+2 := by
  have h01 := basis_RiemannRoch R 0 1
  have h23 := basis_RiemannRoch R 2 3
  simp [symmetricForm,gram] at h01 h23
  have hb01 := integral_pair_defect_bound z.a (basisRank R 0) (basisRank R 1)
    (A R*(basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0)^2)
    ha (hr 0) (hr 1) (mul_nonneg hA.le (sq_nonneg _)) h01
  have hb23 := integral_pair_defect_bound z.f (basisRank R 2) (basisRank R 3)
    (A R*(basisRank R 2*basisDegree R 3-basisRank R 3*basisDegree R 2)^2)
    hf (hr 2) (hr 3) (mul_nonneg hA.le (sq_nonneg _)) h23
  rw [←endpoint_wedge_squares_equal R hA.ne'] at hb23
  exact ⟨hb01,hb23⟩

/-- A nonzero endpoint difference which is an integral primitive translation
cannot occur at a unit wedge: more generally the wedge exceeds κ. -/
theorem difference_forces_large_wedge (A k c a f : ℤ) (hA : 0<A) (hk : 0<k)
    (hc : c≠0) (ha : 3≤a) (hf : 3≤f)
    (hba : a≤A*c^2+2) (hbf : f≤A*c^2+2)
    (hdiff : a-f=k*A*c) : k+1≤|c| := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have habs : |a-f|=k*A*|c| := by
    rw [hdiff,abs_mul,abs_mul,abs_of_pos hk,abs_of_pos hA]
  have hbound : |a-f|≤A*c^2-1 := abs_le.mpr ⟨by omega,by omega⟩
  have hcsq : c^2=|c|^2 := by rw [sq_abs]
  have hstrict : k < |c| := by
    by_contra hnot
    have hp := mul_nonneg (by omega : 0≤k-|c|)
      (mul_nonneg hA.le hcpos.le)
    rw [hcsq] at hbound
    nlinarith only [habs,hbound,hp]
  omega

/-- The positive Pfaffian component would require an endpoint determinant
whose absolute value is at least κ+1. This is a genuine integral restriction
beyond the real Riemann--Roch identities. -/
theorem positive_pfaffian_wedge_bound {z : Six} (R : Frame z) (hA : 0<A R)
    (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) (hf : 3≤z.f)
    (hq : q2 z=4) :
    R.flag.k+1≤|basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0| := by
  have hc := positive_frame_endpoint_wedge_ne_zero R hr ha
  obtain ⟨hba,hbf⟩ := endpoint_pairing_bounds R hA hr ha hf
  exact difference_forces_large_wedge _ _ _ _ _ hA R.flag.k_pos hc ha hf hba hbf
    (endpoint_difference_formula R hq hc)

/-- A unit endpoint rank-degree determinant rules out q₂=4. -/
theorem positive_pfaffian_unit_wedge_impossible {z : Six} (R : Frame z)
    (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) (hf : 3≤z.f)
    (hc : |basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0|=1)
    (hq : q2 z=4) : False := by
  have h := positive_pfaffian_wedge_bound R hA hr ha hf hq
  rw [hc] at h
  have hk := R.flag.k_pos
  omega

/-- Positive Pfaffian sign would force an endpoint gap larger than the
primitive generalized Markov coefficient Aκ². -/
theorem positive_pfaffian_endpoint_gap {z : Six} (R : Frame z)
    (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i) (ha : 3≤z.a) (hf : 3≤z.f)
    (hq : q2 z=4) : A R*R.flag.k^2+A R*R.flag.k≤|z.a-z.f| := by
  let c := basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0
  have hc := positive_frame_endpoint_wedge_ne_zero R hr ha
  have hd := endpoint_difference_formula R hq hc
  have habs : |z.a-z.f|=R.flag.k*A R*|c| := by
    rw [hd,abs_mul,abs_mul,abs_of_pos R.flag.k_pos,abs_of_pos hA]
  have hb := positive_pfaffian_wedge_bound R hA hr ha hf hq
  change R.flag.k+1≤|c| at hb
  have hm := mul_nonneg (mul_nonneg R.flag.k_pos.le hA.le)
    (by omega : 0≤|c|-(R.flag.k+1))
  nlinarith only [habs,hm]

/-- A small endpoint gap suffices to determine the negative Pfaffian sign;
the unrestricted exclusion of q₂=4 is not assumed here. -/
theorem negative_pfaffian_of_small_endpoint_gap {z : Six} (R : Frame z)
    (hz : isSolution z) (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i)
    (ha : 3≤z.a) (hf : 3≤z.f) (hgap : |z.a-z.f|≤A R*R.flag.k^2) : q2 z= -4 := by
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  rcases hq with hq | hq
  · have hg := positive_pfaffian_endpoint_gap R hA hr ha hf hq
    have hp := mul_pos hA R.flag.k_pos
    omega
  · exact hq

/-- A unit endpoint determinant determines q₂=-4 in every positive integral
frame, without an orbit classification or geometric degree hypothesis. -/
theorem negative_pfaffian_of_unit_endpoint_wedge {z : Six} (R : Frame z)
    (hz : isSolution z) (hA : 0<A R) (hr : ∀ i : Fin 4,0<basisRank R i)
    (ha : 3≤z.a) (hf : 3≤z.f)
    (hc : |basisRank R 0*basisDegree R 1-basisRank R 1*basisDegree R 0|=1) :
    q2 z= -4 := by
  have hq : q2 z=4 ∨ q2 z= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  rcases hq with hq | hq
  · exact (positive_pfaffian_unit_wedge_impossible R hA hr ha hf hc hq).elim
  · exact hq

end SerreMarkov.PositivePfaffianSign
