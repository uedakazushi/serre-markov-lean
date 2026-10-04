import SerreMarkov.NegativeTwoEdge

/-! # Descent in the positive chamber at an affine edge

The positive integral chamber with first edge two either reaches the family
through a proved affine boundary, or admits an actual strict braid descent.
The proof uses the two-edge conic and weak Cayley descent at edges of size two.
-/

namespace SerreMarkov.NegativeTwoPositive

open NegativeDescent NegativeTriangles NegativeBoundary NegativeTwoEdge

private theorem triangle_weak (u v w : ℤ) (hu : 2 ≤ u) (hv : 2 ≤ v)
    (hw : 2 ≤ w) (hum : u ≤ w) (hvm : v ≤ w)
    (ht : 4 ≤ cayleyDefect u v w) : |u*v-w| ≤ w := by
  by_cases hu2 : u=2
  · subst u
    exact abs_le.mpr ⟨by omega,by omega⟩
  by_cases hv2 : v=2
  · subst v
    exact abs_le.mpr ⟨by omega,by omega⟩
  exact (cayley_positive_abs_descent u v w (by omega) (by omega) (by omega) ⟨hum,hvm⟩ ht).le

private theorem triangle_strict (u v w : ℤ) (hu : 2 ≤ u) (hv : 2 ≤ v)
    (hw : 2 ≤ w) (hum : u < w) (hvm : v < w)
    (ht : 4 ≤ cayleyDefect u v w) : |u*v-w| < w := by
  by_cases hu2 : u=2
  · subst u
    exact abs_lt.mpr ⟨by omega,by omega⟩
  by_cases hv2 : v=2
  · subst v
    exact abs_lt.mpr ⟨by omega,by omega⟩
  exact cayley_positive_abs_descent u v w (by omega) (by omega) (by omega) ⟨hum.le,hvm.le⟩ ht

private theorem equal_small_conic_impossible (s f : ℤ) (hs : 0 < s) (hs2 : s ≤ 2)
    (hf : 3 ≤ f) (hc : s^2*(f+2)=(f-2)^2 ∨ s^2*(f+2)=(f+2)^2) : False := by
  have hcases : s=1 ∨ s=2 := by omega
  rcases hcases with rfl | rfl <;> rcases hc with hc | hc
  · by_cases hf5 : 5 ≤ f
    · nlinarith [mul_nonneg (by omega : 0 ≤ f) (by omega : 0 ≤ f-5)]
    · nlinarith [mul_nonneg (by omega : 0 ≤ 4-f) (by omega : 0 ≤ f-1)]
  · nlinarith
  · by_cases hf9 : 9 ≤ f
    · nlinarith [mul_nonneg (by omega : 0 ≤ f-9) (by omega : 0 ≤ f-8)]
    · nlinarith [mul_nonneg (by omega : 0 ≤ f) (by omega : 0 ≤ 8-f)]
  · nlinarith

private theorem equal_differences_large (z : Six) (hz : isSolution z) (ha : z.a=2)
    (hf : 3 ≤ z.f) (hs : 0 < z.b-z.d) (heq : z.b-z.d=z.e-z.c) :
    3 ≤ z.b-z.d := by
  by_contra hn
  have hs2 : z.b-z.d ≤ 2 := by omega
  have hz' : isSolution ⟨2,z.b,z.c,z.d,z.e,z.f⟩ := by
    convert hz using 1 <;> cases z <;> simp_all
  have hsign : q2 ⟨2,z.b,z.c,z.d,z.e,z.f⟩=4 ∨
      q2 ⟨2,z.b,z.c,z.d,z.e,z.f⟩=-4 := by
    have he := hz'.2
    have hprod : (q2 ⟨2,z.b,z.c,z.d,z.e,z.f⟩-4)*
        (q2 ⟨2,z.b,z.c,z.d,z.e,z.f⟩+4)=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h <;> omega
  have hc : (z.b-z.d)^2*(z.f+2)=(z.f-2)^2 ∨
      (z.b-z.d)^2*(z.f+2)=(z.f+2)^2 := by
    rcases hsign with h | h
    · have hcon := edge_two_conic_plus z.b z.c z.d z.e z.f hz'.1 h
      left
      nlinarith [sq_nonneg (z.b-z.d+z.c-z.e)]
    · have hcon := edge_two_conic_minus z.b z.c z.d z.e z.f hz'.1 h
      right
      nlinarith [sq_nonneg (z.b-z.d+z.c-z.e)]
  exact equal_small_conic_impossible (z.b-z.d) z.f hs hs2 hf hc

/-- With unequal neighboring pairs and opposite endpoints larger than two,
one elementary braid strictly decreases the height. -/
theorem positive_two_edge_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=2)
    (hb : 2 ≤ z.b) (hc : 2 ≤ z.c) (hd : 2 ≤ z.d) (he : 2 ≤ z.e) (hf : 3 ≤ z.f)
    (hbd : z.b≠z.d) (hce : z.c≠z.e) : OneStepDrop z := by
  obtain ⟨ht1,ht2,ht3,ht4⟩ := negative_triangle_inequalities z hz hneg
  have hql : -4 ≤ 2*z.f-z.b*z.e+z.c*z.d := by
    have hh := hz.2
    change (z.a*z.f-z.b*z.e+z.c*z.d)^2=16 at hh
    rw [ha] at hh
    nlinarith only [hh]
  have hqu : 2*z.f-z.b*z.e+z.c*z.d ≤ 4 := by
    have hh := hz.2
    change (z.a*z.f-z.b*z.e+z.c*z.d)^2=16 at hh
    rw [ha] at hh
    nlinarith only [hh]
  have drop_mu1 (h : |2*z.b-z.d|+|2*z.c-z.e| < z.d+z.e) : OneStepDrop z := by
    left
    apply (mu1_drop_iff z).mpr
    simpa only [ha,abs_of_nonneg (by omega : 0 ≤ z.d),
      abs_of_nonneg (by omega : 0 ≤ z.e)] using h
  have drop_inv1 (h : |2*z.d-z.b|+|2*z.e-z.c| < z.b+z.c) : OneStepDrop z := by
    right; left
    apply (inv1_drop_iff z).mpr
    simpa only [ha,abs_of_nonneg (by omega : 0 ≤ z.b),
      abs_of_nonneg (by omega : 0 ≤ z.c)] using h
  by_cases hbdlt : z.b<z.d
  · by_cases hcelt : z.c<z.e
    · exact drop_mu1 (add_lt_add (abs_lt.mpr ⟨by omega,by omega⟩)
        (abs_lt.mpr ⟨by omega,by omega⟩))
    · have hec : z.e<z.c := by omega
      have h1 := mul_pos (show 0 < z.c-z.e by omega) (show 0 < z.d by omega)
      have h2 := mul_pos (show 0 < z.d-z.b by omega) (show 0 < z.e by omega)
      nlinarith
  have hdb : z.d<z.b := by omega
  by_cases heclt : z.e<z.c
  · exact drop_inv1 (add_lt_add (abs_lt.mpr ⟨by omega,by omega⟩)
      (abs_lt.mpr ⟨by omega,by omega⟩))
  have hce : z.c<z.e := by omega
  let s := z.b-z.d
  let t := z.e-z.c
  have hs : 0 < s := by dsimp [s]; omega
  have ht : 0 < t := by dsimp [t]; omega
  have hq : z.c*s+z.d*t+s*t ≤ 2*z.f+4 := by
    dsimp [s,t]
    nlinarith only [hql]
  have drop_mu2 (hde : z.d*z.e ≤ 2*z.f) : OneStepDrop z := by
    have h1 : |2*z.d-z.b| < z.b := abs_lt.mpr ⟨by omega,by omega⟩
    have hp : 0 ≤ z.d*z.e := by positivity
    have h2 : |z.d*z.e-z.f| ≤ z.f := abs_le.mpr ⟨by omega,by omega⟩
    right; right; left
    apply (mu2_drop_iff z).mpr
    simpa only [ha,abs_of_nonneg (by omega : 0 ≤ z.b),
      abs_of_nonneg (by omega : 0 ≤ z.f)] using add_lt_add_of_lt_of_le h1 h2
  by_cases hts : t<s
  · by_cases hdt : t<z.d
    · have h1 : |z.d-s| < z.d+s-2*t := abs_lt.mpr ⟨by omega,by omega⟩
      apply drop_inv1
      have h2 : 0 ≤ 2*z.e-z.c := by omega
      rw [abs_of_nonneg h2]
      have h1' : |2*z.d-z.b| < z.b-2*(z.e-z.c) := by
        convert h1 using 1 <;> dsimp [s,t] <;> ring
      linarith
    · have hds : 0 < s-z.d := by omega
      have hst : 6 ≤ s*t := by
        have ht2 : 2 ≤ t := by omega
        have hs3 : 3 ≤ s := by omega
        nlinarith [mul_nonneg (by omega : 0 ≤ s-3) (by omega : 0 ≤ t-2)]
      have hp : 0 ≤ z.c*(s-z.d) := mul_nonneg (by omega) hds.le
      apply drop_mu2
      dsimp [s,t] at hq hp hst
      nlinarith
  have hst : s≤t := by omega
  by_cases hfast : s<t ∧ s<z.c
  · obtain ⟨hstlt,hcs⟩ := hfast
    have h1 : |z.c-t| < z.c+t-2*s := abs_lt.mpr ⟨by omega,by omega⟩
    apply drop_mu1
    have h2 : 0 ≤ 2*z.b-z.d := by omega
    rw [abs_of_nonneg h2]
    have h1' : |2*z.c-z.e| < z.e-2*(z.b-z.d) := by
      convert h1 using 1 <;> dsimp [s,t] <;> ring
    linarith
  have hequal_or_small : s=t ∨ (s<t ∧ z.c≤s) := by omega
  have impossible_e (hde : z.d≤z.e) (hfe : z.f≤z.e) : False := by
    have hbound : z.c*(s-2)+t*(z.d+s-2) ≤ 4 := by
      dsimp [s,t] at hq ⊢
      nlinarith only [hq,hfe]
    rcases hequal_or_small with hequal | ⟨hstlt,hsmall⟩
    · have hs3 : 3 ≤ s := by
        apply equal_differences_large z hz ha hf hs
        exact hequal
      have h1 : 0 ≤ z.c*(s-2) := mul_nonneg (by omega) (by omega)
      have h2 : 0 ≤ s*(z.d-2) := mul_nonneg (by omega) (by omega)
      rw [← hequal] at hbound
      nlinarith
    · have hs2 : 2 ≤ s := by omega
      have ht3 : 3 ≤ t := by omega
      have h1 : 0 ≤ z.c*(s-2) := mul_nonneg (by omega) (by omega)
      have h2 : 0 ≤ t*(z.d-2) := mul_nonneg (by omega) (by omega)
      have h3 : 6 ≤ s*t := by
        nlinarith [mul_nonneg (by omega : 0 ≤ s-2) (by omega : 0 ≤ t-3)]
      nlinarith
  by_cases hdf : z.d≤z.f
  · by_cases hef : z.e≤z.f
    · have h2 := triangle_weak z.d z.e z.f hd he (by omega) hdf hef ht4
      have hde : z.d*z.e≤2*z.f := by
        have hh := (abs_le.mp h2).2
        omega
      exact drop_mu2 hde
    · exact False.elim (impossible_e (by omega) (by omega))
  · by_cases hed : z.e≤z.d
    · have ht3' : 4 ≤ cayleyDefect z.f z.c z.b := by
        convert ht3 using 1 <;> dsimp [cayleyDefect] <;> ring
      have ht4' : 4 ≤ cayleyDefect z.f z.e z.d := by
        convert ht4 using 1 <;> dsimp [cayleyDefect] <;> ring
      have h1 := triangle_strict z.f z.c z.b (by omega) hc hb (by omega) (by omega) ht3'
      have h2 := triangle_weak z.f z.e z.d (by omega) he hd (by omega) hed ht4'
      right; right; right; right; right
      apply (inv3_drop_iff z).mpr
      simpa only [abs_of_nonneg (by omega : 0 ≤ z.b),
        abs_of_nonneg (by omega : 0 ≤ z.d)] using add_lt_add_of_lt_of_le h1 h2
    · exact False.elim (impossible_e (by omega) (by omega))

/-- Complete reduction of the positive affine-edge chamber. -/
theorem positive_two_edge_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=2)
    (hb : 2 ≤ z.b) (hc : 2 ≤ z.c) (hd : 2 ≤ z.d) (he : 2 ≤ z.e) (hf : 2 ≤ z.f) :
    FamilyOrDrop z := by
  by_cases hbd : z.b=z.d
  · left; exact affine_edge_equal_reachable_family z hz ha (Or.inl hbd)
  by_cases hce : z.c=z.e
  · left; exact affine_edge_equal_reachable_family z hz ha (Or.inr hce)
  by_cases hf2 : z.f=2
  · left; exact endpoint_two_reachable_family z hz (Or.inl ha) (Or.inl hf2)
  have hdrop := positive_two_edge_descent z hz hneg ha hb hc hd he (by omega) hbd hce
  right
  rcases hdrop with h | h | h | h | h | h
  · exact ⟨[.m1],h⟩
  · exact ⟨[.i1],h⟩
  · exact ⟨[.m2],h⟩
  · exact ⟨[.i2],h⟩
  · exact ⟨[.m3],h⟩
  · exact ⟨[.i3],h⟩

end SerreMarkov.NegativeTwoPositive
