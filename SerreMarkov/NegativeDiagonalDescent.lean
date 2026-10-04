import SerreMarkov.NegativeTriangleOrder
import SerreMarkov.NegativeDescent

/-! # Strict descent when a diagonal is the largest positive pairing

Only the four triangle inequalities and the small Pfaffian are used. No
solution of a local-descent cutpoint or classification hypothesis is assumed.
-/

namespace SerreMarkov.NegativeDiagonalDescent

open NegativeTriangles NegativeTriangleOrder NegativeDescent
set_option maxHeartbeats 1000000

private theorem triangle_gap (u v w : ℤ) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hmax : u ≤ w ∧ v ≤ w) (hc : 4 ≤ cayleyDefect u v w) :
    3*u < 2*w ∧ 3*v < 2*w := by
  have h := positive_triangle_max_gap u v w hu hv hmax hc
  have hu' := le_max_left u v
  have hv' := le_max_right u v
  constructor <;> omega

private theorem scaled_product_lt (a b e f : ℤ) (hb : 0 < b) (he : 0 < e)
    (hf : 0 < f) (ha : 3*a < 2*b) (hf' : 3*f < 2*e) :
    9*(a*f) < 4*(b*e) := by
  have h1 : 0 < (2*b-3*a)*(3*f) := mul_pos (by omega) (by omega)
  have h2 : 0 < (2*e-3*f)*(2*b) := mul_pos (by omega) (by omega)
  nlinarith [h1,h2]

/-- The staggered chain of largest edges contradicts the Pfaffian bound. -/
theorem staggered_max_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e) (hf : 3 ≤ f)
    (hba : 3*a < 2*b) (hbc : 3*c < 2*b)
    (hed : 3*d < 2*e) (hef : 3*f < 2*e) (hae : 3*e < 2*a)
    (hq : -4 ≤ a*f-b*e+c*d) : False := by
  have h1 := scaled_product_lt a b e f (by omega) (by omega) (by omega) hba hef
  have h2 := scaled_product_lt c b e d (by omega) (by omega) (by omega) hbc hed
  have hbe : b*e < 36 := by linarith
  have he5 : 5 ≤ e := by omega
  have ha8 : 8 ≤ a := by omega
  have hb13 : 13 ≤ b := by omega
  have hp : 0 ≤ (b-13)*(e-5) := mul_nonneg (by omega) (by omega)
  nlinarith

/-- If both remaining triangles are centered at the other diagonal, their
four smaller edges cannot realize a Pfaffian of absolute value four. -/
theorem double_diagonal_max_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e) (hf : 3 ≤ f)
    (heb : e ≤ b) (hea : 3*a < 2*e) (hec : 3*c < 2*e)
    (hed : 3*d < 2*e) (hef : 3*f < 2*e)
    (hq : -4 ≤ a*f-b*e+c*d) : False := by
  by_cases he7 : 7 ≤ e
  · have h1 := scaled_product_lt a e e f (by omega) (by omega) (by omega) hea hef
    have h2 := scaled_product_lt c e e d (by omega) (by omega) (by omega) hec hed
    have hp : 0 ≤ (b-e)*e := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (e-7)]
  · have ha3 : a = 3 := by omega
    have hc3 : c = 3 := by omega
    have hd3 : d = 3 := by omega
    have hf3 : f = 3 := by omega
    subst a; subst c; subst d; subst f
    have he5 : 5 ≤ e := by omega
    have hb5 : 5 ≤ b := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ b-5) (by omega : 0 ≤ e-5)]

/-- A largest `b` diagonal forces one elementary braid to reduce the height. -/
theorem b_max_drop (z : Six)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : 3 ≤ z.e) (hf : 3 ≤ z.f)
    (hq : q2 z^2 = 16)
    (htri : 4 ≤ cayleyDefect z.a z.b z.d ∧ 4 ≤ cayleyDefect z.a z.c z.e ∧
      4 ≤ cayleyDefect z.b z.c z.f ∧ 4 ≤ cayleyDefect z.d z.e z.f)
    (hmax : z.a ≤ z.b ∧ z.c ≤ z.b ∧ z.d ≤ z.b ∧ z.e ≤ z.b ∧ z.f ≤ z.b) :
    OneStepDrop z := by
  obtain ⟨h1,h2,h3,h4⟩ := htri
  obtain ⟨hab,hcb,hdb,heb,hfb⟩ := hmax
  have h1' : 4 ≤ cayleyDefect z.a z.d z.b := by
    convert h1 using 1 <;> dsimp [cayleyDefect] <;> ring
  have h3' : 4 ≤ cayleyDefect z.c z.f z.b := by
    convert h3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hdropb1 := cayley_positive_abs_descent z.a z.d z.b ha hd hb ⟨hab,hdb⟩ h1'
  have hdropb3 := cayley_positive_abs_descent z.c z.f z.b hc hf hb ⟨hcb,hfb⟩ h3'
  have hgapb1 := triangle_gap z.a z.d z.b ha hd ⟨hab,hdb⟩ h1'
  have hgapb3 := triangle_gap z.c z.f z.b hc hf ⟨hcb,hfb⟩ h3'
  have hql : -4 ≤ q2 z := by nlinarith only [hq]
  change -4 ≤ z.a*z.f-z.b*z.e+z.c*z.d at hql
  have drop_d (hed : z.e ≤ z.d) (hfd : z.f ≤ z.d) : OneStepDrop z := by
    have h4' : 4 ≤ cayleyDefect z.f z.e z.d := by
      convert h4 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hdropd := cayley_positive_abs_descent z.f z.e z.d hf he hd ⟨hfd,hed⟩ h4'
    have hh : |z.f*z.c-z.b|+|z.f*z.e-z.d| < |z.b|+|z.d| := by
      simpa [mul_comm z.c z.f,abs_of_nonneg (by omega : 0 ≤ z.b),
        abs_of_nonneg (by omega : 0 ≤ z.d)] using add_lt_add hdropb3 hdropd
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((inv3_drop_iff z).mpr hh)))))
  have drop_f (hdf : z.d ≤ z.f) (hef : z.e ≤ z.f) : OneStepDrop z := by
    have hdropf := cayley_positive_abs_descent z.d z.e z.f hd he hf ⟨hdf,hef⟩ h4
    have hh : |z.a*z.d-z.b|+|z.d*z.e-z.f| < |z.b|+|z.f| := by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonneg (by omega : 0 ≤ z.f)]
        using add_lt_add hdropb1 hdropf
    exact Or.inr (Or.inr (Or.inl ((mu2_drop_iff z).mpr hh)))
  have drop_c (hac : z.a ≤ z.c) (hec : z.e ≤ z.c) : OneStepDrop z := by
    have h2' : 4 ≤ cayleyDefect z.a z.e z.c := by
      convert h2 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hdropc := cayley_positive_abs_descent z.a z.e z.c ha he hc ⟨hac,hec⟩ h2'
    have hh : |z.a*z.d-z.b|+|z.a*z.e-z.c| < |z.b|+|z.c| := by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonneg (by omega : 0 ≤ z.c)]
        using add_lt_add hdropb1 hdropc
    exact Or.inr (Or.inl ((inv1_drop_iff z).mpr hh))
  have drop_e (hde : z.d ≤ z.e) (hfe : z.f ≤ z.e) : OneStepDrop z := by
    have h4' : 4 ≤ cayleyDefect z.d z.f z.e := by
      convert h4 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hgape := triangle_gap z.d z.f z.e hd hf ⟨hde,hfe⟩ h4'
    by_cases hac : z.a ≤ z.c
    · by_cases hec : z.e ≤ z.c
      · exact drop_c hac hec
      · have hce : z.c ≤ z.e := by omega
        have hae : z.a ≤ z.e := by omega
        have hg := triangle_gap z.a z.c z.e ha hc ⟨hae,hce⟩ h2
        exact False.elim (double_diagonal_max_impossible z.a z.b z.c z.d z.e z.f
          ha hb hc hd he hf heb hg.1 hg.2 hgape.1 hgape.2 hql)
    · by_cases hea : z.e ≤ z.a
      · have hca : z.c ≤ z.a := by omega
        have h2' : 4 ≤ cayleyDefect z.c z.e z.a := by
          convert h2 using 1 <;> dsimp [cayleyDefect] <;> ring
        have hg := triangle_gap z.c z.e z.a hc he ⟨hca,hea⟩ h2'
        exact False.elim (staggered_max_impossible z.a z.b z.c z.d z.e z.f
          ha hb hc hd he hf hgapb1.1 hgapb3.1 hgape.1 hgape.2 hg.2 hql)
      · have hae : z.a ≤ z.e := by omega
        have hce : z.c ≤ z.e := by omega
        have hg := triangle_gap z.a z.c z.e ha hc ⟨hae,hce⟩ h2
        exact False.elim (double_diagonal_max_impossible z.a z.b z.c z.d z.e z.f
          ha hb hc hd he hf heb hg.1 hg.2 hgape.1 hgape.2 hql)
  rcases le_total z.d z.e with hde | hed
  · by_cases hfe : z.f ≤ z.e
    · exact drop_e hde hfe
    · exact drop_f (by omega) (by omega)
  · by_cases hfd : z.f ≤ z.d
    · exact drop_d hed hfd
    · exact drop_f (by omega) (by omega)

def reverse (z : Six) : Six := ⟨z.f,z.e,z.c,z.d,z.b,z.a⟩

@[simp] theorem reverse_reverse (z : Six) : reverse (reverse z) = z := by cases z; rfl
@[simp] theorem reverse_q2 (z : Six) : q2 (reverse z) = q2 z := by dsimp [reverse,q2]; ring
@[simp] theorem reverse_l1 (z : Six) : l1 (reverse z) = l1 z := by dsimp [reverse,l1]; omega

theorem reverse_mu1 (z : Six) : reverse (mu1 z) = inv3 (reverse z) := by
  ext <;> dsimp [reverse,mu1,inv3] <;> ring

theorem reverse_inv1 (z : Six) : reverse (inv1 z) = mu3 (reverse z) := by
  ext <;> dsimp [reverse,inv1,mu3] <;> ring

theorem reverse_mu2 (z : Six) : reverse (mu2 z) = inv2 (reverse z) := by
  ext <;> dsimp [reverse,mu2,inv2] <;> ring

theorem reverse_inv2 (z : Six) : reverse (inv2 z) = mu2 (reverse z) := by
  ext <;> dsimp [reverse,inv2,mu2] <;> ring

theorem reverse_mu3 (z : Six) : reverse (mu3 z) = inv1 (reverse z) := by
  ext <;> dsimp [reverse,mu3,inv1] <;> ring

theorem reverse_inv3 (z : Six) : reverse (inv3 z) = mu1 (reverse z) := by
  ext <;> dsimp [reverse,inv3,mu1] <;> ring

theorem oneStepDrop_of_reverse (z : Six) (h : OneStepDrop (reverse z)) : OneStepDrop z := by
  rcases h with h | h | h | h | h | h
  · rw [← reverse_inv3,reverse_l1,reverse_l1] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [← reverse_mu3,reverse_l1,reverse_l1] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rw [← reverse_inv2,reverse_l1,reverse_l1] at h
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [← reverse_mu2,reverse_l1,reverse_l1] at h
    exact Or.inr (Or.inr (Or.inl h))
  · rw [← reverse_inv1,reverse_l1,reverse_l1] at h
    exact Or.inr (Or.inl h)
  · rw [← reverse_mu1,reverse_l1,reverse_l1] at h
    exact Or.inl h

/-- The other diagonal is the first one after reversing the four roots. -/
theorem e_max_drop (z : Six)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : 3 ≤ z.e) (hf : 3 ≤ z.f)
    (hq : q2 z^2 = 16)
    (htri : 4 ≤ cayleyDefect z.a z.b z.d ∧ 4 ≤ cayleyDefect z.a z.c z.e ∧
      4 ≤ cayleyDefect z.b z.c z.f ∧ 4 ≤ cayleyDefect z.d z.e z.f)
    (hmax : z.a ≤ z.e ∧ z.b ≤ z.e ∧ z.c ≤ z.e ∧ z.d ≤ z.e ∧ z.f ≤ z.e) :
    OneStepDrop z := by
  obtain ⟨h1,h2,h3,h4⟩ := htri
  obtain ⟨hae,hbe,hce,hde,hfe⟩ := hmax
  have htri' : 4 ≤ cayleyDefect (reverse z).a (reverse z).b (reverse z).d ∧
      4 ≤ cayleyDefect (reverse z).a (reverse z).c (reverse z).e ∧
      4 ≤ cayleyDefect (reverse z).b (reverse z).c (reverse z).f ∧
      4 ≤ cayleyDefect (reverse z).d (reverse z).e (reverse z).f := by
    refine ⟨?_,?_,?_,?_⟩
    · convert h4 using 1 <;> dsimp [reverse,cayleyDefect] <;> ring
    · convert h3 using 1 <;> dsimp [reverse,cayleyDefect] <;> ring
    · convert h2 using 1 <;> dsimp [reverse,cayleyDefect] <;> ring
    · convert h1 using 1 <;> dsimp [reverse,cayleyDefect] <;> ring
  apply oneStepDrop_of_reverse
  exact b_max_drop (reverse z) hf he hc hd hb ha
    (by simpa only [reverse_q2] using hq) htri' ⟨hfe,hce,hde,hbe,hae⟩

end SerreMarkov.NegativeDiagonalDescent
