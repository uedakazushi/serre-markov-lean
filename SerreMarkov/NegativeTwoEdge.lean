import SerreMarkov.NegativeBoundary
import SerreMarkov.NegativePairDescent
import SerreMarkov.SignGaugeDescent

/-! # Arithmetic descent at an affine edge

All reductions use actual signed mutations and integral polynomial certificates.
-/

namespace SerreMarkov.NegativeTwoEdge

open NegativeDescent NegativeTriangles NegativePairDescent NegativeBoundary

private theorem positive_triangle_two_descent (u v w : ℤ) (hu : 3 ≤ u) (hv : 2 ≤ v)
    (_hw : 2 ≤ w) (hum : u < w) (hvm : v ≤ w)
    (htri : 4 ≤ cayleyDefect u v w) : |u*v-w| < w := by
  by_cases hv2 : v = 2
  · subst v
    exact abs_lt.mpr ⟨by omega,by omega⟩
  · have hv3 : 3 ≤ v := by omega
    exact cayley_positive_abs_descent u v w hu hv3 (by omega) ⟨hum.le,hvm⟩ htri

private theorem central_max_two_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hd : 2 ≤ d) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hf : f ≤ -2) (hab : b ≤ a) (had : d ≤ a)
    (htri : 4 ≤ cayleyDefect a b d) (hdisc : gramDiscriminant a b c d e f = 0) : False := by
  have h2a : 0 ≤ 2*a-b*d := by
    by_cases hb2 : b=2
    · rw [hb2]; omega
    by_cases hd2 : d=2
    · rw [hd2]; omega
    have htri' : 4 ≤ cayleyDefect b d a := by
      convert htri using 1 <;> dsimp [cayleyDefect] <;> ring
    have h := cayley_positive_abs_descent b d a (by omega) (by omega) ha ⟨hab,had⟩ htri'
    have hh := (abs_lt.mp h).2
    omega
  have hA : 0 < a^2-4 := by nlinarith
  have hB : 0 ≤ b^2-4 := by nlinarith
  have hD : 0 ≤ d^2-4 := by nlinarith
  have habd : 0 ≤ a*b-2*d := by
    have h1 := mul_nonneg (show 0 ≤ a-d by omega) (show 0 ≤ b by omega)
    have h2 := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ d by omega)
    nlinarith
  have hadb : 0 ≤ a*d-2*b := by
    have h1 := mul_nonneg (show 0 ≤ a-b by omega) (show 0 ≤ d by omega)
    have h2 := mul_nonneg (show 0 ≤ d-2 by omega) (show 0 ≤ b by omega)
    nlinarith
  have K (a b d : ℤ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hbd : b ≤ d) (hda : d ≤ a) :
      0 < a*b*d-b^2-d^2 := by
    have hd : 2 ≤ d := by omega
    by_cases hb2 : b=2
    · rw [hb2]
      by_cases hd2 : d=2
      · rw [hd2]; nlinarith
      · have h := mul_nonneg (show 0 ≤ a-d by omega) (show 0 ≤ d by omega)
        nlinarith
    · have h1 := mul_nonneg (show 0 ≤ a-d by omega) (show 0 ≤ b*d by positivity)
      have h2 := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ d^2 by positivity)
      have h3 := sq_le_sq₀ (show 0 ≤ b by omega) (show 0 ≤ d by omega) |>.mpr hbd
      nlinarith
  have hK : 0 < a*b*d-b^2-d^2 := by
    rcases le_total b d with h | h
    · exact K a b d ha hb h had
    · have hh := K a d b ha hd h hab
      nlinarith
  let F := -f-2
  have hF : 0 ≤ F := by dsimp [F]; omega
  have hcert : gramDiscriminant a b c d e f =
      (a^2-4)*F^2 + 2*(2*(a^2-4)+(a*b-2*d)*e+(a*d-2*b)*c)*F +
      (d^2-4)*c^2+(b^2-4)*e^2+2*(2*a-b*d)*c*e +
      4*(a*d-2*b)*c+4*(a*b-2*d)*e+4*(a*b*d-b^2-d^2) := by
    dsimp [gramDiscriminant,q1,q2,F]
    ring
  have h1 : 0 ≤ (a^2-4)*F^2 := by positivity
  have h2 : 0 ≤ 2*(2*(a^2-4)+(a*b-2*d)*e+(a*d-2*b)*c)*F := by positivity
  have h3 : 0 ≤ (d^2-4)*c^2 := by positivity
  have h4 : 0 ≤ (b^2-4)*e^2 := by positivity
  have h5 : 0 ≤ 2*(2*a-b*d)*c*e := by positivity
  have h6 : 0 ≤ 4*(a*d-2*b)*c := by positivity
  have h7 : 0 ≤ 4*(a*b-2*d)*e := by positivity
  nlinarith [hcert]

theorem opposed_dominance_two_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (he : 2 ≤ e) (hf : f ≤ 0)
    (hd : a*b ≤ 2*d) (hc : a*e ≤ 2*c)
    (hdisc : gramDiscriminant a b c d e f = 0) : False := by
  let C := 2*c-a*e
  let D := 2*d-a*b
  have hC : 0 ≤ C := by dsimp [C]; omega
  have hD : 0 ≤ D := by dsimp [D]; omega
  have hA : 0 < a^2-4 := by nlinarith
  have hA2 : 0 < a^2-2 := by nlinarith
  have hab : 6 ≤ a*b := by
    have h1 := mul_nonneg (show 0 ≤ a-3 by omega) (show 0 ≤ b by omega)
    have h2 := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ (3:ℤ) by norm_num)
    nlinarith
  have hae : 6 ≤ a*e := by
    have h1 := mul_nonneg (show 0 ≤ a-3 by omega) (show 0 ≤ e by omega)
    have h2 := mul_nonneg (show 0 ≤ e-2 by omega) (show 0 ≤ (3:ℤ) by norm_num)
    nlinarith
  have hAB : 0 < a^2*b^2-16 := by nlinarith [sq_nonneg (a*b-6)]
  have hAE : 0 < a^2*e^2-16 := by nlinarith [sq_nonneg (a*e-6)]
  have hBE : 0 < b^2+e^2-4 := by nlinarith
  have hcert : 16*gramDiscriminant a b c d e f =
      C^2*D^2+2*a*b*C^2*D+C^2*(a^2*b^2-16)+2*a*e*C*D^2+
      4*b*e*(a^2-2)*C*D+2*a*b^2*e*(a^2-4)*C+D^2*(a^2*e^2-16)+
      2*a*b*e^2*(a^2-4)*D+
      (a^2-4)*((a^2-4)*b^2*e^2+16*(b^2+e^2-4))+
      16*(a^2-4)*f^2+(-8*f)*(a*C*D+(a^2-4)*(b*C+e*D+a*b*e)) := by
    dsimp [gramDiscriminant,q1,q2,C,D]
    ring
  have h1 : 0 ≤ C^2*D^2 := by positivity
  have h2 : 0 ≤ 2*a*b*C^2*D := by positivity
  have h3 : 0 ≤ C^2*(a^2*b^2-16) := by positivity
  have h4 : 0 ≤ 2*a*e*C*D^2 := by positivity
  have h5 : 0 ≤ 4*b*e*(a^2-2)*C*D := by positivity
  have h6 : 0 ≤ 2*a*b^2*e*(a^2-4)*C := by positivity
  have h7 : 0 ≤ D^2*(a^2*e^2-16) := by positivity
  have h8 : 0 ≤ 2*a*b*e^2*(a^2-4)*D := by positivity
  have h9 : 0 < (a^2-4)*((a^2-4)*b^2*e^2+16*(b^2+e^2-4)) := by positivity
  have h10 : 0 ≤ 16*(a^2-4)*f^2 := by positivity
  have h11 : 0 ≤ (-8*f)*(a*C*D+(a^2-4)*(b*C+e*D+a*b*e)) := by
    have hnf : 0 ≤ -8*f := by omega
    exact mul_nonneg hnf (by positivity)
  nlinarith [hcert]

theorem positive_pair_two_descent (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e) (hf : f ≤ -2)
    (hdisc : gramDiscriminant a b c d e f = 0)
    (htri1 : 4 ≤ cayleyDefect a b d) (htri2 : 4 ≤ cayleyDefect a c e) :
    (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  have hn1 : ¬ (b ≤ a ∧ d ≤ a) := by
    rintro ⟨hba,hda⟩
    exact central_max_two_impossible a b c d e f ha hb hd (by omega) (by omega)
      (by omega) hba hda htri1 hdisc
  have hdisc2 : gramDiscriminant a c b e d f = 0 := by
    convert hdisc using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have hn2 : ¬ (c ≤ a ∧ e ≤ a) := by
    rintro ⟨hca,hea⟩
    exact central_max_two_impossible a c b e d f ha hc he (by omega) (by omega)
      (by omega) hca hea htri2 hdisc2
  by_cases hbd : b ≤ d
  · have had : a < d := by omega
    have hdropd := positive_triangle_two_descent a b d ha hb hd had hbd htri1
    by_cases hce : c ≤ e
    · have hae : a < e := by omega
      exact Or.inl ⟨hdropd,positive_triangle_two_descent a c e ha hc he hae hce htri2⟩
    · have hac : a < c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      have hdropc := positive_triangle_two_descent a e c ha he hc hac (by omega) htri2'
      have hdomd : a*b ≤ 2*d := by have hh := (abs_lt.mp hdropd).2; omega
      have hdomc : a*e ≤ 2*c := by have hh := (abs_lt.mp hdropc).2; omega
      exact False.elim (opposed_dominance_two_impossible a b c d e f ha hb he (by omega)
        hdomd hdomc hdisc)
  · have hab : a < b := by omega
    have htri1' : 4 ≤ cayleyDefect a d b := by
      convert htri1 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hdropb := positive_triangle_two_descent a d b ha hd hb hab (by omega) htri1'
    by_cases hce : c ≤ e
    · have hae : a < e := by omega
      have hdrope := positive_triangle_two_descent a c e ha hc he hae hce htri2
      have hdomb : a*d ≤ 2*b := by have hh := (abs_lt.mp hdropb).2; omega
      have hdome : a*c ≤ 2*e := by have hh := (abs_lt.mp hdrope).2; omega
      have hdisc3 : gramDiscriminant a d e b c f = 0 := by
        convert hdisc using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
      exact False.elim (opposed_dominance_two_impossible a d e b c f ha hd hc (by omega)
        hdomb hdome hdisc3)
    · have hac : a < c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      exact Or.inr ⟨hdropb,positive_triangle_two_descent a e c ha he hc hac (by omega) htri2'⟩


/-- In the affine center, opposite strict choices of the larger outer edges
contradict the same Gram determinant equation. -/
private theorem affine_opposed_impossible (b c d e f : ℤ)
    (hb : 2 ≤ b) (he : 2 ≤ e) (hbd : b < d) (hec : e < c) (hf : f ≤ 0)
    (hdisc : gramDiscriminant 2 b c d e f = 0) : False := by
  let C := c-e
  let D := d-b
  have hC : 0 < C := by dsimp [C]; omega
  have hD : 0 < D := by dsimp [D]; omega
  have hB : 0 ≤ b^2-4 := by nlinarith
  have hE : 0 ≤ e^2-4 := by nlinarith
  have hcert : gramDiscriminant 2 b c d e f =
      C^2*D^2+2*b*C^2*D+C^2*(b^2-4)+2*e*C*D^2+
      2*b*e*C*D+D^2*(e^2-4)-4*f*C*D := by
    dsimp [gramDiscriminant,q1,q2,C,D]
    ring
  have h1 : 0 < C^2*D^2 := by positivity
  have h2 : 0 ≤ 2*b*C^2*D := by positivity
  have h3 : 0 ≤ C^2*(b^2-4) := by positivity
  have h4 : 0 ≤ 2*e*C*D^2 := by positivity
  have h5 : 0 ≤ 2*b*e*C*D := by positivity
  have h6 : 0 ≤ D^2*(e^2-4) := by positivity
  have h7 : 0 ≤ -(4*f*C*D) := by
    have hh : 4*f*C*D ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by omega : 4*f≤0) hC.le) hD.le
    omega
  nlinarith [hcert]

private theorem positive_pair_affine_descent (b c d e f : ℤ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e) (hf : f ≤ -2)
    (hbd : b ≠ d) (hce : c ≠ e) (hdisc : gramDiscriminant 2 b c d e f = 0) :
    (|2*b-d| < d ∧ |2*c-e| < e) ∨ (|2*d-b| < b ∧ |2*e-c| < c) := by
  by_cases h : b < d
  · have hh : c < e := by
      by_contra hn
      exact affine_opposed_impossible b c d e f hb he h (by omega) (by omega) hdisc
    left
    constructor <;> apply abs_lt.mpr <;> constructor <;> omega
  · have hh : e < c := by
      by_contra hn
      have hec : c < e := by omega
      have hdb : d < b := by omega
      have hdisc' : gramDiscriminant 2 d e b c f = 0 := by
        convert hdisc using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
      exact affine_opposed_impossible d e b c f hd hc hdb hec (by omega) hdisc'
    right
    constructor <;> apply abs_lt.mpr <;> constructor <;> omega

/-- With all positive outer coefficients at least two, a negative tail gives
strict simultaneous descent, except for the explicit equal-column affine case. -/
theorem positive_pair_two_dichotomy (a b c d e f : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e) (hf : f ≤ -2)
    (hdisc : gramDiscriminant a b c d e f = 0)
    (htri1 : 4 ≤ cayleyDefect a b d) (htri2 : 4 ≤ cayleyDefect a c e) :
    (a=2 ∧ (b=d ∨ c=e)) ∨
    (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  by_cases ha2 : a=2
  · subst a
    by_cases hbd : b=d
    · exact Or.inl ⟨rfl,Or.inl hbd⟩
    by_cases hce : c=e
    · exact Or.inl ⟨rfl,Or.inr hce⟩
    exact Or.inr (positive_pair_affine_descent b c d e f hb hc hd he hf hbd hce hdisc)
  · exact Or.inr (positive_pair_two_descent a b c d e f (by omega) hb hc hd he hf
      hdisc htri1 htri2)

/-- An affine edge in the middle position with equal pairings to an outside
root is transported by actual braids to the previously classified first edge. -/
theorem middle_affine_equal_family (z : Six) (hz : isSolution z)
    (hd : z.d=2) (heq : z.a=z.b ∨ z.e=z.f) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  let w := applyWord z [.i1,.i2]
  have hr : Reachable z w := ⟨[.i1,.i2],rfl⟩
  have hw : isSolution w := reachable_preserves_solution hr hz
  have ha : w.a=2 := by simp [w,applyWord,step,inv1,inv2,hd]
  have heq' : w.b=w.d ∨ w.c=w.e := by
    rcases heq with hab | hef
    · left
      simp [w,applyWord,step,inv1,inv2,hd,hab]
      ring
    · right
      simp [w,applyWord,step,inv1,inv2,hef]
  obtain ⟨x,y,hxy⟩ := affine_edge_equal_reachable_family w hw ha heq'
  exact ⟨x,y,reachable_trans hr hxy⟩

/-- The same equal-column reduction at the long diagonal is exposed by
moving the last basis root to the second position. -/
theorem diagonal_affine_equal_family (z : Six) (hz : isSolution z)
    (hc : z.c=2) (heq : z.a=z.e ∨ z.b=z.f) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  let w := applyWord z [.i3,.i2]
  have hr : Reachable z w := ⟨[.i3,.i2],rfl⟩
  have ha : w.a=2 := by simp [w,two_inverse_word_formula,hc]
  have heq' : w.b=w.d ∨ w.c=w.e := by
    rcases heq with hae | hbf
    · left
      simp [w,two_inverse_word_formula,hc,hae]
      ring
    · right
      simp [w,two_inverse_word_formula,hc,hbf]
      ring
  obtain ⟨x,y,hxy⟩ := affine_edge_equal_reachable_family w
    (reachable_preserves_solution hr hz) ha heq'
  exact ⟨x,y,reachable_trans hr hxy⟩

/-- The final affine edge with equal adjacent coefficients is moved to
the first position by four inverse braids, retaining the equal-column relation. -/
theorem right_affine_equal_family (z : Six) (hz : isSolution z)
    (hf : z.f=2) (heq : z.b=z.c ∨ z.d=z.e) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  let w := applyWord z [.i2,.i1,.i3,.i2]
  have hr : Reachable z w := ⟨[.i2,.i1,.i3,.i2],rfl⟩
  have ha : w.a=2 := by simp [w,applyWord,step,inv1,inv2,inv3,hf]
  have heq' : w.b=w.d ∨ w.c=w.e := by
    rcases heq with hbc | hde
    · left
      simp [w,applyWord,step,inv1,inv2,inv3,hf,hbc]
      ring
    · right
      simp [w,applyWord,step,inv1,inv2,inv3,hf,hde]
      ring
  obtain ⟨x,y,hxy⟩ := affine_edge_equal_reachable_family w
    (reachable_preserves_solution hr hz) ha heq'
  exact ⟨x,y,reachable_trans hr hxy⟩

/-- An actual finite family reduction or an actual strictly decreasing word. -/
def FamilyOrDrop (z : Six) : Prop :=
    (∃ x y : ℤ, Reachable z (family x y)) ∨
    ∃ word : List Generator, l1 (applyWord z word) < l1 z

private theorem one_negative_tail_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c) (hd : 2 ≤ z.d) (he : 2 ≤ z.e)
    (hf : z.f ≤ -2) : FamilyOrDrop z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hpair := positive_pair_two_dichotomy z.a z.b z.c z.d z.e z.f (by omega) hb hc hd he hf
    (solution_gramDiscriminant z hz) htri1 htri2
  rcases hpair with ⟨ha,heq⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (affine_edge_equal_reachable_family z hz ha heq)
  · right
    refine ⟨[.m1],?_⟩
    have h := (mu1_drop_iff z).mpr (by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.d),abs_of_nonneg (by omega : 0 ≤ z.e)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h
  · right
    refine ⟨[.i1],?_⟩
    have h := (inv1_drop_iff z).mpr (by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonneg (by omega : 0 ≤ z.c)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h

private theorem two_negative_middle_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c) (hd : 2 ≤ z.d)
    (he : z.e ≤ -2) (hf : z.f ≤ -2) : FamilyOrDrop z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.d z.a (-z.e) z.b (-z.f) (-z.c) = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri1' : 4 ≤ cayleyDefect z.d z.a z.b := by
    convert htri1 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri4' : 4 ≤ cayleyDefect z.d (-z.e) (-z.f) := by
    convert htri4 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_two_dichotomy z.d z.a (-z.e) z.b (-z.f) (-z.c)
    hd (by omega) (by omega) hb (by omega) (by omega) hdisc htri1' htri4'
  have hsign1 : z.d*(-z.e)-(-z.f) = -(z.d*z.e-z.f) := by ring
  have hsign2 : z.d*(-z.f)-(-z.e) = -(z.d*z.f-z.e) := by ring
  rcases hpair with ⟨hd,heq⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    exact middle_affine_equal_family z hz hd (by
      rcases heq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega))
  · right
    refine ⟨[.m2],?_⟩
    rw [hsign1,abs_neg] at h2
    have h := (mu2_drop_iff z).mpr (by
      simpa [mul_comm,abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.f ≤ 0)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h
  · right
    refine ⟨[.i2],?_⟩
    rw [hsign2,abs_neg] at h2
    have h := (inv2_drop_iff z).mpr (by
      simpa [mul_comm,abs_of_nonneg (by omega : 0 ≤ z.a),abs_of_nonpos (by omega : z.e ≤ 0)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h

private theorem two_negative_right_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : z.e ≤ -2) (hf : 2 ≤ z.f) : FamilyOrDrop z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.f z.b (-z.d) z.c (-z.e) (-z.a) = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri3' : 4 ≤ cayleyDefect z.f z.b z.c := by
    convert htri3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri4' : 4 ≤ cayleyDefect z.f (-z.d) (-z.e) := by
    convert htri4 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_two_dichotomy z.f z.b (-z.d) z.c (-z.e) (-z.a)
    hf hb (by omega) hc (by omega) (by omega) hdisc htri3' htri4'
  have hsign1 : z.f*(-z.d)-(-z.e) = -(z.f*z.d-z.e) := by ring
  have hsign2 : z.f*(-z.e)-(-z.d) = -(z.f*z.e-z.d) := by ring
  rcases hpair with ⟨hf,heq⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (right_affine_equal_family z hz hf (by
      rcases heq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)))
  · right
    refine ⟨[.m3],?_⟩
    rw [hsign1,abs_neg] at h2
    have h := (mu3_drop_iff z).mpr (by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonpos (by omega : z.e ≤ 0)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h
  · right
    refine ⟨[.i3],?_⟩
    rw [hsign2,abs_neg] at h2
    have h := (inv3_drop_iff z).mpr (by
      simpa [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.d ≤ 0)]
        using add_lt_add h1 h2)
    simpa [applyWord,step] using h

private theorem one_negative_diagonal_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : 2 ≤ z.e) (hf : 2 ≤ z.f) : FamilyOrDrop z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.c z.a z.b z.e z.f z.d = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri2' : 4 ≤ cayleyDefect z.c z.a z.e := by
    convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri3' : 4 ≤ cayleyDefect z.c z.b z.f := by
    convert htri3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_two_dichotomy z.c z.a z.b z.e z.f z.d
    hc (by omega) hb he hf hd hdisc htri2' htri3'
  rcases hpair with ⟨hc,heq⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (diagonal_affine_equal_family z hz hc heq)
  · right
    refine ⟨[.m1,.m2],?_⟩
    rw [two_forward_word_formula,l1_lt_iff]
    have hsum := add_lt_add h1 h2
    simp only [mul_comm z.c] at hsum
    simp only [integerL1]
    have hae : |z.e| = z.e := abs_of_nonneg (by omega)
    have haf : |z.f| = z.f := abs_of_nonneg (by omega)
    rw [hae,haf]
    linarith
  · right
    refine ⟨[.i3,.i2],?_⟩
    rw [two_inverse_word_formula,l1_lt_iff]
    have hsum := add_lt_add h1 h2
    simp only [integerL1]
    have haa : |z.a| = z.a := abs_of_nonneg (by omega)
    have hab : |z.b| = z.b := abs_of_nonneg (by omega)
    rw [haa,hab]
    linarith

theorem alternating_two_tail_impossible (z : Six) (hz : isSolution z)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ z.d) (he : z.e ≤ -2) (hf : 2 ≤ z.f) : False := by
  have h1 : 4 ≤ z.a*z.f := by
    have h := mul_nonneg (show 0 ≤ z.a-2 by omega) (show 0 ≤ z.f-2 by omega)
    nlinarith
  have h2 : 4 ≤ -(z.b*z.e) := by
    have h := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ -z.e-2 by omega)
    nlinarith
  have h3 : 4 ≤ z.c*z.d := by
    have h := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ z.d-2 by omega)
    nlinarith
  have hq : 12 ≤ q2 z := by dsimp [q2]; linarith
  nlinarith [hz.2]

theorem alternating_two_negative_tail_impossible (z : Six) (hz : isSolution z)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : 2 ≤ z.e) (hf : z.f ≤ -2) : False := by
  have h1 : z.a*z.f ≤ -4 := by
    have h := mul_nonneg (show 0 ≤ z.a-2 by omega) (show 0 ≤ -z.f-2 by omega)
    nlinarith
  have h2 : 4 ≤ z.b*z.e := by
    have h := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ z.e-2 by omega)
    nlinarith
  have h3 : z.c*z.d ≤ -4 := by
    have h := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ -z.d-2 by omega)
    nlinarith
  have hq : q2 z ≤ -12 := by dsimp [q2]; linarith
  nlinarith [hz.2]


/-- Every nonpositive-tail sign chamber with an affine first edge and no
edge of absolute value zero or one has an unconditional arithmetic reduction. -/
theorem nonpositive_tail_atLeastTwo_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ z.a) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ |z.d|) (he : 2 ≤ |z.e|) (hf : 2 ≤ |z.f|)
    (hminus : z.d < 0 ∨ z.e < 0 ∨ z.f < 0) : FamilyOrDrop z := by
  have hd' : 2 ≤ z.d ∨ z.d ≤ -2 := by
    rcases le_abs.mp hd with h | h <;> omega
  have he' : 2 ≤ z.e ∨ z.e ≤ -2 := by
    rcases le_abs.mp he with h | h <;> omega
  have hf' : 2 ≤ z.f ∨ z.f ≤ -2 := by
    rcases le_abs.mp hf with h | h <;> omega
  rcases hd' with hd | hd <;> rcases he' with he | he <;> rcases hf' with hf | hf
  · omega
  · exact one_negative_tail_two_reduction z hz hneg ha hb hc hd he hf
  · exact False.elim (alternating_two_tail_impossible z hz (by omega) hb hc hd he hf)
  · exact two_negative_middle_two_reduction z hz hneg ha hb hc hd he hf
  · exact one_negative_diagonal_two_reduction z hz hneg ha hb hc hd he hf
  · exact False.elim (alternating_two_negative_tail_impossible z hz (by omega) hb hc hd he hf)
  · exact two_negative_right_two_reduction z hz hneg ha hb hc hd he hf
  · exact False.elim (SignChambers.solution_not_all_negative_tail z hz (by omega) hb hc hd he hf)

/-- The affine-first-edge specialization of the stronger universal sign
chamber theorem. -/
theorem nonpositive_tail_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : z.a=2) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ |z.d|) (he : 2 ≤ |z.e|) (hf : 2 ≤ |z.f|)
    (hminus : z.d < 0 ∨ z.e < 0 ∨ z.f < 0) : FamilyOrDrop z :=
  nonpositive_tail_atLeastTwo_reduction z hz hneg (by omega) hb hc hd he hf hminus

/-- Both alternatives transfer through an arbitrary initial sign gauge. -/
theorem familyOrDrop_of_gauge (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1)
    (h : FamilyOrDrop (PositiveNormalization.signedSix z s)) : FamilyOrDrop z := by
  rcases h with ⟨x,y,hxy⟩ | ⟨word,hdrop⟩
  · exact Or.inl ⟨x,y,reachable_trans
      (PositiveNormalization.signedSix_reachable z s hs) hxy⟩
  · exact Or.inr ⟨word,SignGaugeDescent.descent_transfer z s hs word hdrop⟩

/-- Normalize the signs with an explicit height-preserving gauge, exposing all
the hypotheses needed by the two affine-edge sign-chamber reductions. -/
theorem first_row_two_normalization (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : |z.a|=2)
    (hb : 2 ≤ |z.b|) (hc : 2 ≤ |z.c|) (hd : 2 ≤ |z.d|)
    (he : 2 ≤ |z.e|) (hf : 2 ≤ |z.f|) :
    ∃ w : Six, Reachable z w ∧ isSolution w ∧ IntrinsicSigns.thirdMinorSum w<0 ∧
      w.a=2 ∧ 2≤w.b ∧ 2≤w.c ∧ 2≤|w.d| ∧ 2≤|w.e| ∧ 2≤|w.f| ∧
      l1 w=l1 z ∧ (FamilyOrDrop w → FamilyOrDrop z) := by
  let s := SignGaugeDescent.firstRowSigns z
  have hs : ∀ i,(s i)^2=1 := SignGaugeDescent.firstRowSigns_square z
  let w := PositiveNormalization.signedSix z s
  have hr : Reachable z w := PositiveNormalization.signedSix_reachable z s hs
  have habc := SignGaugeDescent.firstRowSigns_normalizes z
  have habs := SignGaugeDescent.signedSix_abs z s hs
  have hm : IntrinsicSigns.thirdMinorSum w=IntrinsicSigns.thirdMinorSum z := by
    exact SignGaugeDescent.negativeMarker_signedSix z s hs
  refine ⟨w,hr,reachable_preserves_solution hr hz,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact hneg
  · exact habc.1.trans ha
  · simpa only [w,s,habc.2.1] using hb
  · simpa only [w,s,habc.2.2] using hc
  · simpa only [w,habs.2.2.2.1] using hd
  · simpa only [w,habs.2.2.2.2.1] using he
  · simpa only [w,habs.2.2.2.2.2] using hf
  · exact SignGaugeDescent.l1_signedSix z s hs
  · exact familyOrDrop_of_gauge z s hs

end SerreMarkov.NegativeTwoEdge
