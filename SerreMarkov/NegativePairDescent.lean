import SerreMarkov.NegativeTriangles
import SerreMarkov.NegativeDescent
import SerreMarkov.SignChambers

/-! # Simultaneous descent for two positive Lorentz triangles

The polynomial certificates below exclude opposite choices of the largest
triangle edges. They are universal integer inequalities, without a search bound.
-/

namespace SerreMarkov.NegativePairDescent

open NegativeTriangles NegativeDescent

def gramDiscriminant (a b c d e f : ℤ) : ℤ :=
  q2 ⟨a,b,c,d,e,f⟩ ^ 2 - 4 * q1 ⟨a,b,c,d,e,f⟩ + 16

theorem solution_gramDiscriminant (z : Six) (hz : isSolution z) :
    gramDiscriminant z.a z.b z.c z.d z.e z.f = 0 := by
  have he : (⟨z.a,z.b,z.c,z.d,z.e,z.f⟩ : Six) = z := by cases z; rfl
  simp only [gramDiscriminant, he, hz.1, hz.2]
  norm_num

theorem central_max_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hd : 3 ≤ d) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hf : f ≤ -2) (hab : b ≤ a) (had : d ≤ a)
    (htri : 4 ≤ cayleyDefect a b d) (hdisc : gramDiscriminant a b c d e f = 0) : False := by
  have htri' : 4 ≤ cayleyDefect b d a := by
    convert htri using 1 <;> dsimp [cayleyDefect] <;> ring
  have habs := cayley_signed_abs_descent b d a (by simpa [abs_of_nonneg (by omega : 0 ≤ b)] using hb)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ d)] using hd)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ a)] using ha)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ b), abs_of_nonneg (by omega : 0 ≤ d),
      abs_of_nonneg (by omega : 0 ≤ a)] using And.intro hab had)
    (by positivity) htri'
  rw [abs_of_nonneg (by omega : 0 ≤ a)] at habs
  have h2a : 0 < 2*a-b*d := by have h := (abs_lt.mp habs).2; linarith
  have hA : 0 < a^2-4 := by nlinarith
  have hB : 0 < b^2-4 := by nlinarith
  have hD : 0 < d^2-4 := by nlinarith
  have habd : 0 < a*b-2*d := by
    have h1 := mul_nonneg (show 0 ≤ a-d by omega) (show 0 ≤ b by omega)
    have h2 := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ d by omega)
    nlinarith
  have hadb : 0 < a*d-2*b := by
    have h1 := mul_nonneg (show 0 ≤ a-b by omega) (show 0 ≤ d by omega)
    have h2 := mul_nonneg (show 0 ≤ d-3 by omega) (show 0 ≤ b by omega)
    nlinarith
  have hK : 0 < a*b*d-b^2-d^2 := by
    by_cases hbd : b ≤ d
    · have h1 := mul_nonneg (show 0 ≤ a-d by omega) (show 0 ≤ b*d by positivity)
      have h2 := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ d^2 by positivity)
      have h3 := sq_le_sq₀ (show 0 ≤ b by omega) (show 0 ≤ d by omega) |>.mpr hbd
      nlinarith
    · have h1 := mul_nonneg (show 0 ≤ a-b by omega) (show 0 ≤ b*d by positivity)
      have h2 := mul_nonneg (show 0 ≤ d-3 by omega) (show 0 ≤ b^2 by positivity)
      have h3 := sq_le_sq₀ (show 0 ≤ d by omega) (show 0 ≤ b by omega) |>.mpr (by omega : d ≤ b)
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

theorem opposed_dominance_impossible (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (he : 3 ≤ e) (hf : f ≤ 0)
    (hd : a*b ≤ 2*d) (hc : a*e ≤ 2*c)
    (hdisc : gramDiscriminant a b c d e f = 0) : False := by
  let C := 2*c-a*e
  let D := 2*d-a*b
  have hC : 0 ≤ C := by dsimp [C]; omega
  have hD : 0 ≤ D := by dsimp [D]; omega
  have hA : 0 < a^2-4 := by nlinarith
  have hA2 : 0 < a^2-2 := by nlinarith
  have hab : 9 ≤ a*b := by
    have h1 := mul_nonneg (show 0 ≤ a-3 by omega) (show 0 ≤ b by omega)
    have h2 := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ (3:ℤ) by norm_num)
    nlinarith
  have hae : 9 ≤ a*e := by
    have h1 := mul_nonneg (show 0 ≤ a-3 by omega) (show 0 ≤ e by omega)
    have h2 := mul_nonneg (show 0 ≤ e-3 by omega) (show 0 ≤ (3:ℤ) by norm_num)
    nlinarith
  have hAB : 0 < a^2*b^2-16 := by nlinarith [sq_nonneg (a*b-9)]
  have hAE : 0 < a^2*e^2-16 := by nlinarith [sq_nonneg (a*e-9)]
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

private theorem positive_triangle_descent (u v w : ℤ) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hw : 3 ≤ w) (hum : u ≤ w) (hvm : v ≤ w) (htri : 4 ≤ cayleyDefect u v w) :
    |u*v-w| < w := by
  have h := cayley_signed_abs_descent u v w
    (by simpa [abs_of_nonneg (by omega : 0 ≤ u)] using hu)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ v)] using hv)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ w)] using hw)
    (by simpa [abs_of_nonneg (by omega : 0 ≤ u), abs_of_nonneg (by omega : 0 ≤ v),
      abs_of_nonneg (by omega : 0 ≤ w)] using And.intro hum hvm)
    (by positivity) htri
  simpa [abs_of_nonneg (by omega : 0 ≤ w)] using h

theorem positive_pair_descent (a b c d e f : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e) (hf : f ≤ -3)
    (hdisc : gramDiscriminant a b c d e f = 0)
    (htri1 : 4 ≤ cayleyDefect a b d) (htri2 : 4 ≤ cayleyDefect a c e) :
    (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  have hn1 : ¬ (b ≤ a ∧ d ≤ a) := by
    rintro ⟨hba,hda⟩
    exact central_max_impossible a b c d e f ha hb hd (by omega) (by omega)
      (by omega) hba hda htri1 hdisc
  have hdisc2 : gramDiscriminant a c b e d f = 0 := by
    convert hdisc using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have hn2 : ¬ (c ≤ a ∧ e ≤ a) := by
    rintro ⟨hca,hea⟩
    exact central_max_impossible a c b e d f ha hc he (by omega) (by omega)
      (by omega) hca hea htri2 hdisc2
  by_cases hbd : b ≤ d
  · have had : a ≤ d := by omega
    have hdropd := positive_triangle_descent a b d ha hb hd had hbd htri1
    by_cases hce : c ≤ e
    · have hae : a ≤ e := by omega
      exact Or.inl ⟨hdropd,positive_triangle_descent a c e ha hc he hae hce htri2⟩
    · have hac : a ≤ c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      have hdropc := positive_triangle_descent a e c ha he hc hac (by omega) htri2'
      have hdomd : a*b ≤ 2*d := by have hh := (abs_lt.mp hdropd).2; omega
      have hdomc : a*e ≤ 2*c := by have hh := (abs_lt.mp hdropc).2; omega
      exact False.elim (opposed_dominance_impossible a b c d e f ha hb he (by omega)
        hdomd hdomc hdisc)
  · have hab : a ≤ b := by omega
    have htri1' : 4 ≤ cayleyDefect a d b := by
      convert htri1 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hdropb := positive_triangle_descent a d b ha hd hb hab (by omega) htri1'
    by_cases hce : c ≤ e
    · have hae : a ≤ e := by omega
      have hdrope := positive_triangle_descent a c e ha hc he hae hce htri2
      have hdomb : a*d ≤ 2*b := by have hh := (abs_lt.mp hdropb).2; omega
      have hdome : a*c ≤ 2*e := by have hh := (abs_lt.mp hdrope).2; omega
      have hdisc3 : gramDiscriminant a d e b c f = 0 := by
        convert hdisc using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
      exact False.elim (opposed_dominance_impossible a d e b c f ha hd hc (by omega)
        hdomb hdome hdisc3)
    · have hac : a ≤ c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      exact Or.inr ⟨hdropb,positive_triangle_descent a e c ha he hc hac (by omega) htri2'⟩

theorem one_negative_tail_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c) (hd : 3 ≤ z.d) (he : 3 ≤ z.e)
    (hf : z.f ≤ -3) : l1 (mu1 z) < l1 z ∨ l1 (inv1 z) < l1 z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hpair := positive_pair_descent z.a z.b z.c z.d z.e z.f ha hb hc hd he hf
    (solution_gramDiscriminant z hz) htri1 htri2
  rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    rw [mu1_drop_iff]
    simpa [abs_of_nonneg (by omega : 0 ≤ z.d), abs_of_nonneg (by omega : 0 ≤ z.e)]
      using add_lt_add h1 h2
  · right
    rw [inv1_drop_iff]
    simpa [abs_of_nonneg (by omega : 0 ≤ z.b), abs_of_nonneg (by omega : 0 ≤ z.c)]
      using add_lt_add h1 h2

theorem two_negative_middle_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c) (hd : 3 ≤ z.d)
    (he : z.e ≤ -3) (hf : z.f ≤ -3) : l1 (mu2 z) < l1 z ∨ l1 (inv2 z) < l1 z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.d z.a (-z.e) z.b (-z.f) (-z.c) = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri1' : 4 ≤ cayleyDefect z.d z.a z.b := by
    convert htri1 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri4' : 4 ≤ cayleyDefect z.d (-z.e) (-z.f) := by
    convert htri4 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_descent z.d z.a (-z.e) z.b (-z.f) (-z.c)
    hd ha (by omega) hb (by omega) (by omega) hdisc htri1' htri4'
  have hsign1 : z.d*(-z.e)-(-z.f) = -(z.d*z.e-z.f) := by ring
  have hsign2 : z.d*(-z.f)-(-z.e) = -(z.d*z.f-z.e) := by ring
  rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    rw [hsign1,abs_neg] at h2
    rw [mu2_drop_iff]
    simpa [mul_comm,abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.f ≤ 0)]
      using add_lt_add h1 h2
  · right
    rw [hsign2,abs_neg] at h2
    rw [inv2_drop_iff]
    simpa [mul_comm,abs_of_nonneg (by omega : 0 ≤ z.a),abs_of_nonpos (by omega : z.e ≤ 0)]
      using add_lt_add h1 h2

theorem two_negative_right_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : z.e ≤ -3) (hf : 3 ≤ z.f) :
    l1 (mu3 z) < l1 z ∨ l1 (inv3 z) < l1 z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.f z.b (-z.d) z.c (-z.e) (-z.a) = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri3' : 4 ≤ cayleyDefect z.f z.b z.c := by
    convert htri3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri4' : 4 ≤ cayleyDefect z.f (-z.d) (-z.e) := by
    convert htri4 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_descent z.f z.b (-z.d) z.c (-z.e) (-z.a)
    hf hb (by omega) hc (by omega) (by omega) hdisc htri3' htri4'
  have hsign1 : z.f*(-z.d)-(-z.e) = -(z.f*z.d-z.e) := by ring
  have hsign2 : z.f*(-z.e)-(-z.d) = -(z.f*z.e-z.d) := by ring
  rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    rw [hsign1,abs_neg] at h2
    rw [mu3_drop_iff]
    simpa [abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonpos (by omega : z.e ≤ 0)]
      using add_lt_add h1 h2
  · right
    rw [hsign2,abs_neg] at h2
    rw [inv3_drop_iff]
    simpa [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.d ≤ 0)]
      using add_lt_add h1 h2

theorem two_forward_word_formula (z : Six) :
    applyWord z [.m1,.m2] = ⟨z.d,z.a,z.a*z.c-z.e,z.b,z.b*z.c-z.f,z.c⟩ := by
  ext <;> simp [applyWord,step,mu1,mu2] <;> ring

theorem two_inverse_word_formula (z : Six) :
    applyWord z [.i3,.i2] = ⟨z.c,z.c*z.e-z.a,z.c*z.f-z.b,z.e,z.f,z.d⟩ := by
  ext <;> simp [applyWord,step,inv3,inv2] <;> ring

theorem one_negative_diagonal_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : 3 ≤ z.e) (hf : 3 ≤ z.f) :
    l1 (applyWord z [.m1,.m2]) < l1 z ∨ l1 (applyWord z [.i3,.i2]) < l1 z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hdisc : gramDiscriminant z.c z.a z.b z.e z.f z.d = 0 := by
    convert solution_gramDiscriminant z hz using 1 <;> dsimp [gramDiscriminant,q1,q2] <;> ring
  have htri2' : 4 ≤ cayleyDefect z.c z.a z.e := by
    convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri3' : 4 ≤ cayleyDefect z.c z.b z.f := by
    convert htri3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have hpair := positive_pair_descent z.c z.a z.b z.e z.f z.d
    hc ha hb he hf hd hdisc htri2' htri3'
  rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    rw [two_forward_word_formula,l1_lt_iff]
    have hsum := add_lt_add h1 h2
    simp only [mul_comm z.c] at hsum
    simp only [integerL1]
    have hae : |z.e| = z.e := abs_of_nonneg (by omega)
    have haf : |z.f| = z.f := abs_of_nonneg (by omega)
    rw [hae,haf]
    linarith
  · right
    rw [two_inverse_word_formula,l1_lt_iff]
    have hsum := add_lt_add h1 h2
    simp only [integerL1]
    have haa : |z.a| = z.a := abs_of_nonneg (by omega)
    have hab : |z.b| = z.b := abs_of_nonneg (by omega)
    rw [haa,hab]
    linarith

theorem alternating_tail_impossible (z : Six) (hz : isSolution z)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : z.e ≤ -3) (hf : 3 ≤ z.f) : False := by
  have h1 : 9 ≤ z.a*z.f := by
    have h := mul_nonneg (show 0 ≤ z.a-3 by omega) (show 0 ≤ z.f-3 by omega)
    nlinarith
  have h2 : 9 ≤ -(z.b*z.e) := by
    have h := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ -z.e-3 by omega)
    nlinarith
  have h3 : 9 ≤ z.c*z.d := by
    have h := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ z.d-3 by omega)
    nlinarith
  have hq : 27 ≤ q2 z := by dsimp [q2]; linarith
  nlinarith [hz.2]

theorem alternating_negative_tail_impossible (z : Six) (hz : isSolution z)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : 3 ≤ z.e) (hf : z.f ≤ -3) : False := by
  have h1 : z.a*z.f ≤ -9 := by
    have h := mul_nonneg (show 0 ≤ z.a-3 by omega) (show 0 ≤ -z.f-3 by omega)
    nlinarith
  have h2 : 9 ≤ z.b*z.e := by
    have h := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ z.e-3 by omega)
    nlinarith
  have h3 : z.c*z.d ≤ -9 := by
    have h := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ -z.d-3 by omega)
    nlinarith
  have hq : q2 z ≤ -27 := by dsimp [q2]; linarith
  nlinarith [hz.2]

theorem nonpositive_tail_large_word_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 3 ≤ z.a) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|)
    (hminus : z.d < 0 ∨ z.e < 0 ∨ z.f < 0) :
    ∃ word : List Generator, word.length ≤ 2 ∧
      (∀ g ∈ word, g ∈ braidMoves) ∧ l1 (applyWord z word) < l1 z := by
  have hd' : 3 ≤ z.d ∨ z.d ≤ -3 := by
    rcases le_abs.mp hd with h | h <;> omega
  have he' : 3 ≤ z.e ∨ z.e ≤ -3 := by
    rcases le_abs.mp he with h | h <;> omega
  have hf' : 3 ≤ z.f ∨ z.f ≤ -3 := by
    rcases le_abs.mp hf with h | h <;> omega
  rcases hd' with hd | hd <;> rcases he' with he | he <;> rcases hf' with hf | hf
  · omega
  · rcases one_negative_tail_drop z hz hneg ha hb hc hd he hf with h | h
    · exact ⟨[.m1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · exact False.elim (alternating_tail_impossible z hz ha hb hc hd he hf)
  · rcases two_negative_middle_drop z hz hneg ha hb hc hd he hf with h | h
    · exact ⟨[.m2],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i2],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · rcases one_negative_diagonal_drop z hz hneg ha hb hc hd he hf with h | h
    · exact ⟨[.m1,.m2],by decide,by simp [braidMoves],h⟩
    · exact ⟨[.i3,.i2],by decide,by simp [braidMoves],h⟩
  · exact False.elim (alternating_negative_tail_impossible z hz ha hb hc hd he hf)
  · rcases two_negative_right_drop z hz hneg ha hb hc hd he hf with h | h
    · exact ⟨[.m3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · exact False.elim (SignChambers.solution_not_all_negative_tail z hz (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))

end SerreMarkov.NegativePairDescent
