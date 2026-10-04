import SerreMarkov.NegativePairDescent
import SerreMarkov.SignGaugeDescent

/-! # Algebraic descent at a unit edge

The certificates below are polynomial identities and inequalities over all
integers. No bounded search is used in their proofs.
-/

namespace SerreMarkov.NegativeUnitEdge

open NegativeDescent NegativePairDescent

theorem unit_q1_identity (b c d e f : ℤ) :
    q1 ⟨1,b,c,d,e,f⟩ =
      f^2-(b*c+d*e-c*d)*f+(b^2-b*d+d^2)+(c^2-c*e+e^2)+1 := by
  dsimp [q1]
  ring

theorem unit_q2_sign (z : Six) (hz : isSolution z) (ha : z.a = 1) :
    z.f-z.b*z.e+z.c*z.d = 4 ∨ z.f-z.b*z.e+z.c*z.d = -4 := by
  have h := hz.2
  simp only [q2,ha,one_mul] at h
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num
  exact h

private theorem shifted_opposed_q1_lt (X Y t u k : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hk : k = 4 ∨ k = -4) :
    q1 ⟨1,2*(X+3)+t,2*(Y+3)+u,-(X+3),Y+3,
      (2*(X+3)+t)*(Y+3)+(2*(Y+3)+u)*(X+3)+k⟩ < 8 := by
  rcases hk with rfl | rfl
  all_goals
    apply sub_pos.mp
    dsimp [q1]
    ring_nf
    positivity

theorem unit_opposed_bounds_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hd : z.d ≤ -3) (he : 3 ≤ z.e)
    (hb : -2*z.d ≤ z.b) (hc : 2*z.e ≤ z.c) : False := by
  have hX : 0 ≤ -z.d-3 := by omega
  have hY : 0 ≤ z.e-3 := by omega
  have ht : 0 ≤ z.b+2*z.d := by omega
  have hu : 0 ≤ z.c-2*z.e := by omega
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hlt := shifted_opposed_q1_lt (-z.d-3) (z.e-3) (z.b+2*z.d)
      (z.c-2*z.e) (z.f-z.b*z.e+z.c*z.d) hX hY ht hu (by omega)
    have heq : (⟨1,2*(-z.d-3+3)+(z.b+2*z.d),2*(z.e-3+3)+(z.c-2*z.e),
        -(-z.d-3+3),z.e-3+3,
        (2*(-z.d-3+3)+(z.b+2*z.d))*(z.e-3+3)+
        (2*(z.e-3+3)+(z.c-2*z.e))*(-z.d-3+3)+(z.f-z.b*z.e+z.c*z.d)⟩ : Six) = z := by
      ext <;> simp [ha] <;> ring
    rw [heq,hz.1] at hlt
    omega

theorem unit_negative_diagonal_drop (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : 3 ≤ z.e) (hf : 3 ≤ z.f) :
    l1 (applyWord z [.m1,.m2]) < l1 z := by
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hbound : z.b*z.e+z.c*(-z.d)-4 ≤ z.f := by nlinarith [hk]
    have hDc : 9 ≤ (-z.d)*z.c := by
      have h1 := mul_nonneg (show 0 ≤ -z.d-3 by omega) (show 0 ≤ z.c by omega)
      nlinarith
    have hbe : 12 ≤ (z.b+1)*z.e := by
      have h1 := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ z.e by omega)
      nlinarith
    have hsum : |z.c-z.e|+|z.b*z.c-z.f| < z.e+z.f := by
      by_cases hce : z.c ≤ z.e
      · have hmul := mul_nonneg (show 0 ≤ z.b by omega) (show 0 ≤ z.e-z.c by omega)
        have hfc : z.b*z.c ≤ z.f := by nlinarith
        rw [abs_of_nonpos (by omega : z.c-z.e ≤ 0),
          abs_of_nonpos (by omega : z.b*z.c-z.f ≤ 0)]
        have hbc : 0 ≤ z.b*z.c := by positivity
        nlinarith
      · rw [abs_of_nonneg (by omega : 0 ≤ z.c-z.e)]
        by_cases hfc : z.b*z.c ≤ z.f
        · rw [abs_of_nonpos (by omega : z.b*z.c-z.f ≤ 0)]
          have hbc : z.c ≤ z.b*z.c := by
            have h1 := mul_nonneg (show 0 ≤ z.b-1 by omega) (show 0 ≤ z.c by omega)
            nlinarith
          nlinarith
        · rw [abs_of_nonneg (by omega : 0 ≤ z.b*z.c-z.f)]
          by_contra hbad
          have hB : -2*z.d ≤ z.b := by
            by_contra hB
            have h1 := mul_nonneg (show 0 ≤ -2*z.d-z.b-1 by omega)
              (show 0 ≤ z.c by omega)
            nlinarith
          have hC : 2*z.e ≤ z.c := by
            by_contra hC
            have h1 := mul_nonneg (show 0 ≤ 2*z.e-z.c-1 by omega)
              (show 0 ≤ z.b+1 by omega)
            nlinarith
          exact unit_opposed_bounds_impossible z hz ha hd he hB hC
    rw [two_forward_word_formula,l1_lt_iff]
    simp only [integerL1,ha,one_mul]
    rw [abs_of_nonneg (by omega : 0 ≤ z.e),abs_of_nonneg (by omega : 0 ≤ z.f)]
    linarith

private theorem shifted_tail_q1_lt (X Y t u k : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hk : k = 4 ∨ k = -4) :
    q1 ⟨1,X+3,Y+3,2*(X+3)+t,-(2*(Y+3)+u),
      -(X+3)*(2*(Y+3)+u)-(Y+3)*(2*(X+3)+t)+k⟩ < 8 := by
  rcases hk with rfl | rfl
  all_goals
    apply sub_pos.mp
    dsimp [q1]
    ring_nf
    positivity

theorem unit_tail_bounds_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 2*z.b ≤ z.d) (he : 2*z.c ≤ -z.e) : False := by
  have hX : 0 ≤ z.b-3 := by omega
  have hY : 0 ≤ z.c-3 := by omega
  have ht : 0 ≤ z.d-2*z.b := by omega
  have hu : 0 ≤ -z.e-2*z.c := by omega
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hlt := shifted_tail_q1_lt (z.b-3) (z.c-3) (z.d-2*z.b)
      (-z.e-2*z.c) (z.f-z.b*z.e+z.c*z.d) hX hY ht hu (by omega)
    have heq : (⟨1,z.b-3+3,z.c-3+3,2*(z.b-3+3)+(z.d-2*z.b),
        -(2*(z.c-3+3)+(-z.e-2*z.c)),
        -(z.b-3+3)*(2*(z.c-3+3)+(-z.e-2*z.c))-
        (z.c-3+3)*(2*(z.b-3+3)+(z.d-2*z.b))+(z.f-z.b*z.e+z.c*z.d)⟩ : Six) = z := by
      ext <;> simp [ha] <;> ring
    rw [heq,hz.1] at hlt
    omega

theorem unit_two_negative_middle_drop (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : z.e ≤ -3) (hf : z.f ≤ -3) :
    l1 (mu2 z) < l1 z := by
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hbound : z.b*(-z.e)+z.c*z.d-4 ≤ -z.f := by nlinarith [hk]
    have hcd : 9 ≤ z.c*z.d := by
      have h1 := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ z.d by omega)
      nlinarith
    have hbe : 12 ≤ z.b*(1-z.e) := by
      have h1 := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ 1-z.e by omega)
      nlinarith
    have hsum : |z.d-z.b|+|z.d*z.e-z.f| < z.b-z.f := by
      by_cases hfe : z.d*z.e ≤ z.f
      · rw [abs_of_nonpos (by omega : z.d*z.e-z.f ≤ 0)]
        by_cases hbd : z.d ≤ z.b
        · rw [abs_of_nonpos (by omega : z.d-z.b ≤ 0)]
          have h1 := mul_nonneg (show 0 ≤ z.b-z.d by omega) (show 0 ≤ -z.e by omega)
          nlinarith
        · rw [abs_of_nonneg (by omega : 0 ≤ z.d-z.b)]
          by_contra hbad
          have hD : 2*z.b ≤ z.d := by
            by_contra hD
            have h1 := mul_nonneg (show 0 ≤ 2*z.b-z.d-1 by omega)
              (show 0 ≤ 1-z.e by omega)
            nlinarith
          have hE : 2*z.c ≤ -z.e := by
            by_contra hE
            have h1 := mul_nonneg (show 0 ≤ 2*z.c+z.e-1 by omega)
              (show 0 ≤ z.d by omega)
            nlinarith
          exact unit_tail_bounds_impossible z hz ha hb hc hD hE
      · rw [abs_of_nonneg (by omega : 0 ≤ z.d*z.e-z.f)]
        have hde : z.d*z.e ≤ -z.d := by
          have h1 := mul_nonneg (show 0 ≤ -z.e-1 by omega) (show 0 ≤ z.d by omega)
          nlinarith
        by_cases hbd : z.d ≤ z.b
        · rw [abs_of_nonpos (by omega : z.d-z.b ≤ 0)]
          nlinarith
        · rw [abs_of_nonneg (by omega : 0 ≤ z.d-z.b)]
          nlinarith
    rw [mu2_drop_iff]
    simp only [ha,one_mul,abs_of_nonneg (by omega : 0 ≤ z.b),
      abs_of_nonpos (by omega : z.f ≤ 0)]
    omega

theorem unit_positive_drop (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : 3 ≤ z.e) (hf : 3 ≤ z.f) :
    l1 (mu1 z) < l1 z ∨ l1 (inv1 z) < l1 z ∨ l1 (mu2 z) < l1 z := by
  by_cases hm : l1 (mu1 z) < l1 z
  · exact Or.inl hm
  by_cases hi : l1 (inv1 z) < l1 z
  · exact Or.inr (Or.inl hi)
  right; right
  rw [mu1_drop_iff] at hm
  rw [inv1_drop_iff] at hi
  simp only [ha,one_mul,abs_of_nonneg (by omega : 0 ≤ z.b),
    abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonneg (by omega : 0 ≤ z.d),
    abs_of_nonneg (by omega : 0 ≤ z.e),abs_sub_comm z.d z.b,
    abs_sub_comm z.e z.c] at hm hi
  by_cases hbd : z.b ≤ z.d
  · by_cases hce : z.c ≤ z.e
    · rw [abs_of_nonpos (by omega : z.b-z.d ≤ 0),
        abs_of_nonpos (by omega : z.c-z.e ≤ 0)] at hm
      omega
    · rw [abs_of_nonpos (by omega : z.b-z.d ≤ 0),
        abs_of_nonneg (by omega : 0 ≤ z.c-z.e)] at hm hi
      have hD : 2*z.b+z.e ≤ z.d := by omega
      have hC : z.b+2*z.e ≤ z.c := by omega
      have h1 := mul_nonneg (show 0 ≤ z.d-z.e by omega) (show 0 ≤ z.c by omega)
      have h2 := mul_nonneg (show 0 ≤ z.c-z.b-z.e by omega) (show 0 ≤ z.e by omega)
      have hsq : 9 ≤ z.e^2 := by nlinarith
      obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith
  · by_cases hce : z.c ≤ z.e
    · rw [abs_of_nonneg (by omega : 0 ≤ z.b-z.d),
        abs_of_nonpos (by omega : z.c-z.e ≤ 0)] at hm hi
      have hB : 2*z.d+z.c ≤ z.b := by omega
      have hE : z.d+2*z.c ≤ z.e := by omega
      have h1 := mul_nonneg (show 0 ≤ z.b-z.d-z.c by omega) (show 0 ≤ z.e by omega)
      have h2 := mul_nonneg (show 0 ≤ z.e-z.d by omega) (show 0 ≤ z.c by omega)
      have hce : 9 ≤ z.c*z.e := by
        have hh := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ z.e by omega)
        nlinarith
      have hfe : z.d*z.e ≤ z.f := by
        obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith
      rw [mu2_drop_iff]
      simp only [ha,one_mul,abs_of_nonneg (by omega : 0 ≤ z.b),
        abs_of_nonneg (by omega : 0 ≤ z.f),
        abs_of_nonpos (by omega : z.d-z.b ≤ 0),
        abs_of_nonpos (by omega : z.d*z.e-z.f ≤ 0)]
      have hde : 0 ≤ z.d*z.e := by positivity
      omega
    · rw [abs_of_nonneg (by omega : 0 ≤ z.b-z.d),
        abs_of_nonneg (by omega : 0 ≤ z.c-z.e)] at hi
      omega

theorem unit_one_negative_tail_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : 3 ≤ z.e) (hf : z.f ≤ -3) : False := by
  have hq1 : z.f*(z.b*z.c+z.d*z.e-z.c*z.d-z.f) =
      (z.b^2-z.b*z.d+z.d^2)+(z.c^2-z.c*z.e+z.e^2)-7 := by
    have heq : (⟨1,z.b,z.c,z.d,z.e,z.f⟩ : Six) = z := by ext <;> simp [ha]
    have hh := unit_q1_identity z.b z.c z.d z.e z.f
    rw [heq,hz.1] at hh
    nlinarith [hh]
  have hP : 9 ≤ z.b^2-z.b*z.d+z.d^2 := by
    have hh := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ z.d by omega)
    nlinarith [sq_nonneg (z.b-z.d)]
  have hQ : 9 ≤ z.c^2-z.c*z.e+z.e^2 := by
    have hh := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ z.e by omega)
    nlinarith [sq_nonneg (z.c-z.e)]
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hT : 0 < z.b*z.c+z.d*z.e-z.c*z.d-z.f := by
      by_cases hce : z.e ≤ z.c
      · have h1 := mul_nonneg (show 0 ≤ z.c-z.e by omega) (show 0 ≤ z.b by omega)
        have h2 : 9 ≤ z.d*z.e := by
          have hh := mul_nonneg (show 0 ≤ z.d-3 by omega) (show 0 ≤ z.e by omega)
          nlinarith
        nlinarith
      · have hbd : z.b < z.d := by
          by_contra hbd
          have h1 := mul_nonneg (show 0 ≤ z.b-z.d by omega) (show 0 ≤ z.c by omega)
          have h2 := mul_nonneg (show 0 ≤ z.e-z.c-1 by omega) (show 0 ≤ z.b by omega)
          nlinarith
        have h1 := mul_nonneg (show 0 ≤ z.d-z.b-1 by omega) (show 0 ≤ z.e by omega)
        have h2 : 9 ≤ z.b*z.c := by
          have hh := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ z.c by omega)
          nlinarith
        nlinarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg (show z.f ≤ 0 by omega) (le_of_lt hT)
    nlinarith

private def unitCentralPolynomial (a b d e k : ℤ) : ℤ :=
  a^2-a*b*d^3+a*b*d-a*d^2*k+2*a*k+b^2*d^2+b*d*k+d^4-7*d^2+k^2+
    (-a*b*d+b^2+d^2)*e^2+
    (-a^2*d-a*b*d^2+2*a*b-a*d*k+b^2*d+2*b*k+d^3)*e

set_option maxHeartbeats 1000000 in
private theorem unitCentralPolynomial_shift_neg (B D T E k : ℤ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hk : k = 4 ∨ k = -4) :
    unitCentralPolynomial (B+3+D+T) (B+3) (B+3+D) (E+3) k < 0 ∧
    unitCentralPolynomial (B+3+D+T) (B+3+D) (B+3) (E+3) k < 0 := by
  rcases hk with rfl | rfl
  all_goals
    constructor <;> apply neg_pos.mp <;> dsimp [unitCentralPolynomial] <;>
      ring_nf <;> positivity

theorem unit_central_max_impossible (a b c d e : ℤ)
    (hb : 3 ≤ b) (hd : 3 ≤ d) (he : 3 ≤ e) (hab : b ≤ a) (had : d ≤ a)
    (hsol : isSolution ⟨a,b,c,d,e,-1⟩) : False := by
  have hk : -a-b*e+c*d = 4 ∨ -a-b*e+c*d = -4 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    norm_num
    simpa [q2] using hsol.2
  obtain hk | hk := hk
  all_goals
    have hcd : c*d = a+b*e+(-a-b*e+c*d) := by ring
    have hpoly : unitCentralPolynomial a b d e (-a-b*e+c*d) < 0 := by
      by_cases hbd : b ≤ d
      · have hh := (unitCentralPolynomial_shift_neg (b-3) (d-b) (a-d) (e-3)
          (-a-b*e+c*d) (by omega) (by omega) (by omega) (by omega) (by omega)).1
        convert hh using 1 <;> dsimp [unitCentralPolynomial] <;> ring
      · have hh := (unitCentralPolynomial_shift_neg (d-3) (b-d) (a-b) (e-3)
          (-a-b*e+c*d) (by omega) (by omega) (by omega) (by omega) (by omega)).2
        convert hh using 1 <;> dsimp [unitCentralPolynomial] <;> ring
    have hcert : d^2*(q1 ⟨a,b,c,d,e,-1⟩-8) =
        unitCentralPolynomial a b d e (-a-b*e+c*d) := by
      dsimp [unitCentralPolynomial,q1]
      ring
    rw [hsol.1] at hcert
    nlinarith

private theorem triangle_positive_drop (u v w : ℤ) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hw : 3 ≤ w) (hum : u ≤ w) (hvm : v ≤ w)
    (htri : 4 ≤ NegativeTriangles.cayleyDefect u v w) : |u*v-w| < w := by
  simpa [abs_of_nonneg (by omega : 0 ≤ u),abs_of_nonneg (by omega : 0 ≤ v),
    abs_of_nonneg (by omega : 0 ≤ w)] using
    NegativeTriangles.cayley_signed_abs_descent u v w
      (by simpa [abs_of_nonneg (by omega : 0 ≤ u)] using hu)
      (by simpa [abs_of_nonneg (by omega : 0 ≤ v)] using hv)
      (by simpa [abs_of_nonneg (by omega : 0 ≤ w)] using hw)
      (by simpa [abs_of_nonneg (by omega : 0 ≤ u),abs_of_nonneg (by omega : 0 ≤ v),
        abs_of_nonneg (by omega : 0 ≤ w)] using And.intro hum hvm)
      (by positivity) htri

set_option maxHeartbeats 1000000 in
theorem unit_tail_positive_pair_drop (a b c d e : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e)
    (hsol : isSolution ⟨a,b,c,d,e,-1⟩)
    (htri1 : 4 ≤ NegativeTriangles.cayleyDefect a b d)
    (htri2 : 4 ≤ NegativeTriangles.cayleyDefect a c e) :
    (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  have hn1 : ¬ (b ≤ a ∧ d ≤ a) := by
    rintro ⟨hba,hda⟩
    exact unit_central_max_impossible a b c d e hb hd he hba hda hsol
  have hsol2 : isSolution ⟨a,e,d,c,b,-1⟩ := by
    constructor
    · convert hsol.1 using 1 <;> dsimp [q1] <;> ring
    · convert hsol.2 using 1 <;> dsimp [q2] <;> ring
  have hn2 : ¬ (c ≤ a ∧ e ≤ a) := by
    rintro ⟨hca,hea⟩
    exact unit_central_max_impossible a e d c b he hc hb hea hca hsol2
  by_cases hbd : b ≤ d
  · have had : a ≤ d := by omega
    have hdropd := triangle_positive_drop a b d ha hb hd had hbd htri1
    by_cases hce : c ≤ e
    · have hae : a ≤ e := by omega
      exact Or.inl ⟨hdropd,triangle_positive_drop a c e ha hc he hae hce htri2⟩
    · have hac : a ≤ c := by omega
      have htri2' : 4 ≤ NegativeTriangles.cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [NegativeTriangles.cayleyDefect] <;> ring
      have hdropc := triangle_positive_drop a e c ha he hc hac (by omega) htri2'
      have hdomd : a*b ≤ 2*d := by have hh := (abs_lt.mp hdropd).2; omega
      have hdomc : a*e ≤ 2*c := by have hh := (abs_lt.mp hdropc).2; omega
      exact False.elim (opposed_dominance_impossible a b c d e (-1) ha hb he (by norm_num)
        hdomd hdomc (solution_gramDiscriminant _ hsol))
  · have hab : a ≤ b := by omega
    have htri1' : 4 ≤ NegativeTriangles.cayleyDefect a d b := by
      convert htri1 using 1 <;> dsimp [NegativeTriangles.cayleyDefect] <;> ring
    have hdropb := triangle_positive_drop a d b ha hd hb hab (by omega) htri1'
    by_cases hce : c ≤ e
    · have hae : a ≤ e := by omega
      have hdrope := triangle_positive_drop a c e ha hc he hae hce htri2
      have hdomb : a*d ≤ 2*b := by have hh := (abs_lt.mp hdropb).2; omega
      have hdome : a*c ≤ 2*e := by have hh := (abs_lt.mp hdrope).2; omega
      have hdisc3 : gramDiscriminant a d e b c (-1) = 0 := by
        convert solution_gramDiscriminant _ hsol using 1 <;>
          dsimp [gramDiscriminant,q1,q2] <;> ring
      exact False.elim (opposed_dominance_impossible a d e b c (-1) ha hd hc (by norm_num)
        hdomb hdome hdisc3)
    · have hac : a ≤ c := by omega
      have htri2' : 4 ≤ NegativeTriangles.cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [NegativeTriangles.cayleyDefect] <;> ring
      exact Or.inr ⟨hdropb,triangle_positive_drop a e c ha he hc hac (by omega) htri2'⟩

theorem unit_two_negative_right_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : z.e ≤ -3) (hf : 3 ≤ z.f) :
    l1 (mu3 z) < l1 z ∨ l1 (inv3 z) < l1 z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := NegativeTriangles.negative_triangle_inequalities z hz hneg
  have hsol : isSolution ⟨z.f,z.b,-z.d,z.c,-z.e,-1⟩ := by
    constructor
    · convert hz.1 using 1 <;> dsimp [q1] <;> rw [ha] <;> ring
    · convert hz.2 using 1 <;> dsimp [q2] <;> rw [ha] <;> ring
  have htri1' : 4 ≤ NegativeTriangles.cayleyDefect z.f z.b z.c := by
    convert htri3 using 1 <;> dsimp [NegativeTriangles.cayleyDefect] <;> ring
  have htri2' : 4 ≤ NegativeTriangles.cayleyDefect z.f (-z.d) (-z.e) := by
    convert htri4 using 1 <;> dsimp [NegativeTriangles.cayleyDefect] <;> ring
  rcases unit_tail_positive_pair_drop z.f z.b (-z.d) z.c (-z.e)
    hf hb (by omega) hc (by omega) hsol htri1' htri2' with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · left
    rw [mu3_drop_iff]
    have hh : z.f*(-z.d)-(-z.e) = -(z.f*z.d-z.e) := by ring
    rw [hh,abs_neg] at h2
    simp only [abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonpos (by omega : z.e ≤ 0)]
    linarith
  · right
    rw [inv3_drop_iff]
    have hh : z.f*(-z.e)-(-z.d) = -(z.f*z.e-z.d) := by ring
    rw [hh,abs_neg] at h2
    simp only [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.d ≤ 0)]
    linarith

private theorem unit_alternating_tail_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ z.d) (he : z.e ≤ -3) (hf : 3 ≤ z.f) : False := by
  have h1 : 9 ≤ z.b*(-z.e) := by
    have hh := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ -z.e by omega)
    nlinarith
  have h2 : 9 ≤ z.c*z.d := by
    have hh := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ z.d by omega)
    nlinarith
  obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith

private theorem unit_alternating_negative_tail_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : z.d ≤ -3) (he : 3 ≤ z.e) (hf : z.f ≤ -3) : False := by
  have h1 : 9 ≤ z.b*z.e := by
    have hh := mul_nonneg (show 0 ≤ z.b-3 by omega) (show 0 ≤ z.e by omega)
    nlinarith
  have h2 : 9 ≤ z.c*(-z.d) := by
    have hh := mul_nonneg (show 0 ≤ z.c-3 by omega) (show 0 ≤ -z.d by omega)
    nlinarith
  obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith

theorem unit_first_row_positive_word_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : z.a = 1) (hb : 3 ≤ z.b) (hc : 3 ≤ z.c)
    (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word.length ≤ 2 ∧
      (∀ g ∈ word, g ∈ braidMoves) ∧ l1 (applyWord z word) < l1 z := by
  have hd' : 3 ≤ z.d ∨ z.d ≤ -3 := by rcases le_abs.mp hd with h | h <;> omega
  have he' : 3 ≤ z.e ∨ z.e ≤ -3 := by rcases le_abs.mp he with h | h <;> omega
  have hf' : 3 ≤ z.f ∨ z.f ≤ -3 := by rcases le_abs.mp hf with h | h <;> omega
  rcases hd' with hd | hd <;> rcases he' with he | he <;> rcases hf' with hf | hf
  · rcases unit_positive_drop z hz ha hb hc hd he hf with h | h | h
    · exact ⟨[.m1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i1],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.m2],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · exact False.elim (unit_one_negative_tail_impossible z hz ha hb hc hd he hf)
  · exact False.elim (unit_alternating_tail_impossible z hz ha hb hc hd he hf)
  · exact ⟨[.m2],by decide,by simp [braidMoves],
      by simpa [applyWord,step] using unit_two_negative_middle_drop z hz ha hb hc hd he hf⟩
  · exact ⟨[.m1,.m2],by decide,by simp [braidMoves],
      unit_negative_diagonal_drop z hz ha hb hc hd he hf⟩
  · exact False.elim (unit_alternating_negative_tail_impossible z hz ha hb hc hd he hf)
  · rcases unit_two_negative_right_drop z hz hneg ha hb hc hd he hf with h | h
    · exact ⟨[.m3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
    · exact ⟨[.i3],by decide,by simp [braidMoves],by simpa [applyWord,step] using h⟩
  · have hsum := SignChambers.q1_ge_square_sum_of_negative_tail z
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hz.1] at hsum
    nlinarith [sq_nonneg (z.b-3),sq_nonneg z.a,sq_nonneg z.c,
      sq_nonneg z.d,sq_nonneg z.e,sq_nonneg z.f]

theorem unit_edge_word_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : |z.a| = 1) (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|)
    (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word.length ≤ 2 ∧
      (∀ g ∈ word, g ∈ braidMoves) ∧ l1 (applyWord z word) < l1 z := by
  obtain ⟨s,hs,ha',hb',hc',hr,hl⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  obtain ⟨habsA,habsB,habsC,habsD,habsE,habsF⟩ := SignGaugeDescent.signedSix_abs z s hs
  have hz' := reachable_preserves_solution hr hz
  have hn' : IntrinsicSigns.thirdMinorSum (PositiveNormalization.signedSix z s) < 0 := by
    change negativeMarker (PositiveNormalization.signedSix z s) < 0
    rw [SignGaugeDescent.negativeMarker_signedSix z s hs]
    exact hneg
  obtain ⟨word,hword,hbraid,hdrop⟩ := unit_first_row_positive_word_drop
    (PositiveNormalization.signedSix z s) hz' hn' (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  exact ⟨word,hword,hbraid,SignGaugeDescent.descent_transfer z s hs word hdrop⟩

end SerreMarkov.NegativeUnitEdge
