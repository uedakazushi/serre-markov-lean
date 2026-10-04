import SerreMarkov.NegativeUnitEdge
import SerreMarkov.NegativeTwoEdge
import SerreMarkov.NegativeUnitPairTwo

/-! # Unit-edge descent with other coefficients at least two

Exact integer inequalities retain the failed-descent side conditions needed
at the affine boundary. The positive-pair tail chamber is handled separately.
-/

namespace SerreMarkov.NegativeUnitTwoEdge
open NegativeDescent NegativePairDescent NegativeUnitEdge
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem shifted_opposed_q1_lt (X Y t u k : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hk : k = 4 ∨ k = -4)
    (hside : (2*(X+2)+t)*(Y+2)+(2*(Y+2)+u)*(X+2)+k < (2*(X+2)+t)*(2*(Y+2)+u)) :
    q1 ⟨1,2*(X+2)+t,2*(Y+2)+u,-(X+2),Y+2,
      (2*(X+2)+t)*(Y+2)+(2*(Y+2)+u)*(X+2)+k⟩ < 8 := by
  rcases hk with hk | hk
  ·
    have hp : 1≤Y ∨ 1≤u ∨ 2≤t := by
      by_contra h
      have hY0 : Y=0 := by omega
      have hu0 : u=0 := by omega
      have ht1 : t≤1 := by omega
      simp only [hY0,hu0] at hside
      nlinarith
    rcases hp with hp | hp | hp
    · let Y0 : ℤ := Y-1
      have hY0 : 0≤Y0 := by dsimp [Y0]; omega
      have hlt : q1 ⟨1,2*(X+2)+t,2*((Y0+1)+2)+u,-(X+2),(Y0+1)+2,
        (2*(X+2)+t)*((Y0+1)+2)+(2*((Y0+1)+2)+u)*(X+2)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,Y0] <;> ring
    · let u0 : ℤ := u-1
      have hu0 : 0≤u0 := by dsimp [u0]; omega
      have hlt : q1 ⟨1,2*(X+2)+t,2*(Y+2)+(u0+1),-(X+2),Y+2,
        (2*(X+2)+t)*(Y+2)+(2*(Y+2)+(u0+1))*(X+2)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,u0] <;> ring
    · let t0 : ℤ := t-2
      have ht0 : 0≤t0 := by dsimp [t0]; omega
      have hlt : q1 ⟨1,2*(X+2)+(t0+2),2*(Y+2)+u,-(X+2),Y+2,
        (2*(X+2)+(t0+2))*(Y+2)+(2*(Y+2)+u)*(X+2)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,t0] <;> ring
  · apply sub_pos.mp
    simp only [hk]
    dsimp [q1]
    ring_nf
    positivity

theorem unit_opposed_bounds_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hd : z.d ≤ -2) (he : 2 ≤ z.e)
    (hb : -2*z.d ≤ z.b) (hc : 2*z.e ≤ z.c) (hbc : z.f<z.b*z.c) : False := by
  have hX : 0 ≤ -z.d-2 := by omega
  have hY : 0 ≤ z.e-2 := by omega
  have ht : 0 ≤ z.b+2*z.d := by omega
  have hu : 0 ≤ z.c-2*z.e := by omega
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hlt := shifted_opposed_q1_lt (-z.d-2) (z.e-2) (z.b+2*z.d)
      (z.c-2*z.e) (z.f-z.b*z.e+z.c*z.d) hX hY ht hu (by omega) (by convert hbc using 1 <;> ring)
    have heq : (⟨1,2*(-z.d-2+2)+(z.b+2*z.d),2*(z.e-2+2)+(z.c-2*z.e),
        -(-z.d-2+2),z.e-2+2,
        (2*(-z.d-2+2)+(z.b+2*z.d))*(z.e-2+2)+
        (2*(z.e-2+2)+(z.c-2*z.e))*(-z.d-2+2)+(z.f-z.b*z.e+z.c*z.d)⟩ : Six) = z := by
      ext <;> simp [ha] <;> ring
    rw [heq,hz.1] at hlt
    omega

theorem unit_negative_diagonal_drop (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : 2 ≤ z.e) (hf : 2 ≤ z.f) :
    l1 (applyWord z [.m1,.m2]) < l1 z := by
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hbound : z.b*z.e+z.c*(-z.d)-4 ≤ z.f := by nlinarith [hk]
    have hDc : 4 ≤ (-z.d)*z.c := by
      have h1 := mul_nonneg (show 0 ≤ -z.d-2 by omega) (show 0 ≤ z.c by omega)
      nlinarith
    have hbe : 6 ≤ (z.b+1)*z.e := by
      have h1 := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ z.e by omega)
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
          exact unit_opposed_bounds_impossible z hz ha hd he hB hC (by omega)
    rw [two_forward_word_formula,l1_lt_iff]
    simp only [integerL1,ha,one_mul]
    rw [abs_of_nonneg (by omega : 0 ≤ z.e),abs_of_nonneg (by omega : 0 ≤ z.f)]
    linarith

private theorem shifted_tail_q1_lt (X Y t u k : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hk : k = 4 ∨ k = -4)
    (hside : (2*(X+2)+t)*(-(2*(Y+2)+u)) ≤ -(X+2)*(2*(Y+2)+u)-(Y+2)*(2*(X+2)+t)+k) :
    q1 ⟨1,X+2,Y+2,2*(X+2)+t,-(2*(Y+2)+u),
      -(X+2)*(2*(Y+2)+u)-(Y+2)*(2*(X+2)+t)+k⟩ < 8 := by
  rcases hk with hk | hk
  · apply sub_pos.mp
    simp only [hk]
    dsimp [q1]
    ring_nf
    positivity
  ·
    have hp : 1≤X ∨ 2≤Y ∨ 1≤t ∨ 2≤u := by
      by_contra h
      have hX0 : X=0 := by omega
      have ht0 : t=0 := by omega
      have hY1 : Y≤1 := by omega
      have hu1 : u=0 ∨ u=1 := by omega
      rcases hu1 with hu0 | hu0 <;> simp only [hX0,ht0,hu0] at hside <;> nlinarith
    rcases hp with hp | hp | hp | hp
    · let X0 : ℤ := X-1
      have hX0 : 0≤X0 := by dsimp [X0]; omega
      have hlt : q1 ⟨1,(X0+1)+2,Y+2,2*((X0+1)+2)+t,-(2*(Y+2)+u),
        -((X0+1)+2)*(2*(Y+2)+u)-(Y+2)*(2*((X0+1)+2)+t)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,X0] <;> ring
    · let Y0 : ℤ := Y-2
      have hY0 : 0≤Y0 := by dsimp [Y0]; omega
      have hlt : q1 ⟨1,X+2,(Y0+2)+2,2*(X+2)+t,-(2*((Y0+2)+2)+u),
        -(X+2)*(2*((Y0+2)+2)+u)-((Y0+2)+2)*(2*(X+2)+t)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,Y0] <;> ring
    · let t0 : ℤ := t-1
      have ht0 : 0≤t0 := by dsimp [t0]; omega
      have hlt : q1 ⟨1,X+2,Y+2,2*(X+2)+(t0+1),-(2*(Y+2)+u),
        -(X+2)*(2*(Y+2)+u)-(Y+2)*(2*(X+2)+(t0+1))+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,t0] <;> ring
    · let u0 : ℤ := u-2
      have hu0 : 0≤u0 := by dsimp [u0]; omega
      have hlt : q1 ⟨1,X+2,Y+2,2*(X+2)+t,-(2*(Y+2)+(u0+2)),
        -(X+2)*(2*(Y+2)+(u0+2))-(Y+2)*(2*(X+2)+t)+k⟩ < 8 := by
        apply sub_pos.mp
        simp only [hk]
        dsimp [q1]
        ring_nf
        positivity
      convert hlt using 1 <;> dsimp [q1,u0] <;> ring

theorem unit_tail_bounds_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2*z.b ≤ z.d) (he : 2*z.c ≤ -z.e) (hde : z.d*z.e≤z.f) : False := by
  have hX : 0 ≤ z.b-2 := by omega
  have hY : 0 ≤ z.c-2 := by omega
  have ht : 0 ≤ z.d-2*z.b := by omega
  have hu : 0 ≤ -z.e-2*z.c := by omega
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hlt := shifted_tail_q1_lt (z.b-2) (z.c-2) (z.d-2*z.b)
      (-z.e-2*z.c) (z.f-z.b*z.e+z.c*z.d) hX hY ht hu (by omega) (by convert hde using 1 <;> ring)
    have heq : (⟨1,z.b-2+2,z.c-2+2,2*(z.b-2+2)+(z.d-2*z.b),
        -(2*(z.c-2+2)+(-z.e-2*z.c)),
        -(z.b-2+2)*(2*(z.c-2+2)+(-z.e-2*z.c))-
        (z.c-2+2)*(2*(z.b-2+2)+(z.d-2*z.b))+(z.f-z.b*z.e+z.c*z.d)⟩ : Six) = z := by
      ext <;> simp [ha] <;> ring
    rw [heq,hz.1] at hlt
    omega

theorem unit_two_negative_middle_drop (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ z.d) (he : z.e ≤ -2) (hf : z.f ≤ -2) :
    l1 (mu2 z) < l1 z := by
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hbound : z.b*(-z.e)+z.c*z.d-4 ≤ -z.f := by nlinarith [hk]
    have hcd : 4 ≤ z.c*z.d := by
      have h1 := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ z.d by omega)
      nlinarith
    have hbe : 6 ≤ z.b*(1-z.e) := by
      have h1 := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ 1-z.e by omega)
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
          exact unit_tail_bounds_impossible z hz ha hb hc hD hE hfe
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
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ z.d) (he : 2 ≤ z.e) (hf : 2 ≤ z.f) :
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
      have hsq : 4 ≤ z.e^2 := by nlinarith
      obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith
  · by_cases hce : z.c ≤ z.e
    · rw [abs_of_nonneg (by omega : 0 ≤ z.b-z.d),
        abs_of_nonpos (by omega : z.c-z.e ≤ 0)] at hm hi
      have hB : 2*z.d+z.c ≤ z.b := by omega
      have hE : z.d+2*z.c ≤ z.e := by omega
      have h1 := mul_nonneg (show 0 ≤ z.b-z.d-z.c by omega) (show 0 ≤ z.e by omega)
      have h2 := mul_nonneg (show 0 ≤ z.e-z.d by omega) (show 0 ≤ z.c by omega)
      have hce : 4 ≤ z.c*z.e := by
        have hh := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ z.e by omega)
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
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ z.d) (he : 2 ≤ z.e) (hf : z.f ≤ -2) : False := by
  have hq1 : z.f*(z.b*z.c+z.d*z.e-z.c*z.d-z.f) =
      (z.b^2-z.b*z.d+z.d^2)+(z.c^2-z.c*z.e+z.e^2)-7 := by
    have heq : (⟨1,z.b,z.c,z.d,z.e,z.f⟩ : Six) = z := by ext <;> simp [ha]
    have hh := unit_q1_identity z.b z.c z.d z.e z.f
    rw [heq,hz.1] at hh
    nlinarith [hh]
  have hP : 4 ≤ z.b^2-z.b*z.d+z.d^2 := by
    have hh := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ z.d by omega)
    nlinarith [sq_nonneg (z.b-z.d)]
  have hQ : 4 ≤ z.c^2-z.c*z.e+z.e^2 := by
    have hh := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ z.e by omega)
    nlinarith [sq_nonneg (z.c-z.e)]
  obtain hk | hk := unit_q2_sign z hz ha
  all_goals
    have hT : 0 ≤ z.b*z.c+z.d*z.e-z.c*z.d-z.f := by
      by_cases hce : z.e ≤ z.c
      · have h1 := mul_nonneg (show 0 ≤ z.c-z.e by omega) (show 0 ≤ z.b by omega)
        have h2 : 4 ≤ z.d*z.e := by
          have hh := mul_nonneg (show 0 ≤ z.d-2 by omega) (show 0 ≤ z.e by omega)
          nlinarith
        nlinarith
      · have h1 := mul_nonneg (show 0 ≤ z.e-z.c by omega) (show 0 ≤ z.d by omega)
        have h2 := mul_nonneg (show 0 ≤ z.b by omega) (show 0 ≤ z.c by omega)
        nlinarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg (show z.f ≤ 0 by omega) hT
    nlinarith


private theorem unit_alternating_tail_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : 2 ≤ z.d) (he : z.e ≤ -2) (hf : 2 ≤ z.f) : False := by
  have h1 : 4 ≤ z.b*(-z.e) := by
    have hh := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ -z.e by omega)
    nlinarith
  have h2 : 4 ≤ z.c*z.d := by
    have hh := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ z.d by omega)
    nlinarith
  obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith

private theorem unit_alternating_negative_tail_impossible (z : Six) (hz : isSolution z)
    (ha : z.a = 1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : 2 ≤ z.e) (hf : z.f ≤ -2) : False := by
  have h1 : 4 ≤ z.b*z.e := by
    have hh := mul_nonneg (show 0 ≤ z.b-2 by omega) (show 0 ≤ z.e by omega)
    nlinarith
  have h2 : 4 ≤ z.c*(-z.d) := by
    have hh := mul_nonneg (show 0 ≤ z.c-2 by omega) (show 0 ≤ -z.d by omega)
    nlinarith
  obtain hk | hk := unit_q2_sign z hz ha <;> nlinarith


/-- The unit first edge is now treated with all remaining absolute values at
least two, including the affine equality cases. -/
theorem unit_first_row_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : z.a=1) (hb : 2≤z.b) (hc : 2≤z.c)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) :
    NegativeTwoEdge.FamilyOrDrop z := by
  have hd' : 2≤z.d ∨ z.d≤-2 := by rcases le_abs.mp hd with h | h <;> omega
  have he' : 2≤z.e ∨ z.e≤-2 := by rcases le_abs.mp he with h | h <;> omega
  have hf' : 2≤z.f ∨ z.f≤-2 := by rcases le_abs.mp hf with h | h <;> omega
  rcases hd' with hd | hd <;> rcases he' with he | he <;> rcases hf' with hf | hf
  · right
    rcases unit_positive_drop z hz ha hb hc hd he hf with h | h | h
    · exact ⟨[.m1],h⟩
    · exact ⟨[.i1],h⟩
    · exact ⟨[.m2],h⟩
  · exact False.elim (unit_one_negative_tail_impossible z hz ha hb hc hd he hf)
  · exact False.elim (unit_alternating_tail_impossible z hz ha hb hc hd he hf)
  · exact Or.inr ⟨[.m2],unit_two_negative_middle_drop z hz ha hb hc hd he hf⟩
  · exact Or.inr ⟨[.m1,.m2],unit_negative_diagonal_drop z hz ha hb hc hd he hf⟩
  · exact False.elim (unit_alternating_negative_tail_impossible z hz ha hb hc hd he hf)
  · exact NegativeUnitPairTwo.unit_two_negative_right_reduction z hz hneg ha hb hc hd he hf
  · have hsum := SignChambers.q1_ge_square_sum_of_negative_tail z
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [hz.1] at hsum
    nlinarith [sq_nonneg (z.b-2),sq_nonneg (z.c-2),sq_nonneg (z.d+2),
      sq_nonneg (z.e+2),sq_nonneg (z.f+2),sq_nonneg z.a]

/-- Height-preserving sign normalization removes all sign restrictions. -/
theorem unit_first_edge_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : |z.a|=1) (hb : 2≤|z.b|) (hc : 2≤|z.c|)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) :
    NegativeTwoEdge.FamilyOrDrop z := by
  obtain ⟨s,hs,ha',hb',hc',hr,_⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  obtain ⟨habsA,habsB,habsC,habsD,habsE,habsF⟩ := SignGaugeDescent.signedSix_abs z s hs
  have hw := reachable_preserves_solution hr hz
  have hwn : IntrinsicSigns.thirdMinorSum (PositiveNormalization.signedSix z s)<0 := by
    change negativeMarker (PositiveNormalization.signedSix z s)<0
    rw [SignGaugeDescent.negativeMarker_signedSix z s hs]
    exact hneg
  apply NegativeTwoEdge.familyOrDrop_of_gauge z s hs
  exact unit_first_row_two_reduction _ hw hwn (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

end SerreMarkov.NegativeUnitTwoEdge
