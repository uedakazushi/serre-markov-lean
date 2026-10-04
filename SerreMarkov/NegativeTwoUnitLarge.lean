import SerreMarkov.NegativeUnitEdge
import SerreMarkov.NegativeTwoEdge

/-! # Descent at two unit edges and a large third edge -/

namespace SerreMarkov.NegativeTwoUnitLarge

open NegativeDescent NegativeTwoEdge

private theorem outside_positive_q1_gt (D E T k : ℤ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hT : 0 ≤ T) (hk : k=4 ∨ k=-4) :
    8 < q1 ⟨1,1,2*(E+1)+1+T,D+3,E+1,
      E+1-(2*(E+1)+1+T)*(D+3)+k⟩ := by
  rcases hk with rfl | rfl
  all_goals
    apply sub_pos.mp
    dsimp [q1]
    ring_nf
    positivity

private def unitCertificate (C d L k : ℤ) : ℤ :=
  -(d-2)*(2*C^2*d^3+C^2*d^2-3*C^2*d+2*C^2+C*L*d^2+3*C*L*d-2*C*L-
    C*d^3+3*C*d^2*k-C*d^2+3*C*d*k+8*C*d-2*C*k-4*C+L^2+L*d*k-
    2*L*d+2*L*k+4*L-d^3-d^2*k+4*d^2+d*k^2+2*k^2+4*k-8)

private theorem unitCertificate_positive_sign (X D L : ℤ)
    (hX : 0 ≤ X) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    unitCertificate (X+1) (D+3) L 4 < 0 := by
  apply neg_pos.mp
  dsimp [unitCertificate]
  ring_nf
  positivity

private theorem unitCertificate_negative_sign (X D L : ℤ)
    (hX : 0 ≤ X) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    unitCertificate (X+2) (D+3) L (-4) < 0 := by
  apply neg_pos.mp
  dsimp [unitCertificate]
  ring_nf
  positivity

theorem two_unit_forward_drop (c d e f : ℤ) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hce : c ≤ 2*e) :
    l1 (mu1 ⟨1,1,c,d,e,f⟩) < l1 ⟨1,1,c,d,e,f⟩ := by
  rw [mu1_drop_iff]
  simp only [one_mul,abs_of_nonpos (by omega : 1-d ≤ 0),
    abs_of_nonneg (by omega : 0 ≤ d)]
  have he : 0 ≤ e := by omega
  rw [abs_of_nonneg he]
  have h := abs_le.mpr (show -e ≤ c-e ∧ c-e ≤ e by omega)
  omega

theorem two_unit_opposed_drop (C d e f k : ℤ)
    (hz : isSolution ⟨1,1,-C,d,e,f⟩) (hC : 1 ≤ C) (hd : 3 ≤ d) (he : 1 ≤ e)
    (hf : f=e+C*d+k) (hk : k=4 ∨ k=-4)
    (hspecial : k=-4 → C=1 → False) :
    l1 (mu2 ⟨1,1,-C,d,e,f⟩) < l1 ⟨1,1,-C,d,e,f⟩ := by
  have hCd : 3 ≤ C*d := by
    nlinarith [mul_nonneg (by omega : 0 ≤ C-1) (by omega : 0 ≤ d)]
  have hf0 : 0 ≤ f := by rcases hk with hk | hk <;> omega
  rw [mu2_drop_iff]
  simp only [one_mul,abs_of_nonneg (by omega : 0 ≤ d-1),abs_one,abs_of_nonneg hf0]
  by_cases hde : d*e ≤ f
  · rw [abs_of_nonpos (by omega : d*e-f ≤ 0)]
    have h1 := mul_nonneg (show 0 ≤ e-1 by omega) (show 0 ≤ d by omega)
    nlinarith
  · rw [abs_of_nonneg (by omega : 0 ≤ d*e-f)]
    by_contra hbad
    let L := (d-2)*(e+1)-2*d*C-2*k
    have hL : 0 ≤ L := by dsimp [L]; nlinarith
    have hpoly : unitCertificate C d L k < 0 := by
      rcases hk with rfl | rfl
      · have h := unitCertificate_positive_sign (C-1) (d-3) L (by omega) (by omega) hL
        convert h using 1 <;> dsimp [unitCertificate] <;> ring
      · have hC2 : 2 ≤ C := by by_contra h; exact hspecial rfl (by omega)
        have h := unitCertificate_negative_sign (C-2) (d-3) L (by omega) (by omega) hL
        convert h using 1 <;> dsimp [unitCertificate] <;> ring
    have hcert : (d-2)^2*(q1 ⟨1,1,-C,d,e,f⟩-8)=unitCertificate C d L k := by
      dsimp [q1,unitCertificate,L]
      rw [hf]
      ring
    rw [hz.1] at hcert
    nlinarith

theorem positive_unit_exception (d e f : ℤ)
    (hz : isSolution ⟨1,1,-1,d,e,f⟩) (hd : 3 ≤ d) (he : 1 ≤ e)
    (hf : f=e+d-4) : d=3 ∧ e=2 ∧ f=1 := by
  have hcert : q1 ⟨1,1,-1,d,e,f⟩-8 =
      3-(e-1)*((d-3)^2+(d-3)*(e-1)+3*(d-3)+(e-1)+2) := by
    dsimp [q1]; rw [hf]; ring
  rw [hz.1] at hcert
  by_cases he2 : e ≤ 2
  · have heq : e=1 ∨ e=2 := by omega
    rcases heq with rfl | rfl
    · norm_num at hcert
    · have hd3 : d=3 := by nlinarith [sq_nonneg (d-3)]
      exact ⟨hd3,rfl,by omega⟩
  · have hD : 0 ≤ d-3 := by omega
    have hE : 0 ≤ e-1 := by omega
    have h1 : 0 ≤ (e-1)*(d-3)^2 := by positivity
    have h2 : 0 ≤ (e-1)*(d-3)*(e-1) := by positivity
    have h3 : 0 ≤ 3*(e-1)*(d-3) := by positivity
    nlinarith

theorem positive_two_unit_nonnegative_outside_descent (c d e f : ℤ)
    (hz : isSolution ⟨1,1,c,d,e,f⟩) (hd : 3 ≤ d) (he : 0 ≤ e) :
    ∃ word : List Generator, l1 (applyWord ⟨1,1,c,d,e,f⟩ word)<l1 ⟨1,1,c,d,e,f⟩ := by
  obtain hk | hk := NegativeUnitEdge.unit_q2_sign ⟨1,1,c,d,e,f⟩ hz rfl
  all_goals
    simp only [Six.a,Six.b,Six.c,Six.d,Six.e,Six.f,one_mul] at hk
    by_cases he0 : e=0
    · subst e
      have hcert : q1 ⟨1,1,c,d,0,f⟩-8 =
          (d+1)*(c-(f+c*d)/2)^2+(d-2)*(d-3) := by
        rcases (show f+c*d=4 ∨ f+c*d=-4 by omega) with h | h
        · have hf : f=4-c*d := by omega
          rw [hf]
          norm_num
          dsimp [q1]; ring
        · have hf : f=-4-c*d := by omega
          rw [hf]
          norm_num
          dsimp [q1]; ring
      have h1 : 0 ≤ (d+1)*(c-(f+c*d)/2)^2 := by positivity
      have hd3 : d=3 := by rw [hz.1] at hcert; nlinarith
      subst d
      have hcases : (c=2 ∧ f=-2) ∨ (c=-2 ∧ f=2) := by
        have hq := hz.1
        rcases (show f+3*c=4 ∨ f+3*c=-4 by omega) with h | h
        · have hf : f=4-3*c := by omega
          simp only [q1,hf] at hq
          left; constructor <;> nlinarith [sq_nonneg (c-2)]
        · have hf : f=-4-3*c := by omega
          simp only [q1,hf] at hq
          right; constructor <;> nlinarith [sq_nonneg (c+2)]
      rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals exact ⟨[.i1,.m2],by decide⟩
    · have he1 : 1 ≤ e := by omega
      by_cases hc : 0 ≤ c
      · by_cases hce : c ≤ 2*e
        · exact ⟨[.m1],two_unit_forward_drop c d e f hd hc hce⟩
        · have hlt := outside_positive_q1_gt (d-3) (e-1) (c-2*e-1)
            (f-e+c*d) (by omega) (by omega) (by omega) (by omega)
          have heq : (⟨1,1,2*(e-1+1)+1+(c-2*e-1),d-3+3,e-1+1,
              e-1+1-(2*(e-1+1)+1+(c-2*e-1))*(d-3+3)+(f-e+c*d)⟩ : Six) =
              ⟨1,1,c,d,e,f⟩ := by ext <;> dsimp <;> ring
          rw [heq,hz.1] at hlt
          omega
      · let C := -c
        have hC : 1 ≤ C := by dsimp [C]; omega
        have hz' : isSolution ⟨1,1,-C,d,e,f⟩ := by simpa [C] using hz
        have hf' : f=e+C*d+(f-e+c*d) := by dsimp [C]; ring
        by_cases hspecial : f-e+c*d=-4 ∧ C=1
        · have hc1 : c=-1 := by dsimp [C] at hspecial; omega
          subst c
          obtain ⟨hd3,he2,hf1⟩ := positive_unit_exception d e f hz hd he1 (by omega)
          subst d; subst e; subst f
          exact ⟨[.i3],by decide⟩
        · have hdrop := two_unit_opposed_drop C d e f (f-e+c*d)
            hz' hC hd he1 hf' (by omega) (by intro h1 h2; exact hspecial ⟨h1,h2⟩)
          exact ⟨[.m2],by simpa [C,applyWord,step] using hdrop⟩

theorem eps4_word_descent_transfer (z : Six) (word : List Generator)
    (h : l1 (applyWord (eps4 z) word)<l1 (eps4 z)) : l1 (applyWord z word)<l1 z := by
  let s : Fin 4 → ℤ := ![1,1,1,-1]
  have hs : ∀ i,(s i)^2=1 := by intro i; fin_cases i <;> norm_num [s]
  have heq : PositiveNormalization.signedSix z s=eps4 z := by
    ext <;> simp [PositiveNormalization.signedSix,eps4,s]
  exact SignGaugeDescent.descent_transfer z s hs word (by simpa only [heq] using h)

theorem positive_two_unit_descent (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : 3 ≤ z.d) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  have heq : (⟨1,1,z.c,z.d,z.e,z.f⟩ : Six)=z := by ext <;> simp [ha,hb]
  by_cases he : 0 ≤ z.e
  · rw [← heq] at hz ⊢
    exact positive_two_unit_nonnegative_outside_descent z.c z.d z.e z.f hz hd he
  · have hw : isSolution ⟨1,1,-z.c,z.d,-z.e,-z.f⟩ := by
      have h := step_preserves_solution .s4 z hz
      simpa [step,eps4,ha,hb] using h
    obtain ⟨word,hword⟩ := positive_two_unit_nonnegative_outside_descent
      (-z.c) z.d (-z.e) (-z.f) hw hd (by omega)
    refine ⟨word,eps4_word_descent_transfer z word ?_⟩
    simpa [eps4,ha,hb] using hword

theorem negative_third_three_word (c D e f k : ℤ) (hf : f=e+D*c+k) :
    applyWord ⟨1,1,c,-D,e,f⟩ [.m1,.m1,.m2] =
      ⟨1,1,-e,D+1,c-(D+2)*e-k,c-e⟩ := by
  ext <;> simp [applyWord,step,mu1,mu2,hf] <;> ring

private theorem negative_third_zero_c_impossible (D e f k : ℤ)
    (hz : isSolution ⟨1,1,0,-D,e,f⟩) (hD : 3 ≤ D)
    (hf : f=e+k) (hk : k=4 ∨ k=-4) : False := by
  rcases hk with rfl | rfl
  all_goals
    have h1 : 0 < (D-1)*(D-2) := by
      exact mul_pos (by omega) (by omega)
    have hcert := hz.1
    dsimp [q1] at hcert
    rw [hf] at hcert
    nlinarith [sq_nonneg (e+2),sq_nonneg (e-2),
      mul_nonneg (show 0 ≤ D+2 by omega) (sq_nonneg (e+2)),
      mul_nonneg (show 0 ≤ D+2 by omega) (sq_nonneg (e-2))]

private theorem negative_third_one_c_nonnegative_impossible (D e f k : ℤ)
    (hz : isSolution ⟨1,1,1,-D,e,f⟩) (hD : 3 ≤ D) (he : 0 ≤ e)
    (hf : f=e+D+k) (hk : k=4 ∨ k=-4) : False := by
  let X := D-3
  have hX : 0 ≤ X := by dsimp [X]; omega
  rcases hk with rfl | rfl
  · have hp : 0 < q1 ⟨1,1,1,-D,e,f⟩-8 := by
      rw [hf]
      have heq : D=X+3 := by dsimp [X]; ring
      rw [heq]
      dsimp [q1]
      ring_nf
      positivity
    rw [hz.1] at hp
    omega
  · have hcert : q1 ⟨1,1,1,-D,e,f⟩-8 =
        X^2*e+X^2+X*e^2+3*X*e+2*X+5*(e-1)^2+7 := by
      dsimp [q1,X]; rw [hf]; ring
    have hp : 0 < X^2*e+X^2+X*e^2+3*X*e+2*X+5*(e-1)^2+7 := by positivity
    rw [hz.1] at hcert
    omega

theorem negative_third_nonnegative_outside_descent (c D e f k : ℤ)
    (hz : isSolution ⟨1,1,c,-D,e,f⟩) (hD : 3 ≤ D) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hf : f=e+D*c+k) (hk : k=4 ∨ k=-4) :
    ∃ word : List Generator, l1 (applyWord ⟨1,1,c,-D,e,f⟩ word)<l1 ⟨1,1,c,-D,e,f⟩ := by
  by_cases hc0 : c=0
  · subst c
    exact False.elim (negative_third_zero_c_impossible D e f k hz hD (by simpa using hf) hk)
  by_cases hc1 : c=1
  · subst c
    exact False.elim (negative_third_one_c_nonnegative_impossible D e f k hz hD he (by simpa using hf) hk)
  have hc2 : 2 ≤ c := by omega
  by_cases hce : c≤e
  · refine ⟨[.m1],?_⟩
    rw [show applyWord ⟨1,1,c,-D,e,f⟩ [.m1]=mu1 ⟨1,1,c,-D,e,f⟩ from rfl,mu1_drop_iff]
    simp only [one_mul,abs_of_nonneg (by omega : 0 ≤ 1-(-D)),
      abs_of_nonpos (by omega : c-e ≤ 0),abs_neg,
      abs_of_nonneg (by omega : 0 ≤ D),abs_of_nonneg he]
    omega
  have hdc : 6 ≤ D*c := by
    nlinarith [mul_nonneg (by omega : 0 ≤ D-3) (by omega : 0 ≤ c-2)]
  have hf0 : 0 ≤ f := by rcases hk with hk | hk <;> omega
  have hupper : 1 < (D-1)*c+(D+4)*e+2*k := by
    rcases hk with rfl | rfl
    · have hDm : 0 ≤ D-1 := by omega
      have hDp : 0 ≤ D+4 := by omega
      have h1 : 0 ≤ (D-1)*c := by positivity
      have h2 : 0 ≤ (D+4)*e := by positivity
      linarith
    · by_cases he0 : e=0
      · subst e
        by_contra hn
        have hbound : (D-1)*c≤9 := by omega
        have h1 := mul_nonneg (show 0 ≤ D-1 by omega) (show 0 ≤ c-2 by omega)
        have hD5 : D≤5 := by nlinarith
        have h2 := mul_nonneg (show 0 ≤ D-1 by omega) (show 0 ≤ c^2-4 by nlinarith)
        have h3 := mul_nonneg (show 0 ≤ D-3 by omega) (show 0 ≤ 5-D by omega)
        have hq := hz.1
        simp only [q1] at hq
        rw [hf] at hq
        nlinarith
      · have h1 : 4 ≤ (D-1)*c := by
          nlinarith [mul_nonneg (by omega : 0 ≤ D-3) (by omega : 0 ≤ c-2)]
        have he1 : 1 ≤ e := by omega
        have h2 : 7 ≤ (D+4)*e := by
          nlinarith [mul_nonneg (by omega : 0 ≤ D-3) (by omega : 0 ≤ e-1)]
        linarith
  have hlower : 1 < (D+1)*c-D*e := by
    have h1 := mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ c-e-1 by omega)
    nlinarith
  have habs : |c-(D+2)*e-k| < D*c+2*e+k-1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  refine ⟨[.m1,.m1,.m2],?_⟩
  rw [negative_third_three_word c D e f k hf,l1_lt_iff]
  simp only [integerL1,abs_one,abs_neg,abs_of_nonneg hc,abs_of_nonneg he,
    abs_of_nonneg (by omega : 0 ≤ D),abs_of_nonneg (by omega : 0 ≤ D+1),
    abs_of_nonneg (by omega : 0 ≤ c-e),abs_of_nonneg hf0]
  nlinarith

private def convexUnitBound (C D U k : ℤ) : ℤ :=
  q1 ⟨1,1,C,-D,-(D*C-(C+1+U)+k),C+1+U⟩-8+
    (D+2)*U*(D*C-(C+1+U)+k-1)

private theorem convexUnitBound_pos_sign (X Y U : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hU : 0 ≤ U) :
    convexUnitBound (X+2) (Y+3) U 4 < 0 := by
  apply neg_pos.mp
  dsimp [convexUnitBound,q1]
  ring_nf
  positivity

private theorem convexUnitBound_neg_sign_large_d (X Y U : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hU : 0 ≤ U) :
    convexUnitBound (X+2) (Y+4) U (-4) < 0 := by
  apply neg_pos.mp
  dsimp [convexUnitBound,q1]
  ring_nf
  positivity

private theorem convexUnitBound_neg_sign_large_c (X Y U : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hU : 0 ≤ U) :
    convexUnitBound (X+3) (Y+3) U (-4) < 0 := by
  apply neg_pos.mp
  dsimp [convexUnitBound,q1]
  ring_nf
  positivity

private theorem nonpositive_f_q1_gt (X Y F k : ℤ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hF : 0 ≤ F) (hk : k=4 ∨ k=-4) :
    8 < q1 ⟨1,1,Y+2,-(X+3),-((X+3)*(Y+2)+k+F),-F⟩ := by
  rcases hk with rfl | rfl
  all_goals
    apply sub_pos.mp
    dsimp [q1]
    ring_nf
    positivity

theorem negative_third_opposed_one_impossible (D E f k : ℤ)
    (hz : isSolution ⟨1,1,1,-D,-E,f⟩) (hD : 3 ≤ D) (hE : 1 ≤ E)
    (hf : f=D-E+k) (hk : k=4 ∨ k=-4) : False := by
  have hcert : q1 ⟨1,1,1,-D,-E,f⟩-8 =
      k^2-3*k-1-(D+2)*(f-2)*(E-1) := by dsimp [q1]; rw [hf]; ring
  rw [hz.1] at hcert
  by_cases hf2 : f≤2
  · have hp := mul_nonpos_of_nonpos_of_nonneg (show f-2 ≤ 0 by omega) (show 0 ≤ E-1 by omega)
    have hp' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ D+2 by omega) hp
    rcases hk with rfl | rfl <;> nlinarith
  have hf3 : 3 ≤ f := by omega
  by_cases hE1 : E=1
  · subst E
    rcases hk with rfl | rfl <;> norm_num at hcert
  have hE2 : 2 ≤ E := by omega
  have hprod : 1 ≤ (f-2)*(E-1) := by
    nlinarith [mul_nonneg (by omega : 0 ≤ f-3) (by omega : 0 ≤ E-2)]
  rcases hk with rfl | rfl
  · have hp := mul_nonneg (show 0 ≤ D+2 by omega) (show 0 ≤ (f-2)*(E-1)-1 by omega)
    nlinarith
  · have hD9 : 9 ≤ D := by omega
    have hp : (D+2)*((f-2)*(E-1))=27 := by nlinarith
    have huv : D-8 ≤ (f-2)*(E-1) := by
      nlinarith [mul_nonneg (by omega : 0 ≤ f-3) (by omega : 0 ≤ E-2)]
    have hp' := mul_nonneg (show 0 ≤ D+2 by omega) (show 0 ≤ (f-2)*(E-1)-(D-8) by omega)
    have hD10 : D≤10 := by
      by_contra hn
      have hh := mul_nonneg (show 0 ≤ D-11 by omega) (show 0 ≤ D+5 by omega)
      nlinarith
    interval_cases D <;> norm_num at hp <;> omega

theorem negative_third_opposed_f_bounds (C D E f k : ℤ)
    (hz : isSolution ⟨1,1,C,-D,-E,f⟩) (hC : 2 ≤ C) (hD : 3 ≤ D) (hE : 1 ≤ E)
    (hf : f=D*C-E+k) (hk : k=4 ∨ k=-4) : 1 ≤ f ∧ f≤C := by
  have hfpos : 1 ≤ f := by
    by_contra hn
    have hh := nonpositive_f_q1_gt (D-3) (C-2) (-f) k (by omega) (by omega) (by omega) hk
    have heq : (⟨1,1,C-2+2,-(D-3+3),-((D-3+3)*(C-2+2)+k+(-f)),-(-f)⟩ : Six)=
        ⟨1,1,C,-D,-E,f⟩ := by ext <;> dsimp <;> nlinarith
    rw [heq,hz.1] at hh
    omega
  refine ⟨hfpos,?_⟩
  by_contra hn
  let U := f-C-1
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hbound : convexUnitBound C D U k < 0 := by
    rcases hk with rfl | rfl
    · have hh := convexUnitBound_pos_sign (C-2) (D-3) U (by omega) (by omega) hU
      convert hh using 1 <;> dsimp [convexUnitBound,q1] <;> ring
    · by_cases hD4 : 4 ≤ D
      · have hh := convexUnitBound_neg_sign_large_d (C-2) (D-4) U (by omega) (by omega) hU
        convert hh using 1 <;> dsimp [convexUnitBound,q1] <;> ring
      · by_cases hC3 : 3 ≤ C
        · have hh := convexUnitBound_neg_sign_large_c (C-3) (D-3) U (by omega) (by omega) hU
          convert hh using 1 <;> dsimp [convexUnitBound,q1] <;> ring
        · have hDeq : D=3 := by omega
          have hCeq : C=2 := by omega
          subst D; subst C
          omega
  have hcert : convexUnitBound C D U k = q1 ⟨1,1,C,-D,-E,f⟩-8+
      (D+2)*U*(E-1) := by dsimp [convexUnitBound,U,q1]; rw [hf]; ring
  have hp : 0 ≤ (D+2)*U*(E-1) := by
    have h1 : 0 ≤ D+2 := by omega
    have h2 : 0 ≤ E-1 := by omega
    positivity
  rw [hcert,hz.1] at hbound
  nlinarith

theorem negative_third_opposed_descent (C D E f k : ℤ)
    (hz : isSolution ⟨1,1,C,-D,-E,f⟩) (hC : 0 ≤ C) (hD : 3 ≤ D) (hE : 1 ≤ E)
    (hf : f=D*C-E+k) (hk : k=4 ∨ k=-4) :
    l1 (mu3 ⟨1,1,C,-D,-E,f⟩)<l1 ⟨1,1,C,-D,-E,f⟩ := by
  by_cases hC0 : C=0
  · subst C
    exact False.elim (negative_third_zero_c_impossible D (-E) f k hz hD (by simpa using hf) hk)
  by_cases hC1 : C=1
  · subst C
    exact False.elim (negative_third_opposed_one_impossible D E f k hz hD hE (by simpa using hf) hk)
  have hC2 : 2 ≤ C := by omega
  obtain ⟨hf1,hfC⟩ := negative_third_opposed_f_bounds C D E f k hz hC2 hD hE hf hk
  have hDF : D*f≤2*E := by
    have h1 := mul_nonneg (show 0 ≤ D+2 by omega) (show 0 ≤ C-f by omega)
    rcases hk with rfl | rfl
    · have h2 : 0 ≤ (D-2)*C := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith
    · by_cases hbig : 8 ≤ (D-2)*C
      · nlinarith
      · have h2 := mul_nonneg (show 0 ≤ D-2 by omega) (show 0 ≤ C-2 by omega)
        have h3 := mul_nonneg (show 0 ≤ D-3 by omega) (show 0 ≤ C by omega)
        have hD5 : D≤5 := by nlinarith
        have hC7 : C≤7 := by nlinarith
        have hEeq : E=D*C-f-4 := by omega
        have hq := hz.1
        rw [hEeq] at hq
        interval_cases D <;> interval_cases C <;> interval_cases f <;>
          norm_num [q1] at hq
  have hDf0 : 0 ≤ D*f := by positivity
  have habs : |E-D*f|≤E := abs_le.mpr ⟨by omega,by omega⟩
  rw [mu3_drop_iff]
  have heq : f*(-D)-(-E)=E-D*f := by ring
  change |f*1-C| + |f*(-D)-(-E)| < |C| + |-E|
  simp only [mul_one]
  rw [heq,abs_of_nonpos (by omega : f-C ≤ 0),abs_of_nonneg hC,
    abs_neg,abs_of_nonneg (by omega : 0 ≤ E)]
  omega

theorem negative_two_unit_descent (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d≤-3) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  have normalized (c D e f : ℤ) (hw : isSolution ⟨1,1,c,-D,e,f⟩)
      (hD : 3 ≤ D) (hc : 0 ≤ c) :
      ∃ word : List Generator, l1 (applyWord ⟨1,1,c,-D,e,f⟩ word)<l1 ⟨1,1,c,-D,e,f⟩ := by
    obtain hk | hk := NegativeUnitEdge.unit_q2_sign ⟨1,1,c,-D,e,f⟩ hw rfl
    all_goals
      simp only [Six.a,Six.b,Six.c,Six.d,Six.e,Six.f,one_mul,mul_neg] at hk
      have hmul : c*D=D*c := mul_comm c D
      by_cases he : 0 ≤ e
      · exact negative_third_nonnegative_outside_descent c D e f (f-e-D*c)
          hw hD hc he (by ring) (by omega)
      · have hw' : isSolution ⟨1,1,c,-D,-(-e),f⟩ := by simpa using hw
        have hdrop := negative_third_opposed_descent c D (-e) f (f-e-D*c)
          hw' hc hD (by omega) (by ring) (by omega)
        exact ⟨[.m3],by simpa [applyWord,step] using hdrop⟩
  have heq : (⟨1,1,z.c,-(-z.d),z.e,z.f⟩ : Six)=z := by ext <;> simp [ha,hb]
  by_cases hc : 0 ≤ z.c
  · rw [← heq] at hz ⊢
    exact normalized z.c (-z.d) z.e z.f hz (by omega) hc
  · have hw : isSolution ⟨1,1,-z.c,-(-z.d),-z.e,-z.f⟩ := by
      have h := step_preserves_solution .s4 z hz
      simpa [step,eps4,ha,hb] using h
    obtain ⟨word,hword⟩ := normalized (-z.c) (-z.d) (-z.e) (-z.f) hw (by omega) (by omega)
    refine ⟨word,eps4_word_descent_transfer z word ?_⟩
    simpa [eps4,ha,hb] using hword

/-- No bound is imposed on the other three coefficients. -/
theorem two_unit_large_family_or_drop (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : 3 ≤ |z.d|) : FamilyOrDrop z := by
  right
  rcases le_abs.mp hd with h | h
  · exact positive_two_unit_descent z hz ha hb h
  · exact negative_two_unit_descent z hz ha hb (by omega)

end SerreMarkov.NegativeTwoUnitLarge
