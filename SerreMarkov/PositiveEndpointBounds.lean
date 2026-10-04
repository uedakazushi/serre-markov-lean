import SerreMarkov.PositiveShortWord

/-! # Exact finite bounds at any two small opposite edges

A polynomial certificate writes the endpoint quadratic as nonnegative
products of the four actual one-letter height guards, a square, and a positive
multiple of the total remaining height. The identity is universal; its finite
consequences use only endpoint values between three and five.
-/

namespace SerreMarkov.PositiveEndpointBounds
open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 1000000

def endpointSumBound (a f : ℤ) : ℤ :=
  if a=3 ∧ f=3 then 35 else
  if (a=3 ∧ f=4) ∨ (a=4 ∧ f=3) then 36 else
  if (a=3 ∧ f=5) ∨ (a=5 ∧ f=3) ∨ (a=4 ∧ f=4) then 40 else
  if (a=4 ∧ f=5) ∨ (a=5 ∧ f=4) then 48 else 63

private theorem slack_bound (A F b c d e k : ℤ)
    (hA : 3≤A) (hA5 : A≤5) (hF : 3≤F) (hF5 : F≤5)
    (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (he : 0≤e) (hk : -4≤k)
    (hq1 : b^2+c^2+d^2+e^2-F*b*c-A*b*d-A*c*e-F*d*e+A*F*c*d+A^2+F^2=8)
    (hq2 : c*d-b*e+A*F=k)
    (h0 : 0≤A*(b+c)-2*(d+e)) (h1 : 0≤A*(d+e)-2*(b+c))
    (h2 : 0≤F*(b+d)-2*(c+e)) (h3 : 0≤F*(c+e)-2*(b+d)) :
    b+c+d+e≤endpointSumBound A F := by
  let D := 16*(A+2)*(F+2)
  let K := (A-2)*(F-2)*(16-(A-2)*(F-2))
  let R := 8*A*F*(A+2)*(F+2)
  let T := b+c+d+e
  let Q := b^2+c^2+d^2+e^2-F*b*c-A*b*d-A*c*e-F*d*e+A*F*c*d
  let H := c*d-b*e
  let g0 := A*(b+c)-2*(d+e)
  let g1 := A*(d+e)-2*(b+c)
  let g2 := F*(b+d)-2*(c+e)
  let g3 := F*(c+e)-2*(b+d)
  have hid : D*Q-R*H = K*T^2+4*(F^2-4)*g0*g1+4*(A^2-4)*g2*g3+
      (A+2)^2*(F+2)^2*(b+e-c-d)^2 := by
    dsimp [D,Q,R,H,K,T,g0,g1,g2,g3]
    ring
  have hp0 : 0≤4*(F^2-4)*g0*g1 := by
    have hF2 : 0≤F^2-4 := by nlinarith only [hF,sq_nonneg (F-3)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF2) h0) h1
  have hp1 : 0≤4*(A^2-4)*g2*g3 := by
    have hA2 : 0≤A^2-4 := by nlinarith only [hA,sq_nonneg (A-3)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA2) h2) h3
  have hp2 : 0≤(A+2)^2*(F+2)^2*(b+e-c-d)^2 := by positivity
  have hQ : Q=8-A^2-F^2 := by dsimp [Q]; omega
  have hH : H=k-A*F := by dsimp [H]; omega
  rw [hQ,hH] at hid
  have hR : 0≤R := by dsimp [R]; positivity
  have hkr : 0≤R*(k+4) := mul_nonneg hR (by omega)
  have hcert : K*T^2≤D*(8-A^2-F^2)+R*(A*F+4) := by
    nlinarith only [hid,hp0,hp1,hp2,hkr]
  dsimp [K,D,R] at hcert
  have hT : 0≤T := by dsimp [T]; omega
  have hsmall : T≤endpointSumBound A F := by
    by_contra hn
    have hlower : endpointSumBound A F+1≤T := by omega
    have hcap0 : 0≤endpointSumBound A F+1 := by
      unfold endpointSumBound
      split_ifs <;> norm_num
    have hsquare : (endpointSumBound A F+1)^2≤T^2 := by
      have hh := mul_nonneg (show 0≤T-(endpointSumBound A F+1) by omega)
        (show 0≤T+(endpointSumBound A F+1) by omega)
      nlinarith only [hh]
    interval_cases A <;> interval_cases F
    all_goals
      norm_num [endpointSumBound] at hcert hsquare
      nlinarith only [hcert,hsquare]

  exact hsmall

/-- The endpoint-specific cap is proved from genuine one-letter terminality. -/
theorem small_endpoints_sum_bound (z : Six) (hz : Chamber z)
    (ha : 3≤z.a) (ha5 : z.a≤5) (hf : 3≤z.f) (hf5 : z.f≤5)
    (ht : ShortTerminal z 1) : z.b+z.c+z.d+z.e≤endpointSumBound z.a z.f := by
  have hp := (shortTerminal_iff_polynomial z hz 1).mp ht
  have h0 := hp [.m1] ((mem_braidWords_iff 1 _).mpr ⟨by decide,by simp [braidMoves]⟩)
  have h1 := hp [.i1] ((mem_braidWords_iff 1 _).mpr ⟨by decide,by simp [braidMoves]⟩)
  have h2 := hp [.m3] ((mem_braidWords_iff 1 _).mpr ⟨by decide,by simp [braidMoves]⟩)
  have h3 := hp [.i3] ((mem_braidWords_iff 1 _).mpr ⟨by decide,by simp [braidMoves]⟩)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,inv1,mu3,inv3] at h0 h1 h2 h3
  have hq1 := hz.1.1
  have hq2 : -4≤q2 z := by nlinarith only [hz.1.2]
  obtain ⟨_,_,_,hb,hc,hd,he,_⟩ := hz
  apply slack_bound z.a z.f z.b z.c z.d z.e (q2 z) ha ha5 hf hf5
    (by omega) (by omega) (by omega) (by omega) hq2
  · dsimp [q1] at hq1
    nlinarith only [hq1]
  · dsimp [q2]
    ring
  all_goals nlinarith only [h0,h1,h2,h3]

theorem small_endpoints_sum_le_63 (z : Six) (hz : Chamber z)
    (ha : 3≤z.a) (ha5 : z.a≤5) (hf : 3≤z.f) (hf5 : z.f≤5)
    (ht : ShortTerminal z 1) : z.b+z.c+z.d+z.e≤63 := by
  have h := small_endpoints_sum_bound z hz ha ha5 hf hf5 ht
  have hb : endpointSumBound z.a z.f≤63 := by
    unfold endpointSumBound
    split_ifs <;> norm_num
  omega

end SerreMarkov.PositiveEndpointBounds
