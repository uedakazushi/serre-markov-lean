import SerreMarkov.PositiveShortWord

/-! # A uniform finite bound at two opposite edges equal to three

The four one-letter comparisons give an absolute-value cone inequality.
Two exact quadratic identities from the solution equations then bound the
sum of the four remaining integer coordinates. No initial height bound is
assumed.
-/

namespace SerreMarkov.PositiveEndpointThrees
open PositiveChamber PositiveShortWord NegativeDescent

set_option maxHeartbeats 1000000

theorem endpoint_threes_sum_bound (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hf : z.f=3) (ht : ShortTerminal z 1) :
    z.b+z.c+z.d+z.e≤35 := by
  let B := z.b+z.e
  let C := z.c+z.d
  let u := z.b-z.e
  let v := z.c-z.d
  let T := B+C
  let X := 2*B-3*C
  let Y := 3*B-2*C
  obtain ⟨hsol,hpos,haa,hb,hc,hd,he,hff⟩ := hz
  have hp := (shortTerminal_iff_polynomial z ⟨hsol,hpos,haa,hb,hc,hd,he,hff⟩ 1).mp ht
  have h1 := hp [.m1] (by simp [braidWords,braidMoves])
  have h2 := hp [.i1] (by simp [braidWords,braidMoves])
  have h3 := hp [.m3] (by simp [braidWords,braidMoves])
  have h4 := hp [.i3] (by simp [braidWords,braidMoves])
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,inv1,mu3,inv3] at h1 h2 h3 h4
  rw [ha,hf] at h1 h2 h3 h4
  have hcone : 5*(|u|+|v|)≤T := by
    rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv
    all_goals
      first | rw [abs_of_nonpos hu,abs_of_nonpos hv]
            | rw [abs_of_nonpos hu,abs_of_nonneg hv]
            | rw [abs_of_nonneg hu,abs_of_nonpos hv]
            | rw [abs_of_nonneg hu,abs_of_nonneg hv]
      dsimp [T,B,C,u,v]
      omega
  have hq1 := hsol.1
  dsimp [q1] at hq1
  rw [ha,hf] at hq1
  have hxid : X^2=5*v^2+32-8*q2 z := by
    dsimp [X,B,C,v,q2]
    rw [ha,hf]
    linear_combination 4*hq1
  have hyid : Y^2=5*u^2+212-28*q2 z := by
    dsimp [Y,B,C,u,q2]
    rw [ha,hf]
    linear_combination 4*hq1
  have hq2 : -4≤q2 z := by nlinarith only [hsol.2]
  have hx : X^2≤5*v^2+64 := by nlinarith only [hxid,hq2]
  have hy : Y^2≤5*u^2+324 := by nlinarith only [hyid,hq2]
  have hT0 : 0≤T := by dsimp [T,B,C]; omega
  have hprod : 0≤(T-5*(|u|+|v|))*(T+5*(|u|+|v|)) :=
    mul_nonneg (by omega) (by positivity)
  have habs : u^2+v^2≤(|u|+|v|)^2 := by
    nlinarith only [sq_abs u,sq_abs v,mul_nonneg (abs_nonneg u) (abs_nonneg v)]
  have hsq : 25*(u^2+v^2)≤T^2 := by nlinarith only [hprod,habs]
  have htxy : T=Y-X := by dsimp [T,B,C,X,Y]; ring
  have hupper : T^2≤2*X^2+2*Y^2 := by nlinarith only [htxy,sq_nonneg (X+Y)]
  have hbound : 3*T^2≤3880 := by nlinarith only [hx,hy,hsq,hupper]
  have hsmall : T≤35 := by
    by_contra hn
    have hT36 : 36≤T := by omega
    nlinarith only [hbound,hT36,sq_nonneg (T-36)]
  dsimp [T,B,C] at hsmall
  omega

theorem endpoint_threes_coordinate_bounds (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hf : z.f=3) (ht : ShortTerminal z 1) :
    3≤z.b ∧ z.b≤26 ∧ 3≤z.c ∧ z.c≤26 ∧
      3≤z.d ∧ z.d≤26 ∧ 3≤z.e ∧ z.e≤26 := by
  have hs := endpoint_threes_sum_bound z hz ha hf ht
  obtain ⟨_,_,_,hb,hc,hd,he,_⟩ := hz
  omega

end SerreMarkov.PositiveEndpointThrees
