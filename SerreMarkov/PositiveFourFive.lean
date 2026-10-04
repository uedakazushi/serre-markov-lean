import SerreMarkov.PositiveShortWord

/-! # Universal finite bounds in the positive short-terminal slice `a=4,d=5`

Actual two-letter comparisons give nonnegative slacks. The solution equations
then give positive quadratic conics, including the branches with a negative
constant. This proves a finite box without a supplied height bound; no global
small-edge or positive-classification assertion is assumed.
-/
namespace SerreMarkov.PositiveFourFive
open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 5000000

/-- A quadratic conic on the nonnegative quadrant bounds the sum of the slacks. -/
theorem asymmetric_conic_sum_bound (px q py Kx Ky C p K M x y : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hp : 0<p) (hpx : p≤px) (hpy : p≤py)
    (hq : 2*p≤q) (hKx : Kx≤K) (hKy : Ky≤K)
    (heq : px*x^2+q*x*y+py*y^2-Kx*x-Ky*y+C=0)
    (hder : 0≤2*p*M-K) (hnum : 0<p*M^2-K*M+C) : x+y<M := by
  have hxx := mul_nonneg (sub_nonneg.mpr hpx) (sq_nonneg x)
  have hyy := mul_nonneg (sub_nonneg.mpr hpy) (sq_nonneg y)
  have hxy := mul_nonneg (show 0≤q-2*p by omega) (mul_nonneg hx hy)
  have hkx := mul_nonneg (sub_nonneg.mpr hKx) hx
  have hky := mul_nonneg (sub_nonneg.mpr hKy) hy
  have hquad : p*(x+y)^2-K*(x+y)+C≤0 := by
    nlinarith only [heq,hxx,hyy,hxy,hkx,hky]
  by_contra hn
  have hm : 0≤x+y-M := by omega
  have hpM := mul_nonneg hp.le hm
  have hlin : 0≤p*(x+y+M)-K := by nlinarith only [hder,hpM]
  have hprod := mul_nonneg hm hlin
  nlinarith only [hquad,hnum,hprod]

def sumBound (b : ℤ) : ℤ :=
  if b=3 then 345 else if b=4 then 173 else if b=5 then 132 else if b=6 then 109 else if b=7 then 93 else if b=8 then 80 else if b=9 then 69 else if b=10 then 59 else if b=11 then 50 else if b=12 then 41 else if b=13 then 33 else if b=14 then 26 else if b=15 then 19 else if b=16 then 14 else if b=17 then 0 else 0

private theorem bounds_3 (c e f : ℤ) (hz : isSolution ⟨4,3,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(17)*c-5*e+(72))
    (hi : 0≤(17)*f-4*e+(91)) : c+f≤345 := by
  have hq : q2 ⟨4,3,c,5,e,f⟩=4 ∨ q2 ⟨4,3,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,3,c,5,e,f⟩-4)*(q2 ⟨4,3,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 26*c-20*f+(236)
    let y : ℤ := 35*f-20*c+(289)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 35*x^2+210*x*y+26*y^2-(72450)*x-(59556)*y+(15444198)=0 := by
      dsimp [x,y]
      linear_combination 26010*h1 - 2890*((7)*c+(11)*f-3*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 35 210 26 (72450) (59556) (15444198) 26 (72450) 2555 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 26*c-20*f+(196)
    let y : ℤ := 35*f-20*c+(257)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 35*x^2+210*x*y+26*y^2-(72450)*x-(59556)*y+(15444198)=0 := by
      dsimp [x,y]
      linear_combination 26010*h1 - 2890*((7)*c+(11)*f-3*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 35 210 26 (72450) (59556) (15444198) 26 (72450) 2555 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨4,4,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(16)*c-5*e+(66))
    (hi : 0≤(16)*f-4*e+(84)) : c+f≤173 := by
  have hq : q2 ⟨4,4,c,5,e,f⟩=4 ∨ q2 ⟨4,4,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,4,c,5,e,f⟩-4)*(q2 ⟨4,4,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 39*c-20*f+(284)
    let y : ℤ := 48*f-20*c+(352)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 48*x^2+408*x*y+39*y^2-(162432)*x-(133920)*y+(40953600)=0 := by
      dsimp [x,y]
      linear_combination 94208*h1 - 5888*((11)*c+(16)*f-4*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 48 408 39 (162432) (133920) (40953600) 39 (162432) 3897 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 39*c-20*f+(244)
    let y : ℤ := 48*f-20*c+(320)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 48*x^2+408*x*y+39*y^2-(162432)*x-(133920)*y+(40953600)=0 := by
      dsimp [x,y]
      linear_combination 94208*h1 - 5888*((11)*c+(16)*f-4*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 48 408 39 (162432) (133920) (40953600) 39 (162432) 3897 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨4,5,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(15)*c-5*e+(60))
    (hi : 0≤(15)*f-4*e+(77)) : c+f≤132 := by
  have hq : q2 ⟨4,5,c,5,e,f⟩=4 ∨ q2 ⟨4,5,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,5,c,5,e,f⟩-4)*(q2 ⟨4,5,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 50*c-20*f+(320)
    let y : ℤ := 59*f-20*c+(401)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+550*x*y+50*y^2-(247150)*x-(203500)*y+(68123750)=0 := by
      dsimp [x,y]
      linear_combination 191250*h1 - 7650*((15)*c+(21)*f-5*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 59 550 50 (247150) (203500) (68123750) 50 (247150) 4651 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 50*c-20*f+(280)
    let y : ℤ := 59*f-20*c+(369)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+550*x*y+50*y^2-(247150)*x-(203500)*y+(68123750)=0 := by
      dsimp [x,y]
      linear_combination 191250*h1 - 7650*((15)*c+(21)*f-5*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 59 550 50 (247150) (203500) (68123750) 50 (247150) 4651 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨4,6,c,5,e,f⟩) (_hf : 3≤f)
    (hm : 0≤(14)*c-5*e+(54))
    (hi : 0≤(14)*f-4*e+(70)) : c+f≤109 := by
  have hq : q2 ⟨4,6,c,5,e,f⟩=4 ∨ q2 ⟨4,6,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,6,c,5,e,f⟩-4)*(q2 ⟨4,6,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 59*c-20*f+(344)
    let y : ℤ := 68*f-20*c+(436)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 68*x^2+642*x*y+59*y^2-(313704)*x-(257568)*y+(89322624)=0 := by
      dsimp [x,y]
      linear_combination 303408*h1 - 8428*((19)*c+(26)*f-6*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 68 642 59 (313704) (257568) (89322624) 59 (313704) 5017 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 59*c-20*f+(304)
    let y : ℤ := 68*f-20*c+(404)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 68*x^2+642*x*y+59*y^2-(313704)*x-(257568)*y+(89322624)=0 := by
      dsimp [x,y]
      linear_combination 303408*h1 - 8428*((19)*c+(26)*f-6*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 68 642 59 (313704) (257568) (89322624) 59 (313704) 5017 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨4,7,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(13)*c-5*e+(48))
    (hi : 0≤(13)*f-4*e+(63)) : c+f≤93 := by
  have hq : q2 ⟨4,7,c,5,e,f⟩=4 ∨ q2 ⟨4,7,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,7,c,5,e,f⟩-4)*(q2 ⟨4,7,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 66*c-20*f+(356)
    let y : ℤ := 75*f-20*c+(457)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 75*x^2+690*x*y+66*y^2-(354690)*x-(290052)*y+(99396990)=0 := by
      dsimp [x,y]
      linear_combination 414050*h1 - 8450*((23)*c+(31)*f-7*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 75 690 66 (354690) (290052) (99396990) 66 (354690) 5079 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 66*c-20*f+(316)
    let y : ℤ := 75*f-20*c+(425)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 75*x^2+690*x*y+66*y^2-(354690)*x-(290052)*y+(99396990)=0 := by
      dsimp [x,y]
      linear_combination 414050*h1 - 8450*((23)*c+(31)*f-7*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 75 690 66 (354690) (290052) (99396990) 66 (354690) 5079 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨4,8,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(12)*c-5*e+(42))
    (hi : 0≤(12)*f-4*e+(56)) : c+f≤80 := by
  have hq : q2 ⟨4,8,c,5,e,f⟩=4 ∨ q2 ⟨4,8,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,8,c,5,e,f⟩-4)*(q2 ⟨4,8,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 71*c-20*f+(356)
    let y : ℤ := 80*f-20*c+(464)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 80*x^2+700*x*y+71*y^2-(367360)*x-(298816)*y+(96570368)=0 := by
      dsimp [x,y]
      linear_combination 506880*h1 - 7920*((27)*c+(36)*f-8*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 80 700 71 (367360) (298816) (96570368) 71 (367360) 4898 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 71*c-20*f+(316)
    let y : ℤ := 80*f-20*c+(432)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 80*x^2+700*x*y+71*y^2-(367360)*x-(298816)*y+(96570368)=0 := by
      dsimp [x,y]
      linear_combination 506880*h1 - 7920*((27)*c+(36)*f-8*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 80 700 71 (367360) (298816) (96570368) 71 (367360) 4898 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨4,9,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(11)*c-5*e+(36))
    (hi : 0≤(11)*f-4*e+(49)) : c+f≤69 := by
  have hq : q2 ⟨4,9,c,5,e,f⟩=4 ∨ q2 ⟨4,9,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,9,c,5,e,f⟩-4)*(q2 ⟨4,9,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 74*c-20*f+(344)
    let y : ℤ := 83*f-20*c+(457)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 83*x^2+678*x*y+74*y^2-(352782)*x-(284940)*y+(82304910)=0 := by
      dsimp [x,y]
      linear_combination 568458*h1 - 7018*((31)*c+(41)*f-9*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 83 678 74 (352782) (284940) (82304910) 74 (352782) 4523 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 74*c-20*f+(304)
    let y : ℤ := 83*f-20*c+(425)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 83*x^2+678*x*y+74*y^2-(352782)*x-(284940)*y+(82304910)=0 := by
      dsimp [x,y]
      linear_combination 568458*h1 - 7018*((31)*c+(41)*f-9*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 83 678 74 (352782) (284940) (82304910) 74 (352782) 4523 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨4,10,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(10)*c-5*e+(30))
    (hi : 0≤(10)*f-4*e+(42)) : c+f≤59 := by
  have hq : q2 ⟨4,10,c,5,e,f⟩=4 ∨ q2 ⟨4,10,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,10,c,5,e,f⟩-4)*(q2 ⟨4,10,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 75*c-20*f+(320)
    let y : ℤ := 84*f-20*c+(436)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 84*x^2+630*x*y+75*y^2-(315000)*x-(252000)*y+(60480000)=0 := by
      dsimp [x,y]
      linear_combination 590000*h1 - 5900*((35)*c+(46)*f-10*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 84 630 75 (315000) (252000) (60480000) 75 (315000) 4000 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 75*c-20*f+(280)
    let y : ℤ := 84*f-20*c+(404)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 84*x^2+630*x*y+75*y^2-(315000)*x-(252000)*y+(60480000)=0 := by
      dsimp [x,y]
      linear_combination 590000*h1 - 5900*((35)*c+(46)*f-10*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 84 630 75 (315000) (252000) (60480000) 75 (315000) 4000 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨4,11,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(9)*c-5*e+(24))
    (hi : 0≤(9)*f-4*e+(35)) : c+f≤50 := by
  have hq : q2 ⟨4,11,c,5,e,f⟩=4 ∨ q2 ⟨4,11,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,11,c,5,e,f⟩-4)*(q2 ⟨4,11,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 74*c-20*f+(284)
    let y : ℤ := 83*f-20*c+(401)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 83*x^2+562*x*y+74*y^2-(260194)*x-(205348)*y+(36200054)=0 := by
      dsimp [x,y]
      linear_combination 568458*h1 - 4698*((39)*c+(51)*f-11*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 83 562 74 (260194) (205348) (36200054) 74 (260194) 3373 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 74*c-20*f+(244)
    let y : ℤ := 83*f-20*c+(369)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 83*x^2+562*x*y+74*y^2-(260194)*x-(205348)*y+(36200054)=0 := by
      dsimp [x,y]
      linear_combination 568458*h1 - 4698*((39)*c+(51)*f-11*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 83 562 74 (260194) (205348) (36200054) 74 (260194) 3373 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨4,12,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(8)*c-5*e+(18))
    (hi : 0≤(8)*f-4*e+(28)) : c+f≤41 := by
  have hq : q2 ⟨4,12,c,5,e,f⟩=4 ∨ q2 ⟨4,12,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,12,c,5,e,f⟩-4)*(q2 ⟨4,12,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 71*c-20*f+(236)
    let y : ℤ := 80*f-20*c+(352)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 80*x^2+480*x*y+71*y^2-(195840)*x-(151392)*y+(14503680)=0 := by
      dsimp [x,y]
      linear_combination 506880*h1 - 3520*((43)*c+(56)*f-12*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 80 480 71 (195840) (151392) (14503680) 71 (195840) 2684 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 71*c-20*f+(196)
    let y : ℤ := 80*f-20*c+(320)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 80*x^2+480*x*y+71*y^2-(195840)*x-(151392)*y+(14503680)=0 := by
      dsimp [x,y]
      linear_combination 506880*h1 - 3520*((43)*c+(56)*f-12*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 80 480 71 (195840) (151392) (14503680) 71 (195840) 2684 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨4,13,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(7)*c-5*e+(12))
    (hi : 0≤(7)*f-4*e+(21)) : c+f≤33 := by
  have hq : q2 ⟨4,13,c,5,e,f⟩=4 ∨ q2 ⟨4,13,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,13,c,5,e,f⟩-4)*(q2 ⟨4,13,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 66*c-20*f+(176)
    let y : ℤ := 75*f-20*c+(289)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 75*x^2+390*x*y+66*y^2-(129870)*x-(96876)*y+(-793962)=0 := by
      dsimp [x,y]
      linear_combination 414050*h1 - 2450*((47)*c+(61)*f-13*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 75 390 66 (129870) (96876) (-793962) 66 (129870) 1975 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 66*c-20*f+(136)
    let y : ℤ := 75*f-20*c+(257)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 75*x^2+390*x*y+66*y^2-(129870)*x-(96876)*y+(-793962)=0 := by
      dsimp [x,y]
      linear_combination 414050*h1 - 2450*((47)*c+(61)*f-13*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 75 390 66 (129870) (96876) (-793962) 66 (129870) 1975 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_14 (c e f : ℤ) (hz : isSolution ⟨4,14,c,5,e,f⟩) (_hf : 3≤f)
    (hm : 0≤(6)*c-5*e+(6))
    (hi : 0≤(6)*f-4*e+(14)) : c+f≤26 := by
  have hq : q2 ⟨4,14,c,5,e,f⟩=4 ∨ q2 ⟨4,14,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,14,c,5,e,f⟩-4)*(q2 ⟨4,14,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 59*c-20*f+(104)
    let y : ℤ := 68*f-20*c+(212)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 68*x^2+298*x*y+59*y^2-(69832)*x-(48160)*y+(-7934080)=0 := by
      dsimp [x,y]
      linear_combination 303408*h1 - 1548*((51)*c+(66)*f-14*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 68 298 59 (69832) (48160) (-7934080) 59 (69832) 1290 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 59*c-20*f+(64)
    let y : ℤ := 68*f-20*c+(180)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 68*x^2+298*x*y+59*y^2-(69832)*x-(48160)*y+(-7934080)=0 := by
      dsimp [x,y]
      linear_combination 303408*h1 - 1548*((51)*c+(66)*f-14*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 68 298 59 (69832) (48160) (-7934080) 59 (69832) 1290 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_15 (c e f : ℤ) (hz : isSolution ⟨4,15,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(5)*c-5*e+(0))
    (hi : 0≤(5)*f-4*e+(7)) : c+f≤19 := by
  have hq : q2 ⟨4,15,c,5,e,f⟩=4 ∨ q2 ⟨4,15,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,15,c,5,e,f⟩-4)*(q2 ⟨4,15,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 50*c-20*f+(20)
    let y : ℤ := 59*f-20*c+(121)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+210*x*y+50*y^2-(22050)*x-(10500)*y+(-7571250)=0 := by
      dsimp [x,y]
      linear_combination 191250*h1 - 850*((55)*c+(71)*f-15*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 59 210 50 (22050) (10500) (-7571250) 50 (22050) 669 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 50*c-20*f+(-20)
    let y : ℤ := 59*f-20*c+(89)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+210*x*y+50*y^2-(22050)*x-(10500)*y+(-7571250)=0 := by
      dsimp [x,y]
      linear_combination 191250*h1 - 850*((55)*c+(71)*f-15*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 59 210 50 (22050) (10500) (-7571250) 50 (22050) 669 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_16 (c e f : ℤ) (hz : isSolution ⟨4,16,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(4)*c-5*e+(-6))
    (hi : 0≤(4)*f-4*e+(0)) : c+f≤14 := by
  have hq : q2 ⟨4,16,c,5,e,f⟩=4 ∨ q2 ⟨4,16,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,16,c,5,e,f⟩-4)*(q2 ⟨4,16,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 39*c-20*f+(-76)
    let y : ℤ := 48*f-20*c+(16)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 48*x^2+132*x*y+39*y^2-(-9216)*x-(-12672)*y+(-2543616)=0 := by
      dsimp [x,y]
      linear_combination 94208*h1 - 368*((59)*c+(76)*f-16*e+(4))*hq

    have hb := asymmetric_conic_sum_bound 48 132 39 (-9216) (-12672) (-2543616) 39 (-9216) 165 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 39*c-20*f+(-116)
    let y : ℤ := 48*f-20*c+(-16)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 48*x^2+132*x*y+39*y^2-(-9216)*x-(-12672)*y+(-2543616)=0 := by
      dsimp [x,y]
      linear_combination 94208*h1 - 368*((59)*c+(76)*f-16*e+(-4))*hq

    have hb := asymmetric_conic_sum_bound 48 132 39 (-9216) (-12672) (-2543616) 39 (-9216) 165 x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_17 (c e f : ℤ) (hz : isSolution ⟨4,17,c,5,e,f⟩) (_hf : 3≤f)
    (hm : 0≤(3)*c-5*e+(-12))
    (hi : 0≤(3)*f-4*e+(-7)) : c+f≤0 := by
  have hq : q2 ⟨4,17,c,5,e,f⟩=4 ∨ q2 ⟨4,17,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨4,17,c,5,e,f⟩-4)*(q2 ⟨4,17,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 26*c-20*f+(-184)
    let y : ℤ := 35*f-20*c+(-103)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 35*x^2+70*x*y+26*y^2-(-22610)*x-(-20468)*y+(3014270)=0 := by
      dsimp [x,y]
      linear_combination 26010*h1 - 90*((63)*c+(81)*f-17*e+(4))*hq

    have hxy := mul_nonneg hx hy
    have hp : 0<35*x^2+70*x*y+26*y^2-(-22610)*x-(-20468)*y+(3014270) := by
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

  · dsimp [q2] at hq
    let x : ℤ := 26*c-20*f+(-224)
    let y : ℤ := 35*f-20*c+(-135)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 35*x^2+70*x*y+26*y^2-(-22610)*x-(-20468)*y+(3014270)=0 := by
      dsimp [x,y]
      linear_combination 26010*h1 - 90*((63)*c+(81)*f-17*e+(-4))*hq

    have hxy := mul_nonneg hx hy
    have hp : 0<35*x^2+70*x*y+26*y^2-(-22610)*x-(-20468)*y+(3014270) := by
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

private theorem slice_bounds (b c e f : ℤ) (hbLo : 3≤b) (hbHi : b≤17)
    (hz : isSolution ⟨4,b,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(20-b)*c-5*e+90-6*b)
    (hi : 0≤(20-b)*f-4*e+112-7*b) : c+f≤sumBound b := by
  interval_cases b

  · simpa [sumBound] using bounds_3 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_4 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_5 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_6 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_7 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_8 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_9 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_10 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_11 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_12 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_13 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_14 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_15 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_16 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_17 c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])

/-- Each fixed first triangle gives a finite bound for the remaining coefficients. -/
theorem a_four_d_five_bounds (z : Six) (hz : Chamber z) (ha : z.a=4) (hd : z.d=5)
    (ht : ShortTerminal z 2) : 3≤z.b ∧ z.b≤17 ∧ z.c+z.f≤sumBound z.b := by
  have hb : 3≤z.b := hz.2.2.2.1
  have hf : 3≤z.f := hz.2.2.2.2.2.2.2
  have hInv := (step_preserves_chamber .i1 True.intro z hz).2.2.2.2.2.1
  simp only [step,inv1,ha,hd] at hInv
  have hbHi : z.b≤17 := by omega
  have H := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hm := H [.m2,.m1] (by decide)
  have hi := H [.i1,.i2] (by decide)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,inv1,inv2] at hm hi
  simp only [ha,hd] at hm hi
  have hm' : 0≤(20-z.b)*z.c-5*z.e+90-6*z.b := by nlinarith only [hm]
  have hi' : 0≤(20-z.b)*z.f-4*z.e+112-7*z.b := by nlinarith only [hi]
  have heq : z=⟨4,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hbHi,slice_bounds _ _ _ _ hb hbHi (heq ▸ hz.1) hf hm' hi'⟩

private theorem branch_le {p : Prop} [Decidable p] {u v : ℤ}
    (hu : u≤345) (hv : v≤345) : (if p then u else v)≤345 := by
  split_ifs <;> assumption

private theorem sumBound_le (b : ℤ) : sumBound b≤345 := by
  unfold sumBound
  exact (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (branch_le (by norm_num) (by norm_num))))))))))))))))

/-- A uniform finite box, deduced rather than assumed. -/
theorem a_four_d_five_coordinate_bounds (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=5) (ht : ShortTerminal z 2) :
    3≤z.b ∧ z.b≤16 ∧ 3≤z.c ∧ z.c≤342 ∧ 3≤z.e ∧ z.e≤576 ∧ 3≤z.f ∧ z.f≤342 := by
  obtain ⟨hb,hbHi,hcf⟩ := a_four_d_five_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,he,hf⟩ := hz.2.2
  have hsum : z.c+z.f≤345 := hcf.trans (sumBound_le z.b)
  have hb16 : z.b≤16 := by
    by_contra hn
    have hb17 : z.b=17 := by omega
    simp [hb17,sumBound] at hcf
    omega
  have hq : -4≤q2 z := by nlinarith only [hz.1.2]
  simp only [q2,ha,hd] at hq
  have hbe := mul_nonneg (show 0≤z.b-3 by omega) (show 0≤z.e by omega)
  have he576 : z.e≤576 := by nlinarith only [hq,hsum,hbe,hf]
  exact ⟨hb,hb16,hc,by omega,he,he576,hf,by omega⟩

end SerreMarkov.PositiveFourFive
