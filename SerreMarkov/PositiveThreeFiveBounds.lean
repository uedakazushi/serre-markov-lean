import SerreMarkov.PositiveThreeFourBounds
import SerreMarkov.PositiveShortWord

/-! Universal finite conic bounds for the actual slice a=3,d=5.
The two slacks are the actual words [m2,m1] and [i1,i2]. -/
namespace SerreMarkov.PositiveThreeFive
open PositiveChamber PositiveThreeTriangles PositiveThreeFourBounds PositiveShortWord NegativeDescent
set_option maxHeartbeats 5000000

private theorem conic_box (px pxy py kx ky C MX MY x y : ℤ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (heq : px*x^2+pxy*x*y+py*y^2-kx*x-ky*y+C=0)
    (hpx : 0 < px) (hpy : 0 < py) (hpxy : 0 ≤ pxy)
    (_hMX : 0 ≤ MX) (_hMY : 0 ≤ MY)
    (hXP : 0 ≤ 2*px*MX-kx) (hXY : 0 ≤ pxy*MX-ky)
    (hYP : 0 ≤ 2*py*MY-ky) (hYX : 0 ≤ pxy*MY-kx)
    (hX : 0 < px*MX^2-kx*MX+C) (hY : 0 < py*MY^2-ky*MY+C) : x<MX ∧ y<MY := by
  constructor
  · by_contra hn
    have hm : 0 ≤ x-MX := by omega
    have hl : 0 ≤ px*(x+MX)-kx := by
      have h := mul_nonneg hpx.le hm
      nlinarith only [h,hXP]
    have hpoly := mul_nonneg hm hl
    have hxy : 0 ≤ pxy*x-ky := by
      have h := mul_nonneg hpxy hm
      nlinarith only [h,hXY]
    have hyterm : 0 ≤ y*(py*y+pxy*x-ky) := by
      apply mul_nonneg hy
      have h := mul_nonneg hpy.le hy
      nlinarith only [h,hxy]
    nlinarith only [hpoly,hyterm,hX,heq]
  · by_contra hn
    have hm : 0 ≤ y-MY := by omega
    have hl : 0 ≤ py*(y+MY)-ky := by
      have h := mul_nonneg hpy.le hm
      nlinarith only [h,hYP]
    have hpoly := mul_nonneg hm hl
    have hyx : 0 ≤ pxy*y-kx := by
      have h := mul_nonneg hpxy hm
      nlinarith only [h,hYX]
    have hxterm : 0 ≤ x*(px*x+pxy*y-kx) := by
      apply mul_nonneg hx
      have h := mul_nonneg hpx.le hx
      nlinarith only [h,hyx]
    nlinarith only [hpoly,hxterm,hY,heq]

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨3,4,c,5,e,f⟩)
    (hm : 0 ≤ 11*c-5*e+30)
    (hi : 0 ≤ 11*f-3*e+56) : c ≤ 101 ∧ f ≤ 68 := by
  have hq : q2 ⟨3,4,c,5,e,f⟩=4 ∨ q2 ⟨3,4,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 19*c-15*f+(140)
    let y : ℤ := 35*f-15*c+(236)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 35*x^2+140*x*y+19*y^2-(39760)*x-(25312)*y+(4841088)=0 := by
      dsimp [x,y]
      linear_combination 19360*h1 - 1210*(7*c-4*e+17*f+(4))*hq
    have hb := conic_box 35 140 19 (39760) (25312) (4841088) 998 1101 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 19*c-15*f+(100)
    let y : ℤ := 35*f-15*c+(212)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 35*x^2+140*x*y+19*y^2-(39760)*x-(25312)*y+(4841088)=0 := by
      dsimp [x,y]
      linear_combination 19360*h1 - 1210*(7*c-4*e+17*f+(-4))*hq
    have hb := conic_box 35 140 19 (39760) (25312) (4841088) 998 1101 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨3,5,c,5,e,f⟩)
    (hm : 0 ≤ 10*c-5*e+25)
    (hi : 0 ≤ 10*f-3*e+49) : c ≤ 76 ∧ f ≤ 51 := by
  have hq : q2 ⟨3,5,c,5,e,f⟩=4 ∨ q2 ⟨3,5,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 25*c-15*f+(145)
    let y : ℤ := 41*f-15*c+(257)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 41*x^2+190*x*y+25*y^2-(56800)*x-(36000)*y+(6960000)=0 := by
      dsimp [x,y]
      linear_combination 40000*h1 - 1600*(10*c-5*e+22*f+(4))*hq
    have hb := conic_box 41 190 25 (56800) (36000) (6960000) 1250 1210 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 25*c-15*f+(105)
    let y : ℤ := 41*f-15*c+(233)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 41*x^2+190*x*y+25*y^2-(56800)*x-(36000)*y+(6960000)=0 := by
      dsimp [x,y]
      linear_combination 40000*h1 - 1600*(10*c-5*e+22*f+(-4))*hq
    have hb := conic_box 41 190 25 (56800) (36000) (6960000) 1250 1210 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨3,6,c,5,e,f⟩)
    (hm : 0 ≤ 9*c-5*e+20)
    (hi : 0 ≤ 9*f-3*e+42) : c ≤ 62 ∧ f ≤ 41 := by
  have hq : q2 ⟨3,6,c,5,e,f⟩=4 ∨ q2 ⟨3,6,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 29*c-15*f+(140)
    let y : ℤ := 45*f-15*c+(264)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 45*x^2+210*x*y+29*y^2-(63720)*x-(39816)*y+(7160400)=0 := by
      dsimp [x,y]
      linear_combination 58320*h1 - 1620*(13*c-6*e+27*f+(4))*hq
    have hb := conic_box 45 210 29 (63720) (39816) (7160400) 1293 1161 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 29*c-15*f+(100)
    let y : ℤ := 45*f-15*c+(240)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 45*x^2+210*x*y+29*y^2-(63720)*x-(39816)*y+(7160400)=0 := by
      dsimp [x,y]
      linear_combination 58320*h1 - 1620*(13*c-6*e+27*f+(-4))*hq
    have hb := conic_box 45 210 29 (63720) (39816) (7160400) 1293 1161 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨3,7,c,5,e,f⟩)
    (hm : 0 ≤ 8*c-5*e+15)
    (hi : 0 ≤ 8*f-3*e+35) : c ≤ 51 ∧ f ≤ 32 := by
  have hq : q2 ⟨3,7,c,5,e,f⟩=4 ∨ q2 ⟨3,7,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-15*f+(125)
    let y : ℤ := 47*f-15*c+(257)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+206*x*y+31*y^2-(60340)*x-(36820)*y+(5558364)=0 := by
      dsimp [x,y]
      linear_combination 68992*h1 - 1408*(16*c-7*e+32*f+(4))*hq
    have hb := conic_box 47 206 31 (60340) (36820) (5558364) 1184 1011 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-15*f+(85)
    let y : ℤ := 47*f-15*c+(233)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+206*x*y+31*y^2-(60340)*x-(36820)*y+(5558364)=0 := by
      dsimp [x,y]
      linear_combination 68992*h1 - 1408*(16*c-7*e+32*f+(-4))*hq
    have hb := conic_box 47 206 31 (60340) (36820) (5558364) 1184 1011 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨3,8,c,5,e,f⟩)
    (hm : 0 ≤ 7*c-5*e+10)
    (hi : 0 ≤ 7*f-3*e+28) : c ≤ 41 ∧ f ≤ 25 := by
  have hq : q2 ⟨3,8,c,5,e,f⟩=4 ∨ q2 ⟨3,8,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-15*f+(100)
    let y : ℤ := 47*f-15*c+(236)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+184*x*y+31*y^2-(48736)*x-(28608)*y+(3033600)=0 := by
      dsimp [x,y]
      linear_combination 68992*h1 - 1078*(19*c-8*e+37*f+(4))*hq
    have hb := conic_box 47 184 31 (48736) (28608) (3033600) 971 801 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-15*f+(60)
    let y : ℤ := 47*f-15*c+(212)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+184*x*y+31*y^2-(48736)*x-(28608)*y+(3033600)=0 := by
      dsimp [x,y]
      linear_combination 68992*h1 - 1078*(19*c-8*e+37*f+(-4))*hq
    have hb := conic_box 47 184 31 (48736) (28608) (3033600) 971 801 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨3,9,c,5,e,f⟩)
    (hm : 0 ≤ 6*c-5*e+5)
    (hi : 0 ≤ 6*f-3*e+21) : c ≤ 33 ∧ f ≤ 19 := by
  have hq : q2 ⟨3,9,c,5,e,f⟩=4 ∨ q2 ⟨3,9,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 29*c-15*f+(65)
    let y : ℤ := 45*f-15*c+(201)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 45*x^2+150*x*y+29*y^2-(32400)*x-(17712)*y+(723168)=0 := by
      dsimp [x,y]
      linear_combination 58320*h1 - 720*(22*c-9*e+42*f+(4))*hq
    have hb := conic_box 45 150 29 (32400) (17712) (723168) 697 567 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 29*c-15*f+(25)
    let y : ℤ := 45*f-15*c+(177)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 45*x^2+150*x*y+29*y^2-(32400)*x-(17712)*y+(723168)=0 := by
      dsimp [x,y]
      linear_combination 58320*h1 - 720*(22*c-9*e+42*f+(-4))*hq
    have hb := conic_box 45 150 29 (32400) (17712) (723168) 697 567 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨3,10,c,5,e,f⟩)
    (hm : 0 ≤ 5*c-5*e+0)
    (hi : 0 ≤ 5*f-3*e+14) : c ≤ 25 ∧ f ≤ 14 := by
  have hq : q2 ⟨3,10,c,5,e,f⟩=4 ∨ q2 ⟨3,10,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 25*c-15*f+(20)
    let y : ℤ := 41*f-15*c+(152)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 41*x^2+110*x*y+25*y^2-(15400)*x-(7000)*y+(-510000)=0 := by
      dsimp [x,y]
      linear_combination 40000*h1 - 400*(25*c-10*e+47*f+(4))*hq
    have hb := conic_box 41 110 25 (15400) (7000) (-510000) 407 341 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 25*c-15*f+(-20)
    let y : ℤ := 41*f-15*c+(128)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 41*x^2+110*x*y+25*y^2-(15400)*x-(7000)*y+(-510000)=0 := by
      dsimp [x,y]
      linear_combination 40000*h1 - 400*(25*c-10*e+47*f+(-4))*hq
    have hb := conic_box 41 110 25 (15400) (7000) (-510000) 407 341 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨3,11,c,5,e,f⟩)
    (hm : 0 ≤ 4*c-5*e+-5)
    (hi : 0 ≤ 4*f-3*e+7) : c ≤ 19 ∧ f ≤ 10 := by
  have hq : q2 ⟨3,11,c,5,e,f⟩=4 ∨ q2 ⟨3,11,c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 19*c-15*f+(-35)
    let y : ℤ := 35*f-15*c+(89)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 35*x^2+70*x*y+19*y^2-(1540)*x-(-924)*y+(-457380)=0 := by
      dsimp [x,y]
      linear_combination 19360*h1 - 160*(28*c-11*e+52*f+(4))*hq
    have hb := conic_box 35 70 19 (1540) (-924) (-457380) 139 133 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 19*c-15*f+(-75)
    let y : ℤ := 35*f-15*c+(65)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 35*x^2+70*x*y+19*y^2-(1540)*x-(-924)*y+(-457380)=0 := by
      dsimp [x,y]
      linear_combination 19360*h1 - 160*(28*c-11*e+52*f+(-4))*hq
    have hb := conic_box 35 70 19 (1540) (-924) (-457380) 139 133 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

def cBound : ℕ → ℕ
  | 4 => 101
  | 5 => 76
  | 6 => 62
  | 7 => 51
  | 8 => 41
  | 9 => 33
  | 10 => 25
  | 11 => 19
  | _ => 0

def fBound : ℕ → ℕ
  | 4 => 68
  | 5 => 51
  | 6 => 41
  | 7 => 32
  | 8 => 25
  | 9 => 19
  | 10 => 14
  | 11 => 10
  | _ => 0

private theorem fixed_bounds (b c e f : ℤ) (hb : 4 ≤ b) (hb' : b ≤ 11)
    (hz : isSolution ⟨3,b,c,5,e,f⟩)
    (hm : 0 ≤ (15-b)*c-5*e+50-5*b)
    (hi : 0 ≤ (15-b)*f-3*e+84-7*b) :
    c ≤ (cBound b.toNat : ℤ) ∧ f ≤ (fBound b.toNat : ℤ) := by
  interval_cases b
  · simpa only [cBound,fBound] using bounds_4 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_5 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_6 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_7 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_8 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_9 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_10 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_11 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

/-- A universal coordinate box derived from genuine two-step terminality. -/
theorem a_three_d_five_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=5)
    (ht : ShortTerminal z 2) :
    4 ≤ z.b ∧ z.b ≤ 11 ∧ z.c ≤ (cBound z.b.toNat : ℤ) ∧ z.f ≤ (fBound z.b.toNat : ℤ) := by
  have hb : 4 ≤ z.b := (a_three_incident_bounds z hz ha).1
  have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
  have hInv : 4 ≤ (inv1 z).d := (a_three_incident_bounds (inv1 z) hw ha).2.2.1
  simp only [inv1,ha,hd] at hInv
  have hb' : z.b ≤ 11 := by omega
  have hp := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hM := hp [.m2,.m1] (by decide +kernel)
  have hI := hp [.i1,.i2] (by decide +kernel)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2] at hM
  dsimp [heightPolynomial,coordinateSum,applyWord,step,inv1,inv2] at hI
  rw [ha,hd] at hM hI
  have hm : 0 ≤ (15-z.b)*z.c-5*z.e+50-5*z.b := by nlinarith only [hM]
  have hi : 0 ≤ (15-z.b)*z.f-3*z.e+84-7*z.b := by nlinarith only [hI]
  have heq : z=⟨3,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hb',fixed_bounds z.b z.c z.e z.f hb hb' (heq ▸ hz.1) hm hi⟩

end SerreMarkov.PositiveThreeFive
