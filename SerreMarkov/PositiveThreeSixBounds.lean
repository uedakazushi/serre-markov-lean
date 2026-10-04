import SerreMarkov.PositiveThreeFourBounds
import SerreMarkov.PositiveShortWord

/-! Universal finite conic bounds for the actual slice a=3,d=6.
The two slacks are the actual words [m2,m1] and [i1,i2]. -/
namespace SerreMarkov.PositiveThreeSix
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

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨3,4,c,6,e,f⟩)
    (hm : 0 ≤ 14*c-6*e+40)
    (hi : 0 ≤ 14*f-3*e+88) : c ≤ 152 ∧ f ≤ 90 := by
  have hq : q2 ⟨3,4,c,6,e,f⟩=4 ∨ q2 ⟨3,4,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 20*c-18*f+(184)
    let y : ℤ := 47*f-18*c+(364)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+190*x*y+20*y^2-(81920)*x-(44480)*y+(13676480)=0 := by
      dsimp [x,y]
      linear_combination 34496*h1 - 2156*(6*c-4*e+21*f+(4))*hq
    have hb := conic_box 47 190 20 (81920) (44480) (13676480) 1556 1856 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 20*c-18*f+(136)
    let y : ℤ := 47*f-18*c+(340)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+190*x*y+20*y^2-(81920)*x-(44480)*y+(13676480)=0 := by
      dsimp [x,y]
      linear_combination 34496*h1 - 2156*(6*c-4*e+21*f+(-4))*hq
    have hb := conic_box 47 190 20 (81920) (44480) (13676480) 1556 1856 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨3,5,c,6,e,f⟩)
    (hm : 0 ≤ 13*c-6*e+35)
    (hi : 0 ≤ 13*f-3*e+80) : c ≤ 116 ∧ f ≤ 69 := by
  have hq : q2 ⟨3,5,c,6,e,f⟩=4 ∨ q2 ⟨3,5,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 29*c-18*f+(199)
    let y : ℤ := 56*f-18*c+(412)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 56*x^2+296*x*y+29*y^2-(138000)*x-(75000)*y+(24641400)=0 := by
      dsimp [x,y]
      linear_combination 84500*h1 - 3380*(9*c-5*e+27*f+(4))*hq
    have hb := conic_box 56 296 29 (138000) (75000) (24641400) 2271 2200 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 29*c-18*f+(151)
    let y : ℤ := 56*f-18*c+(388)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 56*x^2+296*x*y+29*y^2-(138000)*x-(75000)*y+(24641400)=0 := by
      dsimp [x,y]
      linear_combination 84500*h1 - 3380*(9*c-5*e+27*f+(-4))*hq
    have hb := conic_box 56 296 29 (138000) (75000) (24641400) 2271 2200 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨3,6,c,6,e,f⟩)
    (hm : 0 ≤ 12*c-6*e+30)
    (hi : 0 ≤ 12*f-3*e+72) : c ≤ 97 ∧ f ≤ 57 := by
  have hq : q2 ⟨3,6,c,6,e,f⟩=4 ∨ q2 ⟨3,6,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 36*c-18*f+(204)
    let y : ℤ := 63*f-18*c+(444)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 7*x^2+40*x*y+4*y^2-(19800)*x-(10656)*y+(3530160)=0 := by
      dsimp [x,y]
      linear_combination 15552*h1 - 432*(12*c-6*e+33*f+(4))*hq
    have hb := conic_box 7 40 4 (19800) (10656) (3530160) 2638 2277 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 36*c-18*f+(156)
    let y : ℤ := 63*f-18*c+(420)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 7*x^2+40*x*y+4*y^2-(19800)*x-(10656)*y+(3530160)=0 := by
      dsimp [x,y]
      linear_combination 15552*h1 - 432*(12*c-6*e+33*f+(-4))*hq
    have hb := conic_box 7 40 4 (19800) (10656) (3530160) 2638 2277 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨3,7,c,6,e,f⟩)
    (hm : 0 ≤ 11*c-6*e+25)
    (hi : 0 ≤ 11*f-3*e+64) : c ≤ 83 ∧ f ≤ 47 := by
  have hq : q2 ⟨3,7,c,6,e,f⟩=4 ∨ q2 ⟨3,7,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 41*c-18*f+(199)
    let y : ℤ := 68*f-18*c+(460)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 68*x^2+388*x*y+41*y^2-(197624)*x-(104636)*y+(33046580)=0 := by
      dsimp [x,y]
      linear_combination 189728*h1 - 3872*(15*c-7*e+39*f+(4))*hq
    have hb := conic_box 68 388 41 (197624) (104636) (33046580) 2729 2183 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 41*c-18*f+(151)
    let y : ℤ := 68*f-18*c+(436)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 68*x^2+388*x*y+41*y^2-(197624)*x-(104636)*y+(33046580)=0 := by
      dsimp [x,y]
      linear_combination 189728*h1 - 3872*(15*c-7*e+39*f+(-4))*hq
    have hb := conic_box 68 388 41 (197624) (104636) (33046580) 2729 2183 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨3,8,c,6,e,f⟩)
    (hm : 0 ≤ 10*c-6*e+20)
    (hi : 0 ≤ 10*f-3*e+56) : c ≤ 72 ∧ f ≤ 39 := by
  have hq : q2 ⟨3,8,c,6,e,f⟩=4 ∨ q2 ⟨3,8,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 44*c-18*f+(184)
    let y : ℤ := 71*f-18*c+(460)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+386*x*y+44*y^2-(195648)*x-(101184)*y+(28582656)=0 := by
      dsimp [x,y]
      linear_combination 224000*h1 - 3500*(18*c-8*e+45*f+(4))*hq
    have hb := conic_box 71 386 44 (195648) (101184) (28582656) 2601 1970 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 44*c-18*f+(136)
    let y : ℤ := 71*f-18*c+(436)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+386*x*y+44*y^2-(195648)*x-(101184)*y+(28582656)=0 := by
      dsimp [x,y]
      linear_combination 224000*h1 - 3500*(18*c-8*e+45*f+(-4))*hq
    have hb := conic_box 71 386 44 (195648) (101184) (28582656) 2601 1970 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨3,9,c,6,e,f⟩)
    (hm : 0 ≤ 9*c-6*e+15)
    (hi : 0 ≤ 9*f-3*e+48) : c ≤ 62 ∧ f ≤ 32 := by
  have hq : q2 ⟨3,9,c,6,e,f⟩=4 ∨ q2 ⟨3,9,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 45*c-18*f+(159)
    let y : ℤ := 72*f-18*c+(444)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 8*x^2+40*x*y+5*y^2-(19440)*x-(9720)*y+(2245320)=0 := by
      dsimp [x,y]
      linear_combination 26244*h1 - 324*(21*c-9*e+51*f+(4))*hq
    have hb := conic_box 8 40 5 (19440) (9720) (2245320) 2309 1677 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 45*c-18*f+(111)
    let y : ℤ := 72*f-18*c+(420)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 8*x^2+40*x*y+5*y^2-(19440)*x-(9720)*y+(2245320)=0 := by
      dsimp [x,y]
      linear_combination 26244*h1 - 324*(21*c-9*e+51*f+(-4))*hq
    have hb := conic_box 8 40 5 (19440) (9720) (2245320) 2309 1677 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨3,10,c,6,e,f⟩)
    (hm : 0 ≤ 8*c-6*e+10)
    (hi : 0 ≤ 8*f-3*e+40) : c ≤ 52 ∧ f ≤ 26 := by
  have hq : q2 ⟨3,10,c,6,e,f⟩=4 ∨ q2 ⟨3,10,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 44*c-18*f+(124)
    let y : ℤ := 71*f-18*c+(412)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+316*x*y+44*y^2-(140600)*x-(66800)*y+(10655600)=0 := by
      dsimp [x,y]
      linear_combination 224000*h1 - 2240*(24*c-10*e+57*f+(4))*hq
    have hb := conic_box 71 316 44 (140600) (66800) (10655600) 1902 1338 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 44*c-18*f+(76)
    let y : ℤ := 71*f-18*c+(388)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+316*x*y+44*y^2-(140600)*x-(66800)*y+(10655600)=0 := by
      dsimp [x,y]
      linear_combination 224000*h1 - 2240*(24*c-10*e+57*f+(-4))*hq
    have hb := conic_box 71 316 44 (140600) (66800) (10655600) 1902 1338 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨3,11,c,6,e,f⟩)
    (hm : 0 ≤ 7*c-6*e+5)
    (hi : 0 ≤ 7*f-3*e+32) : c ≤ 43 ∧ f ≤ 20 := by
  have hq : q2 ⟨3,11,c,6,e,f⟩=4 ∨ q2 ⟨3,11,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 41*c-18*f+(79)
    let y : ℤ := 68*f-18*c+(364)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 68*x^2+260*x*y+41*y^2-(99000)*x-(43164)*y+(2635380)=0 := by
      dsimp [x,y]
      linear_combination 189728*h1 - 1568*(27*c-11*e+63*f+(4))*hq
    have hb := conic_box 68 260 41 (99000) (43164) (2635380) 1429 988 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 41*c-18*f+(31)
    let y : ℤ := 68*f-18*c+(340)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 68*x^2+260*x*y+41*y^2-(99000)*x-(43164)*y+(2635380)=0 := by
      dsimp [x,y]
      linear_combination 189728*h1 - 1568*(27*c-11*e+63*f+(-4))*hq
    have hb := conic_box 68 260 41 (99000) (43164) (2635380) 1429 988 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨3,12,c,6,e,f⟩)
    (hm : 0 ≤ 6*c-6*e+0)
    (hi : 0 ≤ 6*f-3*e+24) : c ≤ 34 ∧ f ≤ 16 := by
  have hq : q2 ⟨3,12,c,6,e,f⟩=4 ∨ q2 ⟨3,12,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 36*c-18*f+(24)
    let y : ℤ := 63*f-18*c+(300)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 7*x^2+22*x*y+4*y^2-(6336)*x-(2304)*y+(-221760)=0 := by
      dsimp [x,y]
      linear_combination 15552*h1 - 108*(30*c-12*e+69*f+(4))*hq
    have hb := conic_box 7 22 4 (6336) (2304) (-221760) 939 661 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 36*c-18*f+(-24)
    let y : ℤ := 63*f-18*c+(276)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 7*x^2+22*x*y+4*y^2-(6336)*x-(2304)*y+(-221760)=0 := by
      dsimp [x,y]
      linear_combination 15552*h1 - 108*(30*c-12*e+69*f+(-4))*hq
    have hb := conic_box 7 22 4 (6336) (2304) (-221760) 939 661 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨3,13,c,6,e,f⟩)
    (hm : 0 ≤ 5*c-6*e+-5)
    (hi : 0 ≤ 5*f-3*e+16) : c ≤ 26 ∧ f ≤ 11 := by
  have hq : q2 ⟨3,13,c,6,e,f⟩=4 ∨ q2 ⟨3,13,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 29*c-18*f+(-41)
    let y : ℤ := 56*f-18*c+(220)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 56*x^2+136*x*y+29*y^2-(21008)*x-(3224)*y+(-2781064)=0 := by
      dsimp [x,y]
      linear_combination 84500*h1 - 500*(33*c-13*e+75*f+(4))*hq
    have hb := conic_box 56 136 29 (21008) (3224) (-2781064) 479 371 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 29*c-18*f+(-89)
    let y : ℤ := 56*f-18*c+(196)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 56*x^2+136*x*y+29*y^2-(21008)*x-(3224)*y+(-2781064)=0 := by
      dsimp [x,y]
      linear_combination 84500*h1 - 500*(33*c-13*e+75*f+(-4))*hq
    have hb := conic_box 56 136 29 (21008) (3224) (-2781064) 479 371 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_14 (c e f : ℤ) (hz : isSolution ⟨3,14,c,6,e,f⟩)
    (hm : 0 ≤ 4*c-6*e+-10)
    (hi : 0 ≤ 4*f-3*e+8) : c ≤ 19 ∧ f ≤ 7 := by
  have hq : q2 ⟨3,14,c,6,e,f⟩=4 ∨ q2 ⟨3,14,c,6,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 20*c-18*f+(-116)
    let y : ℤ := 47*f-18*c+(124)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+80*x*y+20*y^2-(-4200)*x-(-6720)*y+(-787920)=0 := by
      dsimp [x,y]
      linear_combination 34496*h1 - 176*(36*c-14*e+81*f+(4))*hq
    have hb := conic_box 47 80 20 (-4200) (-6720) (-787920) 93 93 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 20*c-18*f+(-164)
    let y : ℤ := 47*f-18*c+(100)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 47*x^2+80*x*y+20*y^2-(-4200)*x-(-6720)*y+(-787920)=0 := by
      dsimp [x,y]
      linear_combination 34496*h1 - 176*(36*c-14*e+81*f+(-4))*hq
    have hb := conic_box 47 80 20 (-4200) (-6720) (-787920) 93 93 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

def cBound : ℕ → ℕ
  | 4 => 152
  | 5 => 116
  | 6 => 97
  | 7 => 83
  | 8 => 72
  | 9 => 62
  | 10 => 52
  | 11 => 43
  | 12 => 34
  | 13 => 26
  | 14 => 19
  | _ => 0

def fBound : ℕ → ℕ
  | 4 => 90
  | 5 => 69
  | 6 => 57
  | 7 => 47
  | 8 => 39
  | 9 => 32
  | 10 => 26
  | 11 => 20
  | 12 => 16
  | 13 => 11
  | 14 => 7
  | _ => 0

private theorem fixed_bounds (b c e f : ℤ) (hb : 4 ≤ b) (hb' : b ≤ 14)
    (hz : isSolution ⟨3,b,c,6,e,f⟩)
    (hm : 0 ≤ (18-b)*c-6*e+60-5*b)
    (hi : 0 ≤ (18-b)*f-3*e+120-8*b) :
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
  · simpa only [cBound,fBound] using bounds_12 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_13 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_14 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

/-- A universal coordinate box derived from genuine two-step terminality. -/
theorem a_three_d_six_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=6)
    (ht : ShortTerminal z 2) :
    4 ≤ z.b ∧ z.b ≤ 14 ∧ z.c ≤ (cBound z.b.toNat : ℤ) ∧ z.f ≤ (fBound z.b.toNat : ℤ) := by
  have hb : 4 ≤ z.b := (a_three_incident_bounds z hz ha).1
  have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
  have hInv : 4 ≤ (inv1 z).d := (a_three_incident_bounds (inv1 z) hw ha).2.2.1
  simp only [inv1,ha,hd] at hInv
  have hb' : z.b ≤ 14 := by omega
  have hp := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hM := hp [.m2,.m1] (by decide +kernel)
  have hI := hp [.i1,.i2] (by decide +kernel)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2] at hM
  dsimp [heightPolynomial,coordinateSum,applyWord,step,inv1,inv2] at hI
  rw [ha,hd] at hM hI
  have hm : 0 ≤ (18-z.b)*z.c-6*z.e+60-5*z.b := by nlinarith only [hM]
  have hi : 0 ≤ (18-z.b)*z.f-3*z.e+120-8*z.b := by nlinarith only [hI]
  have heq : z=⟨3,z.b,z.c,6,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hb',fixed_bounds z.b z.c z.e z.f hb hb' (heq ▸ hz.1) hm hi⟩

end SerreMarkov.PositiveThreeSix
