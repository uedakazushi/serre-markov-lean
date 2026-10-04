import SerreMarkov.PositiveThreeFourBounds
import SerreMarkov.PositiveShortWord

/-! Universal finite conic bounds for the actual slice a=3,d=8.
The two slacks are the actual words [m2,m1] and [i1,i2]. -/
namespace SerreMarkov.PositiveThreeEight
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

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨3,4,c,8,e,f⟩)
    (hm : 0 ≤ 20*c-8*e+60)
    (hi : 0 ≤ 20*f-3*e+170) : c ≤ 343 ∧ f ≤ 154 := by
  have hq : q2 ⟨3,4,c,8,e,f⟩=4 ∨ q2 ⟨3,4,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 16*c-24*f+(272)
    let y : ℤ := 71*f-24*c+(692)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+188*x*y+16*y^2-(161920)*x-(66880)*y+(41395200)=0 := by
      dsimp [x,y]
      linear_combination 44800*h1 - 2800*(4*c-4*e+29*f+(4))*hq
    have hb := conic_box 71 188 16 (161920) (66880) (41395200) 1988 3425 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 16*c-24*f+(208)
    let y : ℤ := 71*f-24*c+(668)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+188*x*y+16*y^2-(161920)*x-(66880)*y+(41395200)=0 := by
      dsimp [x,y]
      linear_combination 44800*h1 - 2800*(4*c-4*e+29*f+(-4))*hq
    have hb := conic_box 71 188 16 (161920) (66880) (41395200) 1988 3425 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨3,5,c,8,e,f⟩)
    (hm : 0 ≤ 19*c-8*e+55)
    (hi : 0 ≤ 19*f-3*e+160) : c ≤ 225 ∧ f ≤ 111 := by
  have hq : q2 ⟨3,5,c,8,e,f⟩=4 ∨ q2 ⟨3,5,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-24*f+(307)
    let y : ℤ := 86*f-24*c+(812)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 86*x^2+466*x*y+31*y^2-(420100)*x-(177750)*y+(122762850)=0 := by
      dsimp [x,y]
      linear_combination 198550*h1 - 7942*(7*c-5*e+37*f+(4))*hq
    have hb := conic_box 86 466 31 (420100) (177750) (122762850) 4573 4931 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-24*f+(243)
    let y : ℤ := 86*f-24*c+(788)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 86*x^2+466*x*y+31*y^2-(420100)*x-(177750)*y+(122762850)=0 := by
      dsimp [x,y]
      linear_combination 198550*h1 - 7942*(7*c-5*e+37*f+(-4))*hq
    have hb := conic_box 86 466 31 (420100) (177750) (122762850) 4573 4931 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨3,6,c,8,e,f⟩)
    (hm : 0 ≤ 18*c-8*e+50)
    (hi : 0 ≤ 18*f-3*e+150) : c ≤ 191 ∧ f ≤ 93 := by
  have hq : q2 ⟨3,6,c,8,e,f⟩=4 ∨ q2 ⟨3,6,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 44*c-24*f+(332)
    let y : ℤ := 99*f-24*c+(912)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+678*x*y+44*y^2-(669600)*x-(282600)*y+(209869056)=0 := by
      dsimp [x,y]
      linear_combination 408240*h1 - 11340*(10*c-6*e+45*f+(4))*hq
    have hb := conic_box 99 678 44 (669600) (282600) (209869056) 6435 5566 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 44*c-24*f+(268)
    let y : ℤ := 99*f-24*c+(888)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+678*x*y+44*y^2-(669600)*x-(282600)*y+(209869056)=0 := by
      dsimp [x,y]
      linear_combination 408240*h1 - 11340*(10*c-6*e+45*f+(-4))*hq
    have hb := conic_box 99 678 44 (669600) (282600) (209869056) 6435 5566 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨3,7,c,8,e,f⟩)
    (hm : 0 ≤ 17*c-8*e+45)
    (hi : 0 ≤ 17*f-3*e+140) : c ≤ 170 ∧ f ≤ 81 := by
  have hq : q2 ⟨3,7,c,8,e,f⟩=4 ∨ q2 ⟨3,7,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 55*c-24*f+(347)
    let y : ℤ := 110*f-24*c+(992)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 110*x^2+830*x*y+55*y^2-(882700)*x-(369250)*y+(284555250)=0 := by
      dsimp [x,y]
      linear_combination 651406*h1 - 13294*(13*c-7*e+53*f+(4))*hq
    have hb := conic_box 110 830 55 (882700) (369250) (284555250) 7689 5826 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 55*c-24*f+(283)
    let y : ℤ := 110*f-24*c+(968)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 110*x^2+830*x*y+55*y^2-(882700)*x-(369250)*y+(284555250)=0 := by
      dsimp [x,y]
      linear_combination 651406*h1 - 13294*(13*c-7*e+53*f+(-4))*hq
    have hb := conic_box 110 830 55 (882700) (369250) (284555250) 7689 5826 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨3,8,c,8,e,f⟩)
    (hm : 0 ≤ 16*c-8*e+40)
    (hi : 0 ≤ 16*f-3*e+130) : c ≤ 153 ∧ f ≤ 71 := by
  have hq : q2 ⟨3,8,c,8,e,f⟩=4 ∨ q2 ⟨3,8,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 64*c-24*f+(352)
    let y : ℤ := 119*f-24*c+(1052)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 119*x^2+928*x*y+64*y^2-(1041280)*x-(430080)*y+(333213696)=0 := by
      dsimp [x,y]
      linear_combination 901120*h1 - 14080*(16*c-8*e+61*f+(4))*hq
    have hb := conic_box 119 928 64 (1041280) (430080) (333213696) 8418 5827 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 64*c-24*f+(288)
    let y : ℤ := 119*f-24*c+(1028)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 119*x^2+928*x*y+64*y^2-(1041280)*x-(430080)*y+(333213696)=0 := by
      dsimp [x,y]
      linear_combination 901120*h1 - 14080*(16*c-8*e+61*f+(-4))*hq
    have hb := conic_box 119 928 64 (1041280) (430080) (333213696) 8418 5827 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨3,9,c,8,e,f⟩)
    (hm : 0 ≤ 15*c-8*e+35)
    (hi : 0 ≤ 15*f-3*e+120) : c ≤ 139 ∧ f ≤ 62 := by
  have hq : q2 ⟨3,9,c,8,e,f⟩=4 ∨ q2 ⟨3,9,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 71*c-24*f+(347)
    let y : ℤ := 126*f-24*c+(1092)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 126*x^2+978*x*y+71*y^2-(1135620)*x-(461430)*y+(348644250)=0 := by
      dsimp [x,y]
      linear_combination 1129950*h1 - 13950*(19*c-9*e+69*f+(4))*hq
    have hb := conic_box 126 978 71 (1135620) (461430) (348644250) 8695 5627 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 71*c-24*f+(283)
    let y : ℤ := 126*f-24*c+(1068)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 126*x^2+978*x*y+71*y^2-(1135620)*x-(461430)*y+(348644250)=0 := by
      dsimp [x,y]
      linear_combination 1129950*h1 - 13950*(19*c-9*e+69*f+(-4))*hq
    have hb := conic_box 126 978 71 (1135620) (461430) (348644250) 8695 5627 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨3,10,c,8,e,f⟩)
    (hm : 0 ≤ 14*c-8*e+30)
    (hi : 0 ≤ 14*f-3*e+110) : c ≤ 126 ∧ f ≤ 55 := by
  have hq : q2 ⟨3,10,c,8,e,f⟩=4 ∨ q2 ⟨3,10,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 76*c-24*f+(332)
    let y : ℤ := 131*f-24*c+(1112)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 131*x^2+986*x*y+76*y^2-(1163200)*x-(463000)*y+(330326400)=0 := by
      dsimp [x,y]
      linear_combination 1313200*h1 - 13132*(22*c-10*e+77*f+(4))*hq
    have hb := conic_box 131 986 76 (1163200) (463000) (330326400) 8586 5267 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 76*c-24*f+(268)
    let y : ℤ := 131*f-24*c+(1088)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 131*x^2+986*x*y+76*y^2-(1163200)*x-(463000)*y+(330326400)=0 := by
      dsimp [x,y]
      linear_combination 1313200*h1 - 13132*(22*c-10*e+77*f+(-4))*hq
    have hb := conic_box 131 986 76 (1163200) (463000) (330326400) 8586 5267 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨3,11,c,8,e,f⟩)
    (hm : 0 ≤ 13*c-8*e+25)
    (hi : 0 ≤ 13*f-3*e+100) : c ≤ 114 ∧ f ≤ 48 := by
  have hq : q2 ⟨3,11,c,8,e,f⟩=4 ∨ q2 ⟨3,11,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 79*c-24*f+(307)
    let y : ℤ := 134*f-24*c+(1112)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 134*x^2+958*x*y+79*y^2-(1127500)*x-(437250)*y+(283540026)=0 := by
      dsimp [x,y]
      linear_combination 1431430*h1 - 11830*(25*c-11*e+85*f+(4))*hq
    have hb := conic_box 134 958 79 (1127500) (437250) (283540026) 8155 4785 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 79*c-24*f+(243)
    let y : ℤ := 134*f-24*c+(1088)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 134*x^2+958*x*y+79*y^2-(1127500)*x-(437250)*y+(283540026)=0 := by
      dsimp [x,y]
      linear_combination 1431430*h1 - 11830*(25*c-11*e+85*f+(-4))*hq
    have hb := conic_box 134 958 79 (1127500) (437250) (283540026) 8155 4785 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨3,12,c,8,e,f⟩)
    (hm : 0 ≤ 12*c-8*e+20)
    (hi : 0 ≤ 12*f-3*e+90) : c ≤ 103 ∧ f ≤ 41 := by
  have hq : q2 ⟨3,12,c,8,e,f⟩=4 ∨ q2 ⟨3,12,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 80*c-24*f+(272)
    let y : ℤ := 135*f-24*c+(1092)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 135*x^2+900*x*y+80*y^2-(1036800)*x-(388800)*y+(217728000)=0 := by
      dsimp [x,y]
      linear_combination 1472256*h1 - 10224*(28*c-12*e+93*f+(4))*hq
    have hb := conic_box 135 900 80 (1036800) (388800) (217728000) 7464 4215 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 80*c-24*f+(208)
    let y : ℤ := 135*f-24*c+(1068)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 135*x^2+900*x*y+80*y^2-(1036800)*x-(388800)*y+(217728000)=0 := by
      dsimp [x,y]
      linear_combination 1472256*h1 - 10224*(28*c-12*e+93*f+(-4))*hq
    have hb := conic_box 135 900 80 (1036800) (388800) (217728000) 7464 4215 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨3,13,c,8,e,f⟩)
    (hm : 0 ≤ 11*c-8*e+15)
    (hi : 0 ≤ 11*f-3*e+80) : c ≤ 91 ∧ f ≤ 35 := by
  have hq : q2 ⟨3,13,c,8,e,f⟩=4 ∨ q2 ⟨3,13,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 79*c-24*f+(227)
    let y : ℤ := 134*f-24*c+(1052)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 134*x^2+818*x*y+79*y^2-(902980)*x-(323830)*y+(144453426)=0 := by
      dsimp [x,y]
      linear_combination 1431430*h1 - 8470*(31*c-13*e+101*f+(4))*hq
    have hb := conic_box 134 818 79 (902980) (323830) (144453426) 6575 3590 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 79*c-24*f+(163)
    let y : ℤ := 134*f-24*c+(1028)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 134*x^2+818*x*y+79*y^2-(902980)*x-(323830)*y+(144453426)=0 := by
      dsimp [x,y]
      linear_combination 1431430*h1 - 8470*(31*c-13*e+101*f+(-4))*hq
    have hb := conic_box 134 818 79 (902980) (323830) (144453426) 6575 3590 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_14 (c e f : ℤ) (hz : isSolution ⟨3,14,c,8,e,f⟩)
    (hm : 0 ≤ 10*c-8*e+10)
    (hi : 0 ≤ 10*f-3*e+70) : c ≤ 81 ∧ f ≤ 29 := by
  have hq : q2 ⟨3,14,c,8,e,f⟩=4 ∨ q2 ⟨3,14,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 76*c-24*f+(172)
    let y : ℤ := 131*f-24*c+(992)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 131*x^2+718*x*y+76*y^2-(740320)*x-(249480)*y+(75264000)=0 := by
      dsimp [x,y]
      linear_combination 1313200*h1 - 6700*(34*c-14*e+109*f+(4))*hq
    have hb := conic_box 131 718 76 (740320) (249480) (75264000) 5548 2947 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 76*c-24*f+(108)
    let y : ℤ := 131*f-24*c+(968)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 131*x^2+718*x*y+76*y^2-(740320)*x-(249480)*y+(75264000)=0 := by
      dsimp [x,y]
      linear_combination 1313200*h1 - 6700*(34*c-14*e+109*f+(-4))*hq
    have hb := conic_box 131 718 76 (740320) (249480) (75264000) 5548 2947 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_15 (c e f : ℤ) (hz : isSolution ⟨3,15,c,8,e,f⟩)
    (hm : 0 ≤ 9*c-8*e+5)
    (hi : 0 ≤ 9*f-3*e+60) : c ≤ 70 ∧ f ≤ 24 := by
  have hq : q2 ⟨3,15,c,8,e,f⟩=4 ∨ q2 ⟨3,15,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 71*c-24*f+(107)
    let y : ℤ := 126*f-24*c+(912)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 126*x^2+606*x*y+71*y^2-(564300)*x-(173250)*y+(19735650)=0 := by
      dsimp [x,y]
      linear_combination 1129950*h1 - 5022*(37*c-15*e+117*f+(4))*hq
    have hb := conic_box 126 606 71 (564300) (173250) (19735650) 4444 2321 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 71*c-24*f+(43)
    let y : ℤ := 126*f-24*c+(888)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 126*x^2+606*x*y+71*y^2-(564300)*x-(173250)*y+(19735650)=0 := by
      dsimp [x,y]
      linear_combination 1129950*h1 - 5022*(37*c-15*e+117*f+(-4))*hq
    have hb := conic_box 126 606 71 (564300) (173250) (19735650) 4444 2321 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_16 (c e f : ℤ) (hz : isSolution ⟨3,16,c,8,e,f⟩)
    (hm : 0 ≤ 8*c-8*e+0)
    (hi : 0 ≤ 8*f-3*e+50) : c ≤ 59 ∧ f ≤ 20 := by
  have hq : q2 ⟨3,16,c,8,e,f⟩=4 ∨ q2 ⟨3,16,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 64*c-24*f+(32)
    let y : ℤ := 119*f-24*c+(812)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 119*x^2+488*x*y+64*y^2-(390400)*x-(102400)*y+(-16072704)=0 := by
      dsimp [x,y]
      linear_combination 901120*h1 - 3520*(40*c-16*e+125*f+(4))*hq
    have hb := conic_box 119 488 64 (390400) (102400) (-16072704) 3322 1745 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 64*c-24*f+(-32)
    let y : ℤ := 119*f-24*c+(788)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 119*x^2+488*x*y+64*y^2-(390400)*x-(102400)*y+(-16072704)=0 := by
      dsimp [x,y]
      linear_combination 901120*h1 - 3520*(40*c-16*e+125*f+(-4))*hq
    have hb := conic_box 119 488 64 (390400) (102400) (-16072704) 3322 1745 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_17 (c e f : ℤ) (hz : isSolution ⟨3,17,c,8,e,f⟩)
    (hm : 0 ≤ 7*c-8*e+-5)
    (hi : 0 ≤ 7*f-3*e+40) : c ≤ 49 ∧ f ≤ 16 := by
  have hq : q2 ⟨3,17,c,8,e,f⟩=4 ∨ q2 ⟨3,17,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 55*c-24*f+(-53)
    let y : ℤ := 110*f-24*c+(692)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 110*x^2+370*x*y+55*y^2-(232900)*x-(43350)*y+(-30561750)=0 := by
      dsimp [x,y]
      linear_combination 651406*h1 - 2254*(43*c-17*e+133*f+(4))*hq
    have hb := conic_box 110 370 55 (232900) (43350) (-30561750) 2242 1238 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 55*c-24*f+(-117)
    let y : ℤ := 110*f-24*c+(668)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 110*x^2+370*x*y+55*y^2-(232900)*x-(43350)*y+(-30561750)=0 := by
      dsimp [x,y]
      linear_combination 651406*h1 - 2254*(43*c-17*e+133*f+(-4))*hq
    have hb := conic_box 110 370 55 (232900) (43350) (-30561750) 2242 1238 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_18 (c e f : ℤ) (hz : isSolution ⟨3,18,c,8,e,f⟩)
    (hm : 0 ≤ 6*c-8*e+-10)
    (hi : 0 ≤ 6*f-3*e+30) : c ≤ 40 ∧ f ≤ 12 := by
  have hq : q2 ⟨3,18,c,8,e,f⟩=4 ∨ q2 ⟨3,18,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 44*c-24*f+(-148)
    let y : ℤ := 99*f-24*c+(552)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+258*x*y+44*y^2-(103680)*x-(1080)*y+(-26780544)=0 := by
      dsimp [x,y]
      linear_combination 408240*h1 - 1260*(46*c-18*e+141*f+(4))*hq
    have hb := conic_box 99 258 44 (103680) (1080) (-26780544) 1262 793 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 44*c-24*f+(-212)
    let y : ℤ := 99*f-24*c+(528)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+258*x*y+44*y^2-(103680)*x-(1080)*y+(-26780544)=0 := by
      dsimp [x,y]
      linear_combination 408240*h1 - 1260*(46*c-18*e+141*f+(-4))*hq
    have hb := conic_box 99 258 44 (103680) (1080) (-26780544) 1262 793 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_19 (c e f : ℤ) (hz : isSolution ⟨3,19,c,8,e,f⟩)
    (hm : 0 ≤ 5*c-8*e+-15)
    (hi : 0 ≤ 5*f-3*e+20) : c ≤ 31 ∧ f ≤ 8 := by
  have hq : q2 ⟨3,19,c,8,e,f⟩=4 ∨ q2 ⟨3,19,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-24*f+(-253)
    let y : ℤ := 86*f-24*c+(392)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 86*x^2+158*x*y+31*y^2-(11020)*x-(-21470)*y+(-11750550)=0 := by
      dsimp [x,y]
      linear_combination 198550*h1 - 550*(49*c-19*e+149*f+(4))*hq
    have hb := conic_box 86 158 31 (11020) (-21470) (-11750550) 440 361 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-24*f+(-317)
    let y : ℤ := 86*f-24*c+(368)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 86*x^2+158*x*y+31*y^2-(11020)*x-(-21470)*y+(-11750550)=0 := by
      dsimp [x,y]
      linear_combination 198550*h1 - 550*(49*c-19*e+149*f+(-4))*hq
    have hb := conic_box 86 158 31 (11020) (-21470) (-11750550) 440 361 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_20 (c e f : ℤ) (hz : isSolution ⟨3,20,c,8,e,f⟩)
    (hm : 0 ≤ 4*c-8*e+-20)
    (hi : 0 ≤ 4*f-3*e+10) : c ≤ 46 ∧ f ≤ 13 := by
  have hq : q2 ⟨3,20,c,8,e,f⟩=4 ∨ q2 ⟨3,20,c,8,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 16*c-24*f+(-368)
    let y : ℤ := 71*f-24*c+(212)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+76*x*y+16*y^2-(-41600)*x-(-24000)*y+(5145600)=0 := by
      dsimp [x,y]
      linear_combination 44800*h1 - 112*(52*c-20*e+157*f+(4))*hq
    have hb := conic_box 71 76 16 (-41600) (-24000) (5145600) 1 1 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 16*c-24*f+(-432)
    let y : ℤ := 71*f-24*c+(188)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+76*x*y+16*y^2-(-41600)*x-(-24000)*y+(5145600)=0 := by
      dsimp [x,y]
      linear_combination 44800*h1 - 112*(52*c-20*e+157*f+(-4))*hq
    have hb := conic_box 71 76 16 (-41600) (-24000) (5145600) 1 1 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

def cBound : ℕ → ℕ
  | 4 => 343
  | 5 => 225
  | 6 => 191
  | 7 => 170
  | 8 => 153
  | 9 => 139
  | 10 => 126
  | 11 => 114
  | 12 => 103
  | 13 => 91
  | 14 => 81
  | 15 => 70
  | 16 => 59
  | 17 => 49
  | 18 => 40
  | 19 => 31
  | 20 => 46
  | _ => 0

def fBound : ℕ → ℕ
  | 4 => 154
  | 5 => 111
  | 6 => 93
  | 7 => 81
  | 8 => 71
  | 9 => 62
  | 10 => 55
  | 11 => 48
  | 12 => 41
  | 13 => 35
  | 14 => 29
  | 15 => 24
  | 16 => 20
  | 17 => 16
  | 18 => 12
  | 19 => 8
  | 20 => 13
  | _ => 0

private theorem fixed_bounds (b c e f : ℤ) (hb : 4 ≤ b) (hb' : b ≤ 20)
    (hz : isSolution ⟨3,b,c,8,e,f⟩)
    (hm : 0 ≤ (24-b)*c-8*e+80-5*b)
    (hi : 0 ≤ (24-b)*f-3*e+210-10*b) :
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
  · simpa only [cBound,fBound] using bounds_15 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_16 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_17 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_18 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_19 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa only [cBound,fBound] using bounds_20 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

/-- A universal coordinate box derived from genuine two-step terminality. -/
theorem a_three_d_eight_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=8)
    (ht : ShortTerminal z 2) :
    4 ≤ z.b ∧ z.b ≤ 20 ∧ z.c ≤ (cBound z.b.toNat : ℤ) ∧ z.f ≤ (fBound z.b.toNat : ℤ) := by
  have hb : 4 ≤ z.b := (a_three_incident_bounds z hz ha).1
  have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
  have hInv : 4 ≤ (inv1 z).d := (a_three_incident_bounds (inv1 z) hw ha).2.2.1
  simp only [inv1,ha,hd] at hInv
  have hb' : z.b ≤ 20 := by omega
  have hp := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hM := hp [.m2,.m1] (by decide +kernel)
  have hI := hp [.i1,.i2] (by decide +kernel)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2] at hM
  dsimp [heightPolynomial,coordinateSum,applyWord,step,inv1,inv2] at hI
  rw [ha,hd] at hM hI
  have hm : 0 ≤ (24-z.b)*z.c-8*z.e+80-5*z.b := by nlinarith only [hM]
  have hi : 0 ≤ (24-z.b)*z.f-3*z.e+210-10*z.b := by nlinarith only [hI]
  have heq : z=⟨3,z.b,z.c,8,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hb',fixed_bounds z.b z.c z.e z.f hb hb' (heq ▸ hz.1) hm hi⟩

end SerreMarkov.PositiveThreeEight
