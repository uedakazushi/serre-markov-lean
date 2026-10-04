import SerreMarkov.PositiveThreeFourBounds
import SerreMarkov.PositiveShortWord

/-! Universal finite conic bounds for the actual slice a=3,d=7.
The two slacks are the actual words [m2,m1] and [i1,i2]. -/
namespace SerreMarkov.PositiveThreeSeven
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

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨3,4,c,7,e,f⟩)
    (hm : 0 ≤ 17*c-7*e+50)
    (hi : 0 ≤ 17*f-3*e+126) : c ≤ 224 ∧ f ≤ 117 := by
  have hq : q2 ⟨3,4,c,7,e,f⟩=4 ∨ q2 ⟨3,4,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 19*c-21*f+(228)
    let y : ℤ := 59*f-21*c+(516)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 59*x^2+212*x*y+19*y^2-(130448)*x-(61552)*y+(27649600)=0 := by
      dsimp [x,y]
      linear_combination 46240*h1 - 2890*(5*c-4*e+25*f+(4))*hq
    have hb := conic_box 59 212 19 (130448) (61552) (27649600) 1974 2701 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 19*c-21*f+(172)
    let y : ℤ := 59*f-21*c+(492)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 59*x^2+212*x*y+19*y^2-(130448)*x-(61552)*y+(27649600)=0 := by
      dsimp [x,y]
      linear_combination 46240*h1 - 2890*(5*c-4*e+25*f+(-4))*hq
    have hb := conic_box 59 212 19 (130448) (61552) (27649600) 1974 2701 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨3,5,c,7,e,f⟩)
    (hm : 0 ≤ 16*c-7*e+45)
    (hi : 0 ≤ 16*f-3*e+117) : c ≤ 165 ∧ f ≤ 89 := by
  have hq : q2 ⟨3,5,c,7,e,f⟩=4 ∨ q2 ⟨3,5,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-21*f+(253)
    let y : ℤ := 71*f-21*c+(597)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+394*x*y+31*y^2-(262440)*x-(124920)*y+(61737200)=0 := by
      dsimp [x,y]
      linear_combination 140800*h1 - 5632*(8*c-5*e+32*f+(4))*hq
    have hb := conic_box 71 394 31 (262440) (124920) (61737200) 3444 3453 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-21*f+(197)
    let y : ℤ := 71*f-21*c+(573)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+394*x*y+31*y^2-(262440)*x-(124920)*y+(61737200)=0 := by
      dsimp [x,y]
      linear_combination 140800*h1 - 5632*(8*c-5*e+32*f+(-4))*hq
    have hb := conic_box 71 394 31 (262440) (124920) (61737200) 3444 3453 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨3,6,c,7,e,f⟩)
    (hm : 0 ≤ 15*c-7*e+40)
    (hi : 0 ≤ 15*f-3*e+108) : c ≤ 140 ∧ f ≤ 74 := by
  have hq : q2 ⟨3,6,c,7,e,f⟩=4 ∨ q2 ⟨3,6,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 41*c-21*f+(268)
    let y : ℤ := 81*f-21*c+(660)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 81*x^2+522*x*y+41*y^2-(377136)*x-(178416)*y+(92565504)=0 := by
      dsimp [x,y]
      linear_combination 259200*h1 - 7200*(11*c-6*e+39*f+(4))*hq
    have hb := conic_box 81 522 41 (377136) (178416) (92565504) 4397 3750 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 41*c-21*f+(212)
    let y : ℤ := 81*f-21*c+(636)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 81*x^2+522*x*y+41*y^2-(377136)*x-(178416)*y+(92565504)=0 := by
      dsimp [x,y]
      linear_combination 259200*h1 - 7200*(11*c-6*e+39*f+(-4))*hq
    have hb := conic_box 81 522 41 (377136) (178416) (92565504) 4397 3750 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨3,7,c,7,e,f⟩)
    (hm : 0 ≤ 14*c-7*e+35)
    (hi : 0 ≤ 14*f-3*e+99) : c ≤ 123 ∧ f ≤ 64 := by
  have hq : q2 ⟨3,7,c,7,e,f⟩=4 ∨ q2 ⟨3,7,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 49*c-21*f+(273)
    let y : ℤ := 89*f-21*c+(705)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 89*x^2+602*x*y+49*y^2-(460796)*x-(215404)*y+(112491652)=0 := by
      dsimp [x,y]
      linear_combination 384160*h1 - 7840*(14*c-7*e+46*f+(4))*hq
    have hb := conic_box 89 602 49 (460796) (215404) (112491652) 4921 3791 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 49*c-21*f+(217)
    let y : ℤ := 89*f-21*c+(681)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 89*x^2+602*x*y+49*y^2-(460796)*x-(215404)*y+(112491652)=0 := by
      dsimp [x,y]
      linear_combination 384160*h1 - 7840*(14*c-7*e+46*f+(-4))*hq
    have hb := conic_box 89 602 49 (460796) (215404) (112491652) 4921 3791 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨3,8,c,7,e,f⟩)
    (hm : 0 ≤ 13*c-7*e+30)
    (hi : 0 ≤ 13*f-3*e+90) : c ≤ 109 ∧ f ≤ 55 := by
  have hq : q2 ⟨3,8,c,7,e,f⟩=4 ∨ q2 ⟨3,8,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 55*c-21*f+(268)
    let y : ℤ := 95*f-21*c+(732)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 95*x^2+640*x*y+55*y^2-(506400)*x-(232800)*y+(117536000)=0 := by
      dsimp [x,y]
      linear_combination 497536*h1 - 7774*(17*c-8*e+53*f+(4))*hq
    have hb := conic_box 95 640 55 (506400) (232800) (117536000) 5088 3647 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 55*c-21*f+(212)
    let y : ℤ := 95*f-21*c+(708)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 95*x^2+640*x*y+55*y^2-(506400)*x-(232800)*y+(117536000)=0 := by
      dsimp [x,y]
      linear_combination 497536*h1 - 7774*(17*c-8*e+53*f+(-4))*hq
    have hb := conic_box 95 640 55 (506400) (232800) (117536000) 5088 3647 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨3,9,c,7,e,f⟩)
    (hm : 0 ≤ 12*c-7*e+25)
    (hi : 0 ≤ 12*f-3*e+81) : c ≤ 97 ∧ f ≤ 47 := by
  have hq : q2 ⟨3,9,c,7,e,f⟩=4 ∨ q2 ⟨3,9,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 59*c-21*f+(253)
    let y : ℤ := 99*f-21*c+(741)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+642*x*y+59*y^2-(512568)*x-(230472)*y+(107658720)=0 := by
      dsimp [x,y]
      linear_combination 583200*h1 - 7200*(20*c-9*e+60*f+(4))*hq
    have hb := conic_box 99 642 59 (512568) (230472) (107658720) 4959 3364 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 59*c-21*f+(197)
    let y : ℤ := 99*f-21*c+(717)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+642*x*y+59*y^2-(512568)*x-(230472)*y+(107658720)=0 := by
      dsimp [x,y]
      linear_combination 583200*h1 - 7200*(20*c-9*e+60*f+(-4))*hq
    have hb := conic_box 99 642 59 (512568) (230472) (107658720) 4959 3364 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨3,10,c,7,e,f⟩)
    (hm : 0 ≤ 11*c-7*e+20)
    (hi : 0 ≤ 11*f-3*e+72) : c ≤ 86 ∧ f ≤ 40 := by
  have hq : q2 ⟨3,10,c,7,e,f⟩=4 ∨ q2 ⟨3,10,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 61*c-21*f+(228)
    let y : ℤ := 101*f-21*c+(732)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 101*x^2+614*x*y+61*y^2-(482480)*x-(210640)*y+(86132800)=0 := by
      dsimp [x,y]
      linear_combination 629200*h1 - 6292*(23*c-10*e+67*f+(4))*hq
    have hb := conic_box 101 614 61 (482480) (210640) (86132800) 4592 2980 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 61*c-21*f+(172)
    let y : ℤ := 101*f-21*c+(708)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 101*x^2+614*x*y+61*y^2-(482480)*x-(210640)*y+(86132800)=0 := by
      dsimp [x,y]
      linear_combination 629200*h1 - 6292*(23*c-10*e+67*f+(-4))*hq
    have hb := conic_box 101 614 61 (482480) (210640) (86132800) 4592 2980 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨3,11,c,7,e,f⟩)
    (hm : 0 ≤ 10*c-7*e+15)
    (hi : 0 ≤ 10*f-3*e+63) : c ≤ 75 ∧ f ≤ 34 := by
  have hq : q2 ⟨3,11,c,7,e,f⟩=4 ∨ q2 ⟨3,11,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 61*c-21*f+(193)
    let y : ℤ := 101*f-21*c+(705)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 101*x^2+562*x*y+61*y^2-(422796)*x-(177276)*y+(58361204)=0 := by
      dsimp [x,y]
      linear_combination 629200*h1 - 5200*(26*c-11*e+74*f+(4))*hq
    have hb := conic_box 101 562 61 (422796) (177276) (58361204) 4044 2528 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 61*c-21*f+(137)
    let y : ℤ := 101*f-21*c+(681)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 101*x^2+562*x*y+61*y^2-(422796)*x-(177276)*y+(58361204)=0 := by
      dsimp [x,y]
      linear_combination 629200*h1 - 5200*(26*c-11*e+74*f+(-4))*hq
    have hb := conic_box 101 562 61 (422796) (177276) (58361204) 4044 2528 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨3,12,c,7,e,f⟩)
    (hm : 0 ≤ 9*c-7*e+10)
    (hi : 0 ≤ 9*f-3*e+54) : c ≤ 65 ∧ f ≤ 28 := by
  have hq : q2 ⟨3,12,c,7,e,f⟩=4 ∨ q2 ⟨3,12,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 59*c-21*f+(148)
    let y : ℤ := 99*f-21*c+(660)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+492*x*y+59*y^2-(342576)*x-(135504)*y+(30445632)=0 := by
      dsimp [x,y]
      linear_combination 583200*h1 - 4050*(29*c-12*e+81*f+(4))*hq
    have hb := conic_box 99 492 59 (342576) (135504) (30445632) 3370 2045 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 59*c-21*f+(92)
    let y : ℤ := 99*f-21*c+(636)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 99*x^2+492*x*y+59*y^2-(342576)*x-(135504)*y+(30445632)=0 := by
      dsimp [x,y]
      linear_combination 583200*h1 - 4050*(29*c-12*e+81*f+(-4))*hq
    have hb := conic_box 99 492 59 (342576) (135504) (30445632) 3370 2045 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨3,13,c,7,e,f⟩)
    (hm : 0 ≤ 8*c-7*e+5)
    (hi : 0 ≤ 8*f-3*e+45) : c ≤ 55 ∧ f ≤ 22 := by
  have hq : q2 ⟨3,13,c,7,e,f⟩=4 ∨ q2 ⟨3,13,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 55*c-21*f+(93)
    let y : ℤ := 95*f-21*c+(597)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 95*x^2+410*x*y+55*y^2-(252200)*x-(91000)*y+(7774000)=0 := by
      dsimp [x,y]
      linear_combination 497536*h1 - 2944*(32*c-13*e+88*f+(4))*hq
    have hb := conic_box 95 410 55 (252200) (91000) (7774000) 2624 1565 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 55*c-21*f+(37)
    let y : ℤ := 95*f-21*c+(573)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 95*x^2+410*x*y+55*y^2-(252200)*x-(91000)*y+(7774000)=0 := by
      dsimp [x,y]
      linear_combination 497536*h1 - 2944*(32*c-13*e+88*f+(-4))*hq
    have hb := conic_box 95 410 55 (252200) (91000) (7774000) 2624 1565 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_14 (c e f : ℤ) (hz : isSolution ⟨3,14,c,7,e,f⟩)
    (hm : 0 ≤ 7*c-7*e+0)
    (hi : 0 ≤ 7*f-3*e+36) : c ≤ 46 ∧ f ≤ 17 := by
  have hq : q2 ⟨3,14,c,7,e,f⟩=4 ∨ q2 ⟨3,14,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 49*c-21*f+(28)
    let y : ℤ := 89*f-21*c+(516)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 89*x^2+322*x*y+49*y^2-(162288)*x-(49392)*y+(-6146560)=0 := by
      dsimp [x,y]
      linear_combination 384160*h1 - 1960*(35*c-14*e+95*f+(4))*hq
    have hb := conic_box 89 322 49 (162288) (49392) (-6146560) 1861 1121 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 49*c-21*f+(-28)
    let y : ℤ := 89*f-21*c+(492)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 89*x^2+322*x*y+49*y^2-(162288)*x-(49392)*y+(-6146560)=0 := by
      dsimp [x,y]
      linear_combination 384160*h1 - 1960*(35*c-14*e+95*f+(-4))*hq
    have hb := conic_box 89 322 49 (162288) (49392) (-6146560) 1861 1121 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_15 (c e f : ℤ) (hz : isSolution ⟨3,15,c,7,e,f⟩)
    (hm : 0 ≤ 6*c-7*e+-5)
    (hi : 0 ≤ 6*f-3*e+27) : c ≤ 37 ∧ f ≤ 13 := by
  have hq : q2 ⟨3,15,c,7,e,f⟩=4 ∨ q2 ⟨3,15,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 41*c-21*f+(-47)
    let y : ℤ := 81*f-21*c+(417)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 81*x^2+234*x*y+41*y^2-(82620)*x-(15660)*y+(-10424700)=0 := by
      dsimp [x,y]
      linear_combination 259200*h1 - 1152*(38*c-15*e+102*f+(4))*hq
    have hb := conic_box 81 234 41 (82620) (15660) (-10424700) 1134 731 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 41*c-21*f+(-103)
    let y : ℤ := 81*f-21*c+(393)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 81*x^2+234*x*y+41*y^2-(82620)*x-(15660)*y+(-10424700)=0 := by
      dsimp [x,y]
      linear_combination 259200*h1 - 1152*(38*c-15*e+102*f+(-4))*hq
    have hb := conic_box 81 234 41 (82620) (15660) (-10424700) 1134 731 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_16 (c e f : ℤ) (hz : isSolution ⟨3,16,c,7,e,f⟩)
    (hm : 0 ≤ 5*c-7*e+-10)
    (hi : 0 ≤ 5*f-3*e+18) : c ≤ 28 ∧ f ≤ 9 := by
  have hq : q2 ⟨3,16,c,7,e,f⟩=4 ∨ q2 ⟨3,16,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 31*c-21*f+(-132)
    let y : ℤ := 71*f-21*c+(300)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+152*x*y+31*y^2-(21056)*x-(-6464)*y+(-6941696)=0 := by
      dsimp [x,y]
      linear_combination 140800*h1 - 550*(41*c-16*e+109*f+(4))*hq
    have hb := conic_box 71 152 31 (21056) (-6464) (-6941696) 495 381 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 31*c-21*f+(-188)
    let y : ℤ := 71*f-21*c+(276)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 71*x^2+152*x*y+31*y^2-(21056)*x-(-6464)*y+(-6941696)=0 := by
      dsimp [x,y]
      linear_combination 140800*h1 - 550*(41*c-16*e+109*f+(-4))*hq
    have hb := conic_box 71 152 31 (21056) (-6464) (-6941696) 495 381 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_17 (c e f : ℤ) (hz : isSolution ⟨3,17,c,7,e,f⟩)
    (hm : 0 ≤ 4*c-7*e+-15)
    (hi : 0 ≤ 4*f-3*e+9) : c ≤ 20 ∧ f ≤ 4 := by
  have hq : q2 ⟨3,17,c,7,e,f⟩=4 ∨ q2 ⟨3,17,c,7,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
  · dsimp [q2] at hq
    let x : ℤ := 19*c-21*f+(-227)
    let y : ℤ := 59*f-21*c+(165)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 59*x^2+82*x*y+19*y^2-(-17544)*x-(-15096)*y+(175712)=0 := by
      dsimp [x,y]
      linear_combination 46240*h1 - 160*(44*c-17*e+116*f+(4))*hq
    have hb := conic_box 59 82 19 (-17544) (-15096) (175712) 1 1 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
  · dsimp [q2] at hq
    let x : ℤ := 19*c-21*f+(-283)
    let y : ℤ := 59*f-21*c+(141)
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : 59*x^2+82*x*y+19*y^2-(-17544)*x-(-15096)*y+(175712)=0 := by
      dsimp [x,y]
      linear_combination 46240*h1 - 160*(44*c-17*e+116*f+(-4))*hq
    have hb := conic_box 59 82 19 (-17544) (-15096) (175712) 1 1 x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

def cBound : ℕ → ℕ
  | 4 => 224
  | 5 => 165
  | 6 => 140
  | 7 => 123
  | 8 => 109
  | 9 => 97
  | 10 => 86
  | 11 => 75
  | 12 => 65
  | 13 => 55
  | 14 => 46
  | 15 => 37
  | 16 => 28
  | 17 => 20
  | _ => 0

def fBound : ℕ → ℕ
  | 4 => 117
  | 5 => 89
  | 6 => 74
  | 7 => 64
  | 8 => 55
  | 9 => 47
  | 10 => 40
  | 11 => 34
  | 12 => 28
  | 13 => 22
  | 14 => 17
  | 15 => 13
  | 16 => 9
  | 17 => 4
  | _ => 0

private theorem fixed_bounds (b c e f : ℤ) (hb : 4 ≤ b) (hb' : b ≤ 17)
    (hz : isSolution ⟨3,b,c,7,e,f⟩)
    (hm : 0 ≤ (21-b)*c-7*e+70-5*b)
    (hi : 0 ≤ (21-b)*f-3*e+162-9*b) :
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

/-- A universal coordinate box derived from genuine two-step terminality. -/
theorem a_three_d_seven_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=7)
    (ht : ShortTerminal z 2) :
    4 ≤ z.b ∧ z.b ≤ 17 ∧ z.c ≤ (cBound z.b.toNat : ℤ) ∧ z.f ≤ (fBound z.b.toNat : ℤ) := by
  have hb : 4 ≤ z.b := (a_three_incident_bounds z hz ha).1
  have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
  have hInv : 4 ≤ (inv1 z).d := (a_three_incident_bounds (inv1 z) hw ha).2.2.1
  simp only [inv1,ha,hd] at hInv
  have hb' : z.b ≤ 17 := by omega
  have hp := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hM := hp [.m2,.m1] (by decide +kernel)
  have hI := hp [.i1,.i2] (by decide +kernel)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2] at hM
  dsimp [heightPolynomial,coordinateSum,applyWord,step,inv1,inv2] at hI
  rw [ha,hd] at hM hI
  have hm : 0 ≤ (21-z.b)*z.c-7*z.e+70-5*z.b := by nlinarith only [hM]
  have hi : 0 ≤ (21-z.b)*z.f-3*z.e+162-9*z.b := by nlinarith only [hI]
  have heq : z=⟨3,z.b,z.c,7,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hb',fixed_bounds z.b z.c z.e z.f hb hb' (heq ▸ hz.1) hm hi⟩

end SerreMarkov.PositiveThreeSeven
