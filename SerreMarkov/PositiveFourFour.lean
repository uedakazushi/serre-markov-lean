import SerreMarkov.PositiveShortWord
import SerreMarkov.PositiveTriangleLower
import SerreMarkov.PositiveBoundedTable

/-! # The actual positive short-word terminal slice `a=d=4`

Two explicit two-letter no-drop comparisons give nonnegative linear slacks.
The solution equations become positive quadratic conics in these slacks.
The resulting finite bounds are proved without a height-bound hypothesis.
No universal small-adjacent-edge assertion is made here.
-/

namespace SerreMarkov.PositiveFourFour

open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 5000000

private theorem conic_sum_bound (p q K C M x y : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hp : 0<p) (hq : 2*p≤q)
    (heq : p*x^2+q*x*y+p*y^2-K*(x+y)+C=0)
    (hder : 0≤2*p*M-K) (hnum : 0<p*M^2-K*M+C) : x+y<M := by
  have hxy := mul_nonneg hx hy
  have hcross := mul_nonneg (show 0≤q-2*p by omega) hxy
  have hquad : p*(x+y)^2-K*(x+y)+C≤0 := by nlinarith only [heq,hcross]
  by_contra hn
  have hm : 0≤x+y-M := by omega
  have hpM := mul_nonneg hp.le hm
  have hlin : 0≤p*(x+y+M)-K := by nlinarith only [hder,hpM]
  have hprod := mul_nonneg hm hlin
  nlinarith only [hquad,hnum,hprod]

def sumBound (b : ℤ) : ℤ :=
  if b=3 then 102 else if b=4 then 73 else if b=5 then 59 else
  if b=6 then 49 else if b=7 then 40 else if b=8 then 32 else
  if b=9 then 26 else if b=10 then 20 else if b=11 then 15 else
  if b=12 then 12 else 0

private theorem bounds_3 (c e f : ℤ) (hz : isSolution ⟨4,3,c,4,e,f⟩)
    (hm : 0≤(13)*c-4*e+(54))
    (hi : 0≤(13)*f-4*e+(54)) : c+f≤102 := by
  have hq : q2 ⟨4,3,c,4,e,f⟩=4 ∨ q2 ⟨4,3,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,3,c,4,e,f⟩-4)*(q2 ⟨4,3,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 23*c-16*f+(178)
    let y : ℤ := 23*f-16*c+(178)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 23*x^2+123*x*y+23*y^2-(27378)*(x+y)+(4251195)=0 := by
      dsimp [x,y]
      linear_combination 10647*h1 - 1183*((8)*(c+f)-3*e+(4))*hq

    have hb := conic_sum_bound 23 123 (27378) (4251195) 1008 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 23*c-16*f+(146)
    let y : ℤ := 23*f-16*c+(146)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 23*x^2+123*x*y+23*y^2-(27378)*(x+y)+(4251195)=0 := by
      dsimp [x,y]
      linear_combination 10647*h1 - 1183*((8)*(c+f)-3*e+(-4))*hq

    have hb := conic_sum_bound 23 123 (27378) (4251195) 1008 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨4,4,c,4,e,f⟩)
    (hm : 0≤(12)*c-4*e+(48))
    (hi : 0≤(12)*f-4*e+(48)) : c+f≤73 := by
  have hq : q2 ⟨4,4,c,4,e,f⟩=4 ∨ q2 ⟨4,4,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,4,c,4,e,f⟩-4)*(q2 ⟨4,4,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 32*c-16*f+(208)
    let y : ℤ := 32*f-16*c+(208)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 1*x^2+7*x*y+1*y^2-(1728)*(x+y)+(302976)=0 := by
      dsimp [x,y]
      linear_combination 1152*h1 - 72*((12)*(c+f)-4*e+(4))*hq

    have hb := conic_sum_bound 1 7 (1728) (302976) 1531 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 32*c-16*f+(176)
    let y : ℤ := 32*f-16*c+(176)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 1*x^2+7*x*y+1*y^2-(1728)*(x+y)+(302976)=0 := by
      dsimp [x,y]
      linear_combination 1152*h1 - 72*((12)*(c+f)-4*e+(-4))*hq

    have hb := conic_sum_bound 1 7 (1728) (302976) 1531 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨4,5,c,4,e,f⟩)
    (hm : 0≤(11)*c-4*e+(42))
    (hi : 0≤(11)*f-4*e+(42)) : c+f≤59 := by
  have hq : q2 ⟨4,5,c,4,e,f⟩=4 ∨ q2 ⟨4,5,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,5,c,4,e,f⟩-4)*(q2 ⟨4,5,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 39*c-16*f+(226)
    let y : ℤ := 39*f-16*c+(226)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 39*x^2+285*x*y+39*y^2-(76230)*(x+y)+(13803075)=0 := by
      dsimp [x,y]
      linear_combination 69575*h1 - 2783*((16)*(c+f)-5*e+(4))*hq

    have hb := conic_sum_bound 39 285 (76230) (13803075) 1754 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 39*c-16*f+(194)
    let y : ℤ := 39*f-16*c+(194)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 39*x^2+285*x*y+39*y^2-(76230)*(x+y)+(13803075)=0 := by
      dsimp [x,y]
      linear_combination 69575*h1 - 2783*((16)*(c+f)-5*e+(-4))*hq

    have hb := conic_sum_bound 39 285 (76230) (13803075) 1754 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨4,6,c,4,e,f⟩)
    (hm : 0≤(10)*c-4*e+(36))
    (hi : 0≤(10)*f-4*e+(36)) : c+f≤49 := by
  have hq : q2 ⟨4,6,c,4,e,f⟩=4 ∨ q2 ⟨4,6,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,6,c,4,e,f⟩-4)*(q2 ⟨4,6,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 44*c-16*f+(232)
    let y : ℤ := 44*f-16*c+(232)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 11*x^2+78*x*y+11*y^2-(21600)*(x+y)+(3744000)=0 := by
      dsimp [x,y]
      linear_combination 25200*h1 - 700*((20)*(c+f)-6*e+(4))*hq

    have hb := conic_sum_bound 11 78 (21600) (3744000) 1773 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 44*c-16*f+(200)
    let y : ℤ := 44*f-16*c+(200)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 11*x^2+78*x*y+11*y^2-(21600)*(x+y)+(3744000)=0 := by
      dsimp [x,y]
      linear_combination 25200*h1 - 700*((20)*(c+f)-6*e+(-4))*hq

    have hb := conic_sum_bound 11 78 (21600) (3744000) 1773 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨4,7,c,4,e,f⟩)
    (hm : 0≤(9)*c-4*e+(30))
    (hi : 0≤(9)*f-4*e+(30)) : c+f≤40 := by
  have hq : q2 ⟨4,7,c,4,e,f⟩=4 ∨ q2 ⟨4,7,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,7,c,4,e,f⟩-4)*(q2 ⟨4,7,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 47*c-16*f+(226)
    let y : ℤ := 47*f-16*c+(226)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 47*x^2+311*x*y+47*y^2-(85050)*(x+y)+(12998475)=0 := by
      dsimp [x,y]
      linear_combination 123039*h1 - 2511*((24)*(c+f)-7*e+(4))*hq

    have hb := conic_sum_bound 47 311 (85050) (12998475) 1643 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 47*c-16*f+(194)
    let y : ℤ := 47*f-16*c+(194)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 47*x^2+311*x*y+47*y^2-(85050)*(x+y)+(12998475)=0 := by
      dsimp [x,y]
      linear_combination 123039*h1 - 2511*((24)*(c+f)-7*e+(-4))*hq

    have hb := conic_sum_bound 47 311 (85050) (12998475) 1643 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨4,8,c,4,e,f⟩)
    (hm : 0≤(8)*c-4*e+(24))
    (hi : 0≤(8)*f-4*e+(24)) : c+f≤32 := by
  have hq : q2 ⟨4,8,c,4,e,f⟩=4 ∨ q2 ⟨4,8,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,8,c,4,e,f⟩-4)*(q2 ⟨4,8,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 48*c-16*f+(208)
    let y : ℤ := 48*f-16*c+(208)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+18*x*y+3*y^2-(4608)*(x+y)+(552960)=0 := by
      dsimp [x,y]
      linear_combination 8192*h1 - 128*((28)*(c+f)-8*e+(4))*hq

    have hb := conic_sum_bound 3 18 (4608) (552960) 1406 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 48*c-16*f+(176)
    let y : ℤ := 48*f-16*c+(176)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+18*x*y+3*y^2-(4608)*(x+y)+(552960)=0 := by
      dsimp [x,y]
      linear_combination 8192*h1 - 128*((28)*(c+f)-8*e+(-4))*hq

    have hb := conic_sum_bound 3 18 (4608) (552960) 1406 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨4,9,c,4,e,f⟩)
    (hm : 0≤(7)*c-4*e+(18))
    (hi : 0≤(7)*f-4*e+(18)) : c+f≤26 := by
  have hq : q2 ⟨4,9,c,4,e,f⟩=4 ∨ q2 ⟨4,9,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,9,c,4,e,f⟩-4)*(q2 ⟨4,9,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 47*c-16*f+(178)
    let y : ℤ := 47*f-16*c+(178)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 47*x^2+249*x*y+47*y^2-(55566)*(x+y)+(4139667)=0 := by
      dsimp [x,y]
      linear_combination 123039*h1 - 1519*((32)*(c+f)-9*e+(4))*hq

    have hb := conic_sum_bound 47 249 (55566) (4139667) 1104 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 47*c-16*f+(146)
    let y : ℤ := 47*f-16*c+(146)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 47*x^2+249*x*y+47*y^2-(55566)*(x+y)+(4139667)=0 := by
      dsimp [x,y]
      linear_combination 123039*h1 - 1519*((32)*(c+f)-9*e+(-4))*hq

    have hb := conic_sum_bound 47 249 (55566) (4139667) 1104 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨4,10,c,4,e,f⟩)
    (hm : 0≤(6)*c-4*e+(12))
    (hi : 0≤(6)*f-4*e+(12)) : c+f≤20 := by
  have hq : q2 ⟨4,10,c,4,e,f⟩=4 ∨ q2 ⟨4,10,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,10,c,4,e,f⟩-4)*(q2 ⟨4,10,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 44*c-16*f+(136)
    let y : ℤ := 44*f-16*c+(136)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 11*x^2+50*x*y+11*y^2-(8640)*(x+y)+(115200)=0 := by
      dsimp [x,y]
      linear_combination 25200*h1 - 252*((36)*(c+f)-10*e+(4))*hq

    have hb := conic_sum_bound 11 50 (8640) (115200) 773 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 44*c-16*f+(104)
    let y : ℤ := 44*f-16*c+(104)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 11*x^2+50*x*y+11*y^2-(8640)*(x+y)+(115200)=0 := by
      dsimp [x,y]
      linear_combination 25200*h1 - 252*((36)*(c+f)-10*e+(-4))*hq

    have hb := conic_sum_bound 11 50 (8640) (115200) 773 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨4,11,c,4,e,f⟩)
    (hm : 0≤(5)*c-4*e+(6))
    (hi : 0≤(5)*f-4*e+(6)) : c+f≤15 := by
  have hq : q2 ⟨4,11,c,4,e,f⟩=4 ∨ q2 ⟨4,11,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,11,c,4,e,f⟩-4)*(q2 ⟨4,11,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 39*c-16*f+(82)
    let y : ℤ := 39*f-16*c+(82)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 39*x^2+147*x*y+39*y^2-(14850)*(x+y)+(-1225125)=0 := by
      dsimp [x,y]
      linear_combination 69575*h1 - 575*((40)*(c+f)-11*e+(4))*hq

    have hb := conic_sum_bound 39 147 (14850) (-1225125) 452 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 39*c-16*f+(50)
    let y : ℤ := 39*f-16*c+(50)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 39*x^2+147*x*y+39*y^2-(14850)*(x+y)+(-1225125)=0 := by
      dsimp [x,y]
      linear_combination 69575*h1 - 575*((40)*(c+f)-11*e+(-4))*hq

    have hb := conic_sum_bound 39 147 (14850) (-1225125) 452 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨4,12,c,4,e,f⟩)
    (hm : 0≤(4)*c-4*e+(0))
    (hi : 0≤(4)*f-4*e+(0)) : c+f≤12 := by
  have hq : q2 ⟨4,12,c,4,e,f⟩=4 ∨ q2 ⟨4,12,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,12,c,4,e,f⟩-4)*(q2 ⟨4,12,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 32*c-16*f+(16)
    let y : ℤ := 32*f-16*c+(16)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 1*x^2+3*x*y+1*y^2-(0)*(x+y)+(-28800)=0 := by
      dsimp [x,y]
      linear_combination 1152*h1 - 8*((44)*(c+f)-12*e+(4))*hq

    have hb := conic_sum_bound 1 3 (0) (-28800) 171 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 32*c-16*f+(-16)
    let y : ℤ := 32*f-16*c+(-16)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 1*x^2+3*x*y+1*y^2-(0)*(x+y)+(-28800)=0 := by
      dsimp [x,y]
      linear_combination 1152*h1 - 8*((44)*(c+f)-12*e+(-4))*hq

    have hb := conic_sum_bound 1 3 (0) (-28800) 171 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨4,13,c,4,e,f⟩)
    (hm : 0≤(3)*c-4*e+(-6))
    (hi : 0≤(3)*f-4*e+(-6)) : c+f≤0 := by
  have hq : q2 ⟨4,13,c,4,e,f⟩=4 ∨ q2 ⟨4,13,c,4,e,f⟩= -4 := by
    have h : (q2 ⟨4,13,c,4,e,f⟩-4)*(q2 ⟨4,13,c,4,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 23*c-16*f+(-62)
    let y : ℤ := 23*f-16*c+(-62)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 23*x^2+53*x*y+23*y^2-(-7722)*(x+y)+(418275)=0 := by
      dsimp [x,y]
      linear_combination 10647*h1 - 63*((48)*(c+f)-13*e+(4))*hq

    have hp : 0<23*x^2+53*x*y+23*y^2-(-7722)*(x+y)+(418275) := by
      have hxy := mul_nonneg hx hy
      have hs : 0≤x+y := by omega
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

  · dsimp [q2] at hq
    let x : ℤ := 23*c-16*f+(-94)
    let y : ℤ := 23*f-16*c+(-94)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 23*x^2+53*x*y+23*y^2-(-7722)*(x+y)+(418275)=0 := by
      dsimp [x,y]
      linear_combination 10647*h1 - 63*((48)*(c+f)-13*e+(-4))*hq

    have hp : 0<23*x^2+53*x*y+23*y^2-(-7722)*(x+y)+(418275) := by
      have hxy := mul_nonneg hx hy
      have hs : 0≤x+y := by omega
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

private theorem slice_bounds (b c e f : ℤ) (hbLo : 3≤b) (hbHi : b≤13)
    (hz : isSolution ⟨4,b,c,4,e,f⟩)
    (hm : 0≤(16-b)*c-4*e+72-6*b)
    (hi : 0≤(16-b)*f-4*e+72-6*b) : c+f≤sumBound b := by
  interval_cases b

  · simpa [sumBound] using bounds_3 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_4 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_5 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_6 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_7 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_8 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_9 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_10 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_11 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_12 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

  · simpa [sumBound] using bounds_13 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

/-- The bounds follow from two actual length-two comparisons. -/
theorem a_four_d_four_bounds (z : Six) (hz : Chamber z) (ha : z.a=4) (hd : z.d=4)
    (ht : ShortTerminal z 2) : 3≤z.b ∧ z.b≤13 ∧ z.c+z.f≤sumBound z.b := by
  have hb : 3≤z.b := hz.2.2.2.1
  have hInv := (step_preserves_chamber .i1 True.intro z hz).2.2.2.2.2.1
  simp only [step,inv1,ha,hd] at hInv
  have hbHi : z.b≤13 := by omega
  have H := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hm := H [.m2,.m1] (by decide)
  have hi := H [.i1,.i2] (by decide)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,inv1,inv2] at hm hi
  simp only [ha,hd] at hm hi
  have hm' : 0≤(16-z.b)*z.c-4*z.e+72-6*z.b := by nlinarith only [hm]
  have hi' : 0≤(16-z.b)*z.f-4*z.e+72-6*z.b := by nlinarith only [hi]
  have heq : z=⟨4,z.b,z.c,4,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hbHi,slice_bounds _ _ _ _ hb hbHi (heq ▸ hz.1) hm' hi'⟩

private theorem sumBound_le (b : ℤ) : sumBound b≤102 := by
  dsimp [sumBound]
  split_ifs <;> norm_num

/-- A finite box for every remaining coefficient in this actual slice. -/
theorem a_four_d_four_coordinate_bounds (z : Six) (hz : Chamber z)
    (ha : z.a=4) (hd : z.d=4) (ht : ShortTerminal z 2) :
    3≤z.b ∧ z.b≤12 ∧ 3≤z.c ∧ z.c≤99 ∧ 3≤z.e ∧ z.e≤137 ∧ 3≤z.f ∧ z.f≤99 := by
  obtain ⟨hb,hbHi,hcf⟩ := a_four_d_four_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,he,hf⟩ := hz.2.2
  have hsum : z.c+z.f≤102 := hcf.trans (sumBound_le z.b)
  have hb12 : z.b≤12 := by
    by_contra hn
    have hb13 : z.b=13 := by omega
    simp [hb13,sumBound] at hcf
    omega
  have hq : -4≤q2 z := by nlinarith only [hz.1.2]
  simp only [q2,ha,hd] at hq
  have hbe := mul_nonneg (show 0≤z.b-3 by omega) (show 0≤z.e by omega)
  have he137 : z.e≤137 := by nlinarith only [hq,hsum,hbe]
  exact ⟨hb,hb12,hc,by omega,he,he137,hf,by omega⟩

/-- The eliminated binary conic, with the Pfaffian recorded explicitly. -/
def binaryConic (b c f q : ℤ) : ℤ :=
  -(16*b-b^2-16)*(c^2+f^2)+((16-b)*b^2-32*b+32)*c*f+
    (4*b-8)*q*(c+f)+q^2+b^2*(b^2-16*b+24)

private theorem binaryConic_zero (b c e f q : ℤ)
    (hz : isSolution ⟨4,b,c,4,e,f⟩) (hq : q2 ⟨4,b,c,4,e,f⟩=q) :
    binaryConic b c f q=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [q2] at hq
  dsimp [binaryConic]
  linear_combination b^2*h1-((4*b-4)*(c+f)-b*e+q)*hq

def candidate (b c f q : ℤ) : Six := ⟨4,b,c,4,(4*f+4*c-q)/b,f⟩

private instance conditionDecidable (z : Six) :
    Decidable (isSolution z ∧ 0<IntrinsicSigns.thirdMinorSum z ∧
      Coordinates z ∧ BalanceInequalities z) := by
  unfold isSolution Coordinates BalanceInequalities
  infer_instance

def candidateCondition (z : Six) : Bool :=
  decide (isSolution z ∧ 0<IntrinsicSigns.thirdMinorSum z ∧
    Coordinates z ∧ BalanceInequalities z)

/-- Blocks contain ten consecutive values of `c`. The conic test precedes
construction of the Gram tuple, so the finite calculation stays small. -/
def blockCandidates (b : ℤ) (t : ℕ) : List Six :=
  (List.range 10).flatMap fun (j : ℕ) =>
    let c : ℤ := 10*(t : ℤ)+(j : ℤ)+3
    (List.range ((sumBound b-c-2).toNat)).flatMap fun (fi : ℕ) =>
      let f : ℤ := (fi : ℤ)+3
      (([4,-4] : List ℤ).filter (fun q => decide (binaryConic b c f q=0))).map
        (candidate b c f)

def blockSolutions (b : ℤ) (t : ℕ) : List Six :=
  (blockCandidates b t).filter candidateCondition

private theorem shortTerminal_condition (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 2) : candidateCondition z=true := by
  unfold candidateCondition
  exact decide_eq_true ⟨hz.1,hz.2.1,hz.2.2,shortTerminal_balances z hz ht⟩

/-- Completeness is independent of the untrusted finite output table. -/
theorem a_four_d_four_mem_block (z : Six) (hz : Chamber z) (ha : z.a=4) (hd : z.d=4)
    (ht : ShortTerminal z 2) :
    ∃ bi t : ℕ, bi<11 ∧ t<10 ∧ z∈blockSolutions (bi+3) t := by
  obtain ⟨hb,hbHi,hcf⟩ := a_four_d_four_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,_,hf⟩ := hz.2.2
  have hcf102 : z.c+z.f≤102 := hcf.trans (sumBound_le z.b)
  let bi := (z.b-3).toNat
  let ci := (z.c-3).toNat
  let fi := (z.f-3).toNat
  let t := ci/10
  let j := ci%10
  have hbi : (bi : ℤ)=z.b-3 := Int.toNat_of_nonneg (by omega)
  have hci : (ci : ℤ)=z.c-3 := Int.toNat_of_nonneg (by omega)
  have hfi : (fi : ℤ)=z.f-3 := Int.toNat_of_nonneg (by omega)
  have hbshape : (bi : ℤ)+3=z.b := by omega
  have hcshape' : (10*(t : ℤ)+(j : ℤ)+3)=z.c := by
    have h := Nat.mod_add_div ci 10
    have hcast : ((ci%10 : ℕ) : ℤ)+10*((ci/10 : ℕ) : ℤ)=(ci : ℤ) := by exact_mod_cast h
    dsimp [t,j]
    omega
  have htlt : t<10 := by dsimp [t]; omega
  have hjlt : j<10 := by dsimp [j]; omega
  have hfil : fi<(sumBound z.b-z.c-2).toNat := by
    have hh : 0≤sumBound z.b-z.c-2 := by omega
    have hh' := Int.toNat_of_nonneg hh
    omega
  have hshape : z=⟨4,z.b,z.c,4,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  have hsol : isSolution ⟨4,z.b,z.c,4,z.e,z.f⟩ := hshape ▸ hz.1
  have hq : q2 ⟨4,z.b,z.c,4,z.e,z.f⟩=4 ∨ q2 ⟨4,z.b,z.c,4,z.e,z.f⟩= -4 := by
    have hh : (q2 ⟨4,z.b,z.c,4,z.e,z.f⟩-4)*(q2 ⟨4,z.b,z.c,4,z.e,z.f⟩+4)=0 := by
      nlinarith [hsol.2]
    rcases mul_eq_zero.mp hh with hh|hh <;> omega
  refine ⟨bi,t,by omega,htlt,?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_,shortTerminal_condition z hz ht⟩
  rw [blockCandidates]
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hjlt,?_⟩
  simp only [hbshape,hcshape']
  apply List.mem_flatMap.mpr
  refine ⟨fi,List.mem_range.mpr hfil,?_⟩
  have hfshape : (fi : ℤ)+3=z.f := by omega
  simp only [hfshape]
  apply List.mem_map.mpr
  rcases hq with hq|hq
  · refine ⟨4,List.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · exact decide_eq_true (binaryConic_zero _ _ _ _ _ hsol hq)
    · have he : (4*z.f+4*z.c-4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 4*z.f+4*z.c-4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]
  · refine ⟨-4,List.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · exact decide_eq_true (binaryConic_zero _ _ _ _ _ hsol hq)
    · have he : (4*z.f+4*z.c+4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 4*z.f+4*z.c+4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]

end SerreMarkov.PositiveFourFour
