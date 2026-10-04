import SerreMarkov.PositiveShortWord
import SerreMarkov.PositiveTriangleLower
import SerreMarkov.PositiveBoundedTable

/-! # The actual short-word terminal slice `a=d=5`

Two genuine length-two comparisons produce nonnegative linear slacks. The
original solution equations become positive conics in these slacks, proving a
finite box without assuming any bound on the original solution height.
-/

namespace SerreMarkov.PositiveFiveFive

open PositiveChamber PositiveShortWord NegativeDescent
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

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
  if b=3 then 197 else if b=4 then 158 else if b=5 then 137 else if b=6 then 122 else if b=7 then 110 else if b=8 then 100 else if b=9 then 90 else if b=10 then 81 else if b=11 then 73 else if b=12 then 65 else if b=13 then 57 else if b=14 then 50 else if b=15 then 42 else if b=16 then 35 else if b=17 then 28 else if b=18 then 22 else if b=19 then 17 else if b=20 then 13 else if b=21 then 11 else 0

private theorem bounds_3 (c e f : ℤ) (hz : isSolution ⟨5,3,c,5,e,f⟩)
    (hm : 0≤(22)*c-5*e+(119))
    (hi : 0≤(22)*f-5*e+(119)) : c+f≤197 := by
  have hq : q2 ⟨5,3,c,5,e,f⟩=4 ∨ q2 ⟨5,3,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,3,c,5,e,f⟩-4)*(q2 ⟨5,3,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 41*c-25*f+(377)
    let y : ℤ := 41*f-25*c+(377)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 41*x^2+402*x*y+41*y^2-(172788)*(x+y)+(59942916)=0 := by
      dsimp [x,y]
      linear_combination 69696*h1 - 7744*((10)*(c+f)-3*e+(4))*hq

    have hb := conic_sum_bound 41 402 (172788) (59942916) 3833 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 41*c-25*f+(337)
    let y : ℤ := 41*f-25*c+(337)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 41*x^2+402*x*y+41*y^2-(172788)*(x+y)+(59942916)=0 := by
      dsimp [x,y]
      linear_combination 69696*h1 - 7744*((10)*(c+f)-3*e+(-4))*hq

    have hb := conic_sum_bound 41 402 (172788) (59942916) 3833 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_4 (c e f : ℤ) (hz : isSolution ⟨5,4,c,5,e,f⟩)
    (hm : 0≤(21)*c-5*e+(112))
    (hi : 0≤(21)*f-5*e+(112)) : c+f≤158 := by
  have hq : q2 ⟨5,4,c,5,e,f⟩=4 ∨ q2 ⟨5,4,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,4,c,5,e,f⟩-4)*(q2 ⟨5,4,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 59*c-25*f+(468)
    let y : ℤ := 59*f-25*c+(468)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+764*x*y+59*y^2-(395136)*(x+y)+(166832064)=0 := by
      dsimp [x,y]
      linear_combination 239904*h1 - 14994*((15)*(c+f)-4*e+(4))*hq

    have hb := conic_sum_bound 59 764 (395136) (166832064) 6245 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 59*c-25*f+(428)
    let y : ℤ := 59*f-25*c+(428)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+764*x*y+59*y^2-(395136)*(x+y)+(166832064)=0 := by
      dsimp [x,y]
      linear_combination 239904*h1 - 14994*((15)*(c+f)-4*e+(-4))*hq

    have hb := conic_sum_bound 59 764 (395136) (166832064) 6245 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_5 (c e f : ℤ) (hz : isSolution ⟨5,5,c,5,e,f⟩)
    (hm : 0≤(20)*c-5*e+(105))
    (hi : 0≤(20)*f-5*e+(105)) : c+f≤137 := by
  have hq : q2 ⟨5,5,c,5,e,f⟩=4 ∨ q2 ⟨5,5,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,5,c,5,e,f⟩-4)*(q2 ⟨5,5,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 75*c-25*f+(545)
    let y : ℤ := 75*f-25*c+(545)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+42*x*y+3*y^2-(25200)*(x+y)+(12063600)=0 := by
      dsimp [x,y]
      linear_combination 20000*h1 - 800*((20)*(c+f)-5*e+(4))*hq

    have hb := conic_sum_bound 3 42 (25200) (12063600) 7891 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 75*c-25*f+(505)
    let y : ℤ := 75*f-25*c+(505)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+42*x*y+3*y^2-(25200)*(x+y)+(12063600)=0 := by
      dsimp [x,y]
      linear_combination 20000*h1 - 800*((20)*(c+f)-5*e+(-4))*hq

    have hb := conic_sum_bound 3 42 (25200) (12063600) 7891 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_6 (c e f : ℤ) (hz : isSolution ⟨5,6,c,5,e,f⟩)
    (hm : 0≤(19)*c-5*e+(98))
    (hi : 0≤(19)*f-5*e+(98)) : c+f≤122 := by
  have hq : q2 ⟨5,6,c,5,e,f⟩=4 ∨ q2 ⟨5,6,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,6,c,5,e,f⟩-4)*(q2 ⟨5,6,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 89*c-25*f+(608)
    let y : ℤ := 89*f-25*c+(608)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 89*x^2+1266*x*y+89*y^2-(849072)*(x+y)+(439160832)=0 := by
      dsimp [x,y]
      linear_combination 831744*h1 - 23104*((25)*(c+f)-6*e+(4))*hq

    have hb := conic_sum_bound 89 1266 (849072) (439160832) 8992 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 89*c-25*f+(568)
    let y : ℤ := 89*f-25*c+(568)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 89*x^2+1266*x*y+89*y^2-(849072)*(x+y)+(439160832)=0 := by
      dsimp [x,y]
      linear_combination 831744*h1 - 23104*((25)*(c+f)-6*e+(-4))*hq

    have hb := conic_sum_bound 89 1266 (849072) (439160832) 8992 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_7 (c e f : ℤ) (hz : isSolution ⟨5,7,c,5,e,f⟩)
    (hm : 0≤(18)*c-5*e+(91))
    (hi : 0≤(18)*f-5*e+(91)) : c+f≤110 := by
  have hq : q2 ⟨5,7,c,5,e,f⟩=4 ∨ q2 ⟨5,7,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,7,c,5,e,f⟩-4)*(q2 ⟨5,7,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 101*c-25*f+(657)
    let y : ℤ := 101*f-25*c+(657)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 101*x^2+1418*x*y+101*y^2-(1031940)*(x+y)+(555739380)=0 := by
      dsimp [x,y]
      linear_combination 1206576*h1 - 24624*((30)*(c+f)-7*e+(4))*hq

    have hb := conic_sum_bound 101 1418 (1031940) (555739380) 9647 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 101*c-25*f+(617)
    let y : ℤ := 101*f-25*c+(617)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 101*x^2+1418*x*y+101*y^2-(1031940)*(x+y)+(555739380)=0 := by
      dsimp [x,y]
      linear_combination 1206576*h1 - 24624*((30)*(c+f)-7*e+(-4))*hq

    have hb := conic_sum_bound 101 1418 (1031940) (555739380) 9647 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_8 (c e f : ℤ) (hz : isSolution ⟨5,8,c,5,e,f⟩)
    (hm : 0≤(17)*c-5*e+(84))
    (hi : 0≤(17)*f-5*e+(84)) : c+f≤100 := by
  have hq : q2 ⟨5,8,c,5,e,f⟩=4 ∨ q2 ⟨5,8,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,8,c,5,e,f⟩-4)*(q2 ⟨5,8,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 111*c-25*f+(692)
    let y : ℤ := 111*f-25*c+(692)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 111*x^2+1512*x*y+111*y^2-(1165248)*(x+y)+(633229056)=0 := by
      dsimp [x,y]
      linear_combination 1590656*h1 - 24854*((35)*(c+f)-8*e+(4))*hq

    have hb := conic_sum_bound 111 1512 (1165248) (633229056) 9923 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 111*c-25*f+(652)
    let y : ℤ := 111*f-25*c+(652)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 111*x^2+1512*x*y+111*y^2-(1165248)*(x+y)+(633229056)=0 := by
      dsimp [x,y]
      linear_combination 1590656*h1 - 24854*((35)*(c+f)-8*e+(-4))*hq

    have hb := conic_sum_bound 111 1512 (1165248) (633229056) 9923 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_9 (c e f : ℤ) (hz : isSolution ⟨5,9,c,5,e,f⟩)
    (hm : 0≤(16)*c-5*e+(77))
    (hi : 0≤(16)*f-5*e+(77)) : c+f≤90 := by
  have hq : q2 ⟨5,9,c,5,e,f⟩=4 ∨ q2 ⟨5,9,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,9,c,5,e,f⟩-4)*(q2 ⟨5,9,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 119*c-25*f+(713)
    let y : ℤ := 119*f-25*c+(713)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 119*x^2+1554*x*y+119*y^2-(1241856)*(x+y)+(661457664)=0 := by
      dsimp [x,y]
      linear_combination 1949184*h1 - 24064*((40)*(c+f)-9*e+(4))*hq

    have hb := conic_sum_bound 119 1554 (1241856) (661457664) 9873 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 119*c-25*f+(673)
    let y : ℤ := 119*f-25*c+(673)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 119*x^2+1554*x*y+119*y^2-(1241856)*(x+y)+(661457664)=0 := by
      dsimp [x,y]
      linear_combination 1949184*h1 - 24064*((40)*(c+f)-9*e+(-4))*hq

    have hb := conic_sum_bound 119 1554 (1241856) (661457664) 9873 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_10 (c e f : ℤ) (hz : isSolution ⟨5,10,c,5,e,f⟩)
    (hm : 0≤(15)*c-5*e+(70))
    (hi : 0≤(15)*f-5*e+(70)) : c+f≤81 := by
  have hq : q2 ⟨5,10,c,5,e,f⟩=4 ∨ q2 ⟨5,10,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,10,c,5,e,f⟩-4)*(q2 ⟨5,10,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 125*c-25*f+(720)
    let y : ℤ := 125*f-25*c+(720)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 5*x^2+62*x*y+5*y^2-(50400)*(x+y)+(25545600)=0 := by
      dsimp [x,y]
      linear_combination 90000*h1 - 900*((45)*(c+f)-10*e+(4))*hq

    have hb := conic_sum_bound 5 62 (50400) (25545600) 9545 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 125*c-25*f+(680)
    let y : ℤ := 125*f-25*c+(680)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 5*x^2+62*x*y+5*y^2-(50400)*(x+y)+(25545600)=0 := by
      dsimp [x,y]
      linear_combination 90000*h1 - 900*((45)*(c+f)-10*e+(-4))*hq

    have hb := conic_sum_bound 5 62 (50400) (25545600) 9545 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_11 (c e f : ℤ) (hz : isSolution ⟨5,11,c,5,e,f⟩)
    (hm : 0≤(14)*c-5*e+(63))
    (hi : 0≤(14)*f-5*e+(63)) : c+f≤73 := by
  have hq : q2 ⟨5,11,c,5,e,f⟩=4 ∨ q2 ⟨5,11,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,11,c,5,e,f⟩-4)*(q2 ⟨5,11,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 129*c-25*f+(713)
    let y : ℤ := 129*f-25*c+(713)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 129*x^2+1506*x*y+129*y^2-(1222452)*(x+y)+(570535812)=0 := by
      dsimp [x,y]
      linear_combination 2466464*h1 - 20384*((50)*(c+f)-11*e+(4))*hq

    have hb := conic_sum_bound 129 1506 (1222452) (570535812) 8985 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 129*c-25*f+(673)
    let y : ℤ := 129*f-25*c+(673)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 129*x^2+1506*x*y+129*y^2-(1222452)*(x+y)+(570535812)=0 := by
      dsimp [x,y]
      linear_combination 2466464*h1 - 20384*((50)*(c+f)-11*e+(-4))*hq

    have hb := conic_sum_bound 129 1506 (1222452) (570535812) 8985 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_12 (c e f : ℤ) (hz : isSolution ⟨5,12,c,5,e,f⟩)
    (hm : 0≤(13)*c-5*e+(56))
    (hi : 0≤(13)*f-5*e+(56)) : c+f≤65 := by
  have hq : q2 ⟨5,12,c,5,e,f⟩=4 ∨ q2 ⟨5,12,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,12,c,5,e,f⟩-4)*(q2 ⟨5,12,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 131*c-25*f+(692)
    let y : ℤ := 131*f-25*c+(692)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 131*x^2+1428*x*y+131*y^2-(1135680)*(x+y)+(468711360)=0 := by
      dsimp [x,y]
      linear_combination 2579616*h1 - 17914*((55)*(c+f)-12*e+(4))*hq

    have hb := conic_sum_bound 131 1428 (1135680) (468711360) 8235 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 131*c-25*f+(652)
    let y : ℤ := 131*f-25*c+(652)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 131*x^2+1428*x*y+131*y^2-(1135680)*(x+y)+(468711360)=0 := by
      dsimp [x,y]
      linear_combination 2579616*h1 - 17914*((55)*(c+f)-12*e+(-4))*hq

    have hb := conic_sum_bound 131 1428 (1135680) (468711360) 8235 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_13 (c e f : ℤ) (hz : isSolution ⟨5,13,c,5,e,f⟩)
    (hm : 0≤(12)*c-5*e+(49))
    (hi : 0≤(12)*f-5*e+(49)) : c+f≤57 := by
  have hq : q2 ⟨5,13,c,5,e,f⟩=4 ∨ q2 ⟨5,13,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,13,c,5,e,f⟩-4)*(q2 ⟨5,13,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 131*c-25*f+(657)
    let y : ℤ := 131*f-25*c+(657)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 131*x^2+1322*x*y+131*y^2-(1009008)*(x+y)+(348272496)=0 := by
      dsimp [x,y]
      linear_combination 2579616*h1 - 15264*((60)*(c+f)-13*e+(4))*hq

    have hb := conic_sum_bound 131 1322 (1009008) (348272496) 7341 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 131*c-25*f+(617)
    let y : ℤ := 131*f-25*c+(617)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 131*x^2+1322*x*y+131*y^2-(1009008)*(x+y)+(348272496)=0 := by
      dsimp [x,y]
      linear_combination 2579616*h1 - 15264*((60)*(c+f)-13*e+(-4))*hq

    have hb := conic_sum_bound 131 1322 (1009008) (348272496) 7341 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_14 (c e f : ℤ) (hz : isSolution ⟨5,14,c,5,e,f⟩)
    (hm : 0≤(11)*c-5*e+(42))
    (hi : 0≤(11)*f-5*e+(42)) : c+f≤50 := by
  have hq : q2 ⟨5,14,c,5,e,f⟩=4 ∨ q2 ⟨5,14,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,14,c,5,e,f⟩-4)*(q2 ⟨5,14,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 129*c-25*f+(608)
    let y : ℤ := 129*f-25*c+(608)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 129*x^2+1194*x*y+129*y^2-(853776)*(x+y)+(225396864)=0 := by
      dsimp [x,y]
      linear_combination 2466464*h1 - 12584*((65)*(c+f)-14*e+(4))*hq

    have hb := conic_sum_bound 129 1194 (853776) (225396864) 6343 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 129*c-25*f+(568)
    let y : ℤ := 129*f-25*c+(568)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 129*x^2+1194*x*y+129*y^2-(853776)*(x+y)+(225396864)=0 := by
      dsimp [x,y]
      linear_combination 2466464*h1 - 12584*((65)*(c+f)-14*e+(-4))*hq

    have hb := conic_sum_bound 129 1194 (853776) (225396864) 6343 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_15 (c e f : ℤ) (hz : isSolution ⟨5,15,c,5,e,f⟩)
    (hm : 0≤(10)*c-5*e+(35))
    (hi : 0≤(10)*f-5*e+(35)) : c+f≤42 := by
  have hq : q2 ⟨5,15,c,5,e,f⟩=4 ∨ q2 ⟨5,15,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,15,c,5,e,f⟩-4)*(q2 ⟨5,15,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 125*c-25*f+(545)
    let y : ℤ := 125*f-25*c+(545)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 5*x^2+42*x*y+5*y^2-(27300)*(x+y)+(4598100)=0 := by
      dsimp [x,y]
      linear_combination 90000*h1 - 400*((70)*(c+f)-15*e+(4))*hq

    have hb := conic_sum_bound 5 42 (27300) (4598100) 5287 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 125*c-25*f+(505)
    let y : ℤ := 125*f-25*c+(505)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 5*x^2+42*x*y+5*y^2-(27300)*(x+y)+(4598100)=0 := by
      dsimp [x,y]
      linear_combination 90000*h1 - 400*((70)*(c+f)-15*e+(-4))*hq

    have hb := conic_sum_bound 5 42 (27300) (4598100) 5287 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_16 (c e f : ℤ) (hz : isSolution ⟨5,16,c,5,e,f⟩)
    (hm : 0≤(9)*c-5*e+(28))
    (hi : 0≤(9)*f-5*e+(28)) : c+f≤35 := by
  have hq : q2 ⟨5,16,c,5,e,f⟩=4 ∨ q2 ⟨5,16,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,16,c,5,e,f⟩-4)*(q2 ⟨5,16,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 119*c-25*f+(468)
    let y : ℤ := 119*f-25*c+(468)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 119*x^2+896*x*y+119*y^2-(508032)*(x+y)+(28449792)=0 := by
      dsimp [x,y]
      linear_combination 1949184*h1 - 7614*((75)*(c+f)-16*e+(4))*hq

    have hb := conic_sum_bound 119 896 (508032) (28449792) 4213 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 119*c-25*f+(428)
    let y : ℤ := 119*f-25*c+(428)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 119*x^2+896*x*y+119*y^2-(508032)*(x+y)+(28449792)=0 := by
      dsimp [x,y]
      linear_combination 1949184*h1 - 7614*((75)*(c+f)-16*e+(-4))*hq

    have hb := conic_sum_bound 119 896 (508032) (28449792) 4213 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_17 (c e f : ℤ) (hz : isSolution ⟨5,17,c,5,e,f⟩)
    (hm : 0≤(8)*c-5*e+(21))
    (hi : 0≤(8)*f-5*e+(21)) : c+f≤28 := by
  have hq : q2 ⟨5,17,c,5,e,f⟩=4 ∨ q2 ⟨5,17,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,17,c,5,e,f⟩-4)*(q2 ⟨5,17,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 111*c-25*f+(377)
    let y : ℤ := 111*f-25*c+(377)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 111*x^2+738*x*y+111*y^2-(342720)*(x+y)+(-27466560)=0 := by
      dsimp [x,y]
      linear_combination 1590656*h1 - 5504*((80)*(c+f)-17*e+(4))*hq

    have hb := conic_sum_bound 111 738 (342720) (-27466560) 3166 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 111*c-25*f+(337)
    let y : ℤ := 111*f-25*c+(337)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 111*x^2+738*x*y+111*y^2-(342720)*(x+y)+(-27466560)=0 := by
      dsimp [x,y]
      linear_combination 1590656*h1 - 5504*((80)*(c+f)-17*e+(-4))*hq

    have hb := conic_sum_bound 111 738 (342720) (-27466560) 3166 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_18 (c e f : ℤ) (hz : isSolution ⟨5,18,c,5,e,f⟩)
    (hm : 0≤(7)*c-5*e+(14))
    (hi : 0≤(7)*f-5*e+(14)) : c+f≤22 := by
  have hq : q2 ⟨5,18,c,5,e,f⟩=4 ∨ q2 ⟨5,18,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,18,c,5,e,f⟩-4)*(q2 ⟨5,18,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 101*c-25*f+(272)
    let y : ℤ := 101*f-25*c+(272)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 101*x^2+582*x*y+101*y^2-(197568)*(x+y)+(-51819264)=0 := by
      dsimp [x,y]
      linear_combination 1206576*h1 - 3724*((85)*(c+f)-18*e+(4))*hq

    have hb := conic_sum_bound 101 582 (197568) (-51819264) 2191 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 101*c-25*f+(232)
    let y : ℤ := 101*f-25*c+(232)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 101*x^2+582*x*y+101*y^2-(197568)*(x+y)+(-51819264)=0 := by
      dsimp [x,y]
      linear_combination 1206576*h1 - 3724*((85)*(c+f)-18*e+(-4))*hq

    have hb := conic_sum_bound 101 582 (197568) (-51819264) 2191 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_19 (c e f : ℤ) (hz : isSolution ⟨5,19,c,5,e,f⟩)
    (hm : 0≤(6)*c-5*e+(7))
    (hi : 0≤(6)*f-5*e+(7)) : c+f≤17 := by
  have hq : q2 ⟨5,19,c,5,e,f⟩=4 ∨ q2 ⟨5,19,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,19,c,5,e,f⟩-4)*(q2 ⟨5,19,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 89*c-25*f+(153)
    let y : ℤ := 89*f-25*c+(153)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 89*x^2+434*x*y+89*y^2-(81396)*(x+y)+(-49267836)=0 := by
      dsimp [x,y]
      linear_combination 831744*h1 - 2304*((90)*(c+f)-19*e+(4))*hq

    have hb := conic_sum_bound 89 434 (81396) (-49267836) 1331 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 89*c-25*f+(113)
    let y : ℤ := 89*f-25*c+(113)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 89*x^2+434*x*y+89*y^2-(81396)*(x+y)+(-49267836)=0 := by
      dsimp [x,y]
      linear_combination 831744*h1 - 2304*((90)*(c+f)-19*e+(-4))*hq

    have hb := conic_sum_bound 89 434 (81396) (-49267836) 1331 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_20 (c e f : ℤ) (hz : isSolution ⟨5,20,c,5,e,f⟩)
    (hm : 0≤(5)*c-5*e+(0))
    (hi : 0≤(5)*f-5*e+(0)) : c+f≤13 := by
  have hq : q2 ⟨5,20,c,5,e,f⟩=4 ∨ q2 ⟨5,20,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,20,c,5,e,f⟩-4)*(q2 ⟨5,20,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 75*c-25*f+(20)
    let y : ℤ := 75*f-25*c+(20)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+12*x*y+3*y^2-(0)*(x+y)+(-1166400)=0 := by
      dsimp [x,y]
      linear_combination 20000*h1 - 50*((95)*(c+f)-20*e+(4))*hq

    have hb := conic_sum_bound 3 12 (0) (-1166400) 624 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 75*c-25*f+(-20)
    let y : ℤ := 75*f-25*c+(-20)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 3*x^2+12*x*y+3*y^2-(0)*(x+y)+(-1166400)=0 := by
      dsimp [x,y]
      linear_combination 20000*h1 - 50*((95)*(c+f)-20*e+(-4))*hq

    have hb := conic_sum_bound 3 12 (0) (-1166400) 624 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_21 (c e f : ℤ) (hz : isSolution ⟨5,21,c,5,e,f⟩)
    (hm : 0≤(4)*c-5*e+(-7))
    (hi : 0≤(4)*f-5*e+(-7)) : c+f≤11 := by
  have hq : q2 ⟨5,21,c,5,e,f⟩=4 ∨ q2 ⟨5,21,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,21,c,5,e,f⟩-4)*(q2 ⟨5,21,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 59*c-25*f+(-127)
    let y : ℤ := 59*f-25*c+(-127)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+186*x*y+59*y^2-(-44688)*(x+y)+(-3619728)=0 := by
      dsimp [x,y]
      linear_combination 239904*h1 - 544*((100)*(c+f)-21*e+(4))*hq

    have hb := conic_sum_bound 59 186 (-44688) (-3619728) 74 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

  · dsimp [q2] at hq
    let x : ℤ := 59*c-25*f+(-167)
    let y : ℤ := 59*f-25*c+(-167)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 59*x^2+186*x*y+59*y^2-(-44688)*(x+y)+(-3619728)=0 := by
      dsimp [x,y]
      linear_combination 239904*h1 - 544*((100)*(c+f)-21*e+(-4))*hq

    have hb := conic_sum_bound 59 186 (-44688) (-3619728) 74 x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega

private theorem bounds_22 (c e f : ℤ) (hz : isSolution ⟨5,22,c,5,e,f⟩)
    (hm : 0≤(3)*c-5*e+(-14))
    (hi : 0≤(3)*f-5*e+(-14)) : c+f≤0 := by
  have hq : q2 ⟨5,22,c,5,e,f⟩=4 ∨ q2 ⟨5,22,c,5,e,f⟩= -4 := by
    have h : (q2 ⟨5,22,c,5,e,f⟩-4)*(q2 ⟨5,22,c,5,e,f⟩+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq

  · dsimp [q2] at hq
    let x : ℤ := 41*c-25*f+(-288)
    let y : ℤ := 41*f-25*c+(-288)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 41*x^2+98*x*y+41*y^2-(-55440)*(x+y)+(15333120)=0 := by
      dsimp [x,y]
      linear_combination 69696*h1 - 144*((105)*(c+f)-22*e+(4))*hq

    have hxy := mul_nonneg hx hy
    have hp : 0<41*x^2+98*x*y+41*y^2-(-55440)*(x+y)+(15333120) := by
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

  · dsimp [q2] at hq
    let x : ℤ := 41*c-25*f+(-328)
    let y : ℤ := 41*f-25*c+(-328)
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : 41*x^2+98*x*y+41*y^2-(-55440)*(x+y)+(15333120)=0 := by
      dsimp [x,y]
      linear_combination 69696*h1 - 144*((105)*(c+f)-22*e+(-4))*hq

    have hxy := mul_nonneg hx hy
    have hp : 0<41*x^2+98*x*y+41*y^2-(-55440)*(x+y)+(15333120) := by
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega

private theorem slice_bounds (b c e f : ℤ) (hbLo : 3≤b) (hbHi : b≤22)
    (hz : isSolution ⟨5,b,c,5,e,f⟩)
    (hm : 0≤(25-b)*c-5*e+140-7*b)
    (hi : 0≤(25-b)*f-5*e+140-7*b) : c+f≤sumBound b := by
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
  · simpa [sumBound] using bounds_14 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_15 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_16 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_17 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_18 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_19 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_20 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_21 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])
  · simpa [sumBound] using bounds_22 c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])

/-- Bounds derived from actual `[m2,m1]` and `[i1,i2]` comparisons. -/
theorem a_five_d_five_bounds (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5)
    (ht : ShortTerminal z 2) : 3≤z.b ∧ z.b≤22 ∧ z.c+z.f≤sumBound z.b := by
  have hb : 3≤z.b := hz.2.2.2.1
  have hInv := (step_preserves_chamber .i1 True.intro z hz).2.2.2.2.2.1
  simp only [step,inv1,ha,hd] at hInv
  have hbHi : z.b≤22 := by omega
  have H := (shortTerminal_iff_polynomial z hz 2).mp ht
  have hm := H [.m2,.m1] (by decide)
  have hi := H [.i1,.i2] (by decide)
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,inv1,inv2] at hm hi
  simp only [ha,hd] at hm hi
  have hm' : 0≤(25-z.b)*z.c-5*z.e+140-7*z.b := by nlinarith only [hm]
  have hi' : 0≤(25-z.b)*z.f-5*z.e+140-7*z.b := by nlinarith only [hi]
  have heq : z=⟨5,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  exact ⟨hb,hbHi,slice_bounds _ _ _ _ hb hbHi (heq ▸ hz.1) hm' hi'⟩

private theorem sumBound_le (b : ℤ) : sumBound b≤197 := by
  unfold sumBound
  repeat' (first | split | omega)

/-- Every coefficient belongs to a finite box, proved from the equations and no-drop hypothesis. -/
theorem a_five_d_five_coordinate_bounds (z : Six) (hz : Chamber z)
    (ha : z.a=5) (hd : z.d=5) (ht : ShortTerminal z 2) :
    3≤z.b ∧ z.b≤21 ∧ 3≤z.c ∧ z.c≤194 ∧ 3≤z.e ∧ z.e≤329 ∧ 3≤z.f ∧ z.f≤194 := by
  obtain ⟨hb,hbHi,hcf⟩ := a_five_d_five_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,he,hf⟩ := hz.2.2
  have hsum : z.c+z.f≤197 := hcf.trans (sumBound_le z.b)
  have hb21 : z.b≤21 := by
    by_contra hn
    have hb22 : z.b=22 := by omega
    simp [hb22,sumBound] at hcf
    omega
  have hq : -4≤q2 z := by nlinarith only [hz.1.2]
  simp only [q2,ha,hd] at hq
  have hbe := mul_nonneg (show 0≤z.b-3 by omega) (show 0≤z.e by omega)
  have he329 : z.e≤329 := by nlinarith only [hq,hsum,hbe]
  exact ⟨hb,hb21,hc,by omega,he,he329,hf,by omega⟩


/-- The eliminated binary conic, with the Pfaffian recorded explicitly. -/
def binaryConic (b c f q : ℤ) : ℤ :=
  -(25*b-b^2-25)*(c^2+f^2)+((25-b)*b^2-50*b+50)*c*f+
    (5*b-10)*q*(c+f)+q^2+b^2*(b^2-25*b+42)

private theorem binaryConic_zero (b c e f q : ℤ)
    (hz : isSolution ⟨5,b,c,5,e,f⟩) (hq : q2 ⟨5,b,c,5,e,f⟩=q) :
    binaryConic b c f q=0 := by
  have h1 := hz.1
  dsimp [q1] at h1
  dsimp [q2] at hq
  dsimp [binaryConic]
  linear_combination b^2*h1-((5*b-5)*(c+f)-b*e+q)*hq

def candidate (b c f q : ℤ) : Six := ⟨5,b,c,5,(5*f+5*c-q)/b,f⟩

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
theorem a_five_d_five_mem_block (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5)
    (ht : ShortTerminal z 2) :
    ∃ bi t : ℕ, bi<20 ∧ t<20 ∧ z∈blockSolutions (bi+3) t := by
  obtain ⟨hb,hbHi,hcf⟩ := a_five_d_five_bounds z hz ha hd ht
  obtain ⟨_,_,hc,_,_,hf⟩ := hz.2.2
  have hcf197 : z.c+z.f≤197 := hcf.trans (sumBound_le z.b)
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
  have htlt : t<20 := by dsimp [t]; omega
  have hjlt : j<10 := by dsimp [j]; omega
  have hfil : fi<(sumBound z.b-z.c-2).toNat := by
    have hh : 0≤sumBound z.b-z.c-2 := by omega
    have hh' := Int.toNat_of_nonneg hh
    omega
  have hshape : z=⟨5,z.b,z.c,5,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  have hsol : isSolution ⟨5,z.b,z.c,5,z.e,z.f⟩ := hshape ▸ hz.1
  have hq : q2 ⟨5,z.b,z.c,5,z.e,z.f⟩=4 ∨ q2 ⟨5,z.b,z.c,5,z.e,z.f⟩= -4 := by
    have hh : (q2 ⟨5,z.b,z.c,5,z.e,z.f⟩-4)*(q2 ⟨5,z.b,z.c,5,z.e,z.f⟩+4)=0 := by
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
    · have he : (5*z.f+5*z.c-4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 5*z.f+5*z.c-4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]
  · refine ⟨-4,List.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · exact decide_eq_true (binaryConic_zero _ _ _ _ _ hsol hq)
    · have he : (5*z.f+5*z.c+4)/z.b=z.e := by
        dsimp [q2] at hq
        have heq : 5*z.f+5*z.c+4=z.e*z.b := by nlinarith only [hq]
        rw [heq,Int.mul_ediv_cancel _ (by omega)]
      ext <;> simp [candidate,ha,hd,he]


/-- The only actual terminal point in this slice. -/
def terminal : Six := ⟨5,11,4,5,4,4⟩

def blockCheck (bi t : ℕ) : Bool :=
  (blockSolutions ((bi : ℤ)+3) t).all (fun z => decide (z=terminal))

theorem blockCheck_correct (bi t : ℕ) (h : blockCheck bi t=true)
    (z : Six) (hz : z∈blockSolutions ((bi : ℤ)+3) t) : z=terminal := by
  exact of_decide_eq_true (List.all_eq_true.mp h z hz)

/-- The generic completeness proof is independent of the finite checks. -/
theorem a_five_d_five_eq_of_checks
    (hchecks : ∀ bi t : ℕ, bi<20 → t<20 → blockCheck bi t=true)
    (z : Six) (hz : Chamber z) (ha : z.a=5) (hd : z.d=5) (ht : ShortTerminal z 2) :
    z=terminal := by
  obtain ⟨bi,t,hbi,ht',hmem⟩ := a_five_d_five_mem_block z hz ha hd ht
  exact blockCheck_correct bi t (hchecks bi t hbi ht') z hmem

end SerreMarkov.PositiveFiveFive
