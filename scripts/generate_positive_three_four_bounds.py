#!/usr/bin/env python3
"""Emit arithmetic identities which Lean's ring kernel must verify."""
from pathlib import Path

project=Path(__file__).resolve().parent.parent
out=project/'SerreMarkov'/'PositiveThreeFourBounds.lean'
head='''import SerreMarkov.PositiveThreeTriangles

/-! # Finite conic bounds for the actual positive slice `a=3,d=4`

Two actual one-step height inequalities give nonnegative linear slacks.
The solution equations become positive-coefficient conics in those slacks,
which bound the original coordinates. No height bound is assumed.
-/

namespace SerreMarkov.PositiveThreeFourBounds

open PositiveChamber PositiveThreeTriangles NegativeDescent
set_option maxHeartbeats 5000000

def oneStepCheck (z : Six) : Bool :=
  braidMoves.all (fun g => decide (l1 z ≤ l1 (step g z)))

theorem oneStepCheck_ineq (z : Six) (h : oneStepCheck z=true)
    (g : Generator) (hg : g ∈ braidMoves) : l1 z ≤ l1 (step g z) :=
  of_decide_eq_true (List.all_eq_true.mp h g hg)

private theorem conic_box (px pxy py kx ky C MX MY x y : ℤ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (heq : px*x^2+pxy*x*y+py*y^2-kx*x-ky*y+C=0)
    (hpx : 0 < px) (hpy : 0 < py) (hpxy : 0 ≤ pxy) (hC : 0 ≤ C)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hXP : 0 < px*MX-kx) (hXY : 0 ≤ pxy*MX-ky)
    (hYP : 0 < py*MY-ky) (hYX : 0 ≤ pxy*MY-kx) : x<MX ∧ y<MY := by
  constructor
  · by_contra hn
    have hxM : MX ≤ x := by omega
    have hxp : 0 < px*x-kx := by
      have h := mul_nonneg hpx.le (show 0 ≤ x-MX by omega)
      nlinarith only [h,hXP]
    have hxy : 0 ≤ pxy*x-ky := by
      have h := mul_nonneg hpxy (show 0 ≤ x-MX by omega)
      nlinarith only [h,hXY]
    have ht1 : 0 < x*(px*x-kx) := mul_pos (by omega) hxp
    have ht2 : 0 ≤ y*(py*y+pxy*x-ky) := by
      apply mul_nonneg hy
      have h := mul_nonneg hpy.le hy
      nlinarith only [h,hxy]
    nlinarith only [ht1,ht2,hC,heq]
  · by_contra hn
    have hyM : MY ≤ y := by omega
    have hyp : 0 < py*y-ky := by
      have h := mul_nonneg hpy.le (show 0 ≤ y-MY by omega)
      nlinarith only [h,hYP]
    have hyx : 0 ≤ pxy*y-kx := by
      have h := mul_nonneg hpxy (show 0 ≤ y-MY by omega)
      nlinarith only [h,hYX]
    have ht1 : 0 < y*(py*y-ky) := mul_pos (by omega) hyp
    have ht2 : 0 ≤ x*(px*x+pxy*y-kx) := by
      apply mul_nonneg hx
      have h := mul_nonneg hpx.le hx
      nlinarith only [h,hyx]
    nlinarith only [ht1,ht2,hC,heq]

private theorem bounds_four (c e f : ℤ) (hz : isSolution ⟨3,4,c,4,e,f⟩)
    (hm : 0 ≤ 12+3*c-8-2*e) (hi : 0 ≤ 16+4*f-6-2*e) : c≤164 ∧ f≤181 := by
  have hq : q2 ⟨3,4,c,4,e,f⟩=4 ∨ q2 ⟨3,4,c,4,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  dsimp [q2] at hq
  rcases hq with hq|hq <;> omega
'''
data={
5:{-4:(58,94,23,9800,5950,323750),4:(58,94,23,11480,7070,460950)},
6:{-4:(12,30,5,4680,2880,263520),4:(12,30,5,4680,2880,263520)},
7:{-4:(58,214,23,45360,28014,3871294),4:(58,214,23,41664,25102,3086510)},
8:{-4:(68,410,19,112672,68576,13659136),4:(68,410,19,92704,52192,7695360)}}
scales={5:50,6:44,7:578,8:2116}
boxes={5:(198,308),6:(391,577),7:(783,1219),8:(1657,3610)}
lines=[head]
for b in range(5,9):
    lines.append(f'''\nprivate theorem bounds_{b} (c e f : ℤ) (hz : isSolution ⟨3,{b},c,4,e,f⟩)
    (hm : 0 ≤ {3*b}+3*c-8-2*e) (hi : 0 ≤ {4*b}+4*f-6-2*e) : c≤164 ∧ f≤181 := by
  have hq : q2 ⟨3,{b},c,4,e,f⟩=4 ∨ q2 ⟨3,{b},c,4,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
''')
    for q in(4,-4):
        A=3*b-8;B=4*b-6;K1=3*b*b-8*b+2*q;K2=4*b*b-6*b+2*q
        px,pxy,py,kx,ky,C=data[b][q];MX,MY=boxes[b];scale=scales[b]
        sign='+' if q>0 else '-';absq=abs(q)
        lines.append(f'''  · dsimp [q2] at hq
    let x : ℤ := {A}*c-6*f+{K1}
    let y : ℤ := {B}*f-8*c+{K2}
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : {px}*x^2+{pxy}*x*y+{py}*y^2-{kx}*x-{ky}*y+{C}=0 := by
      dsimp [x,y]
      linear_combination {scale*b*b}*h1 - {scale}*({3*b-4}*c-{b}*e+{4*b-3}*f{sign}{absq})*hq
    have hbox := conic_box {px} {pxy} {py} {kx} {ky} {C} {MX} {MY} x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    dsimp [x,y] at hbox
    omega
''')
tail='''
private theorem fixed_slice_bounds (b c e f : ℤ) (hbLo : 4 ≤ b) (hbHi : b ≤ 8)
    (hz : isSolution ⟨3,b,c,4,e,f⟩)
    (hm : 0 ≤ 3*b+3*c-8-2*e) (hi : 0 ≤ 4*b+4*f-6-2*e) : c≤164 ∧ f≤181 := by
  interval_cases b
  · exact bounds_four c e f hz hm hi
  · exact bounds_5 c e f hz hm hi
  · exact bounds_6 c e f hz hm hi
  · exact bounds_7 c e f hz hm hi
  · exact bounds_8 c e f hz hm hi

theorem chamber_integerL1_eq_sum (z : Six) (hz : Chamber z) :
    integerL1 z=z.a+z.b+z.c+z.d+z.e+z.f := by
  simpa only [applyWord] using braid_word_integerL1_eq_sum z hz [] (by simp)

/-- Actual one-step minima in the slice have a finite coordinate box,
derived from the equations and the two actual height inequalities. -/
theorem a_three_d_four_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) (hd : z.d=4)
    (hone : oneStepCheck z=true) : 4≤z.b ∧ z.b≤8 ∧ z.c≤164 ∧ z.f≤181 := by
  have hbLo : 4≤z.b := (a_three_incident_bounds z hz ha).1
  have hwI : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
  have hInv : 4≤(inv1 z).d := (a_three_incident_bounds (inv1 z) hwI ha).2.2.1
  simp only [inv1,ha,hd] at hInv
  have hbHi : z.b≤8 := by omega
  have hM := oneStepCheck_ineq z hone .m1 (by simp [braidMoves])
  have hI := oneStepCheck_ineq z hone .i2 (by simp [braidMoves])
  have hMz : integerL1 z ≤ integerL1 (mu1 z) := by
    rw [integerL1_cast,integerL1_cast]
    exact_mod_cast hM
  have hIz : integerL1 z ≤ integerL1 (inv2 z) := by
    rw [integerL1_cast,integerL1_cast]
    exact_mod_cast hI
  rw [chamber_integerL1_eq_sum z hz,
    chamber_integerL1_eq_sum (mu1 z) (step_preserves_chamber .m1 True.intro z hz)] at hMz
  rw [chamber_integerL1_eq_sum z hz,
    chamber_integerL1_eq_sum (inv2 z) (step_preserves_chamber .i2 True.intro z hz)] at hIz
  simp only [mu1,ha,hd] at hMz
  simp only [inv2,ha,hd] at hIz
  have hm : 0≤3*z.b+3*z.c-8-2*z.e := by omega
  have hi : 0≤4*z.b+4*z.f-6-2*z.e := by omega
  have heq : z=⟨3,z.b,z.c,4,z.e,z.f⟩ := by ext <;> simp [ha,hd]
  have hbounds := fixed_slice_bounds z.b z.c z.e z.f hbLo hbHi (heq ▸ hz.1) hm hi
  exact ⟨hbLo,hbHi,hbounds.1,hbounds.2⟩

end SerreMarkov.PositiveThreeFourBounds
'''
out.write_text(''.join(lines)+tail)
print(out)
