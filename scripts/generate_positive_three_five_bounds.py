#!/usr/bin/env python3
"""Generate exact conic identities, independently verified by Lean."""
import sympy as s
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'SerreMarkov'
head='''import SerreMarkov.PositiveThreeFourBounds
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
'''
lines=[head];records={};c,e,f,x,y=s.symbols('c e f x y');a=3;d=5
for b in range(4,12):
 A=a*d*b-b*b-d*d;B=a*d*b-b*b-a*a;C1=d*(a*a+a-2)-(a+2)*b;C2=a*(d*d+d-2)-(d+2)*b;M=s.Matrix([[A,-a*d],[-a*d,B]])
 rec={}
 for q in(4,-4):
  cf=M.inv()*s.Matrix([x-(d*q+b*C1),y-(a*q+b*C2)]);ep=(a*f+d*c-q)/b
  Q=a*c*d*f-a*b*d-a*c*e-b*c*f-d*e*f+a*a+b*b+c*c+d*d+e*e+f*f-8
  P=s.Poly(s.expand(Q.subs(e,ep).subs({c:cf[0],f:cf[1]},simultaneous=True)),x,y)
  den=int(s.ilcm(*[t.q for t in P.coeffs()]));px,pxy,py,lx,ly,C=[int(t*den)for t in(P.coeff_monomial(x*x),P.coeff_monomial(x*y),P.coeff_monomial(y*y),P.coeff_monomial(x),P.coeff_monomial(y),P.coeff_monomial(1))];kx=-lx;ky=-ly
  MX=1
  while not(2*px*MX-kx>=0 and pxy*MX-ky>=0 and px*MX*MX-kx*MX+C>0):MX+=1
  MY=1
  while not(2*py*MY-ky>=0 and pxy*MY-kx>=0 and py*MY*MY-ky*MY+C>0):MY+=1
  cm=int(s.floor(cf[0].subs({x:MX-1,y:MY-1})));fm=int(s.floor(cf[1].subs({x:MX-1,y:MY-1})))
  assert den%(b*b)==0
  rec[q]=(px,pxy,py,kx,ky,C,MX,MY,cm,fm,den,den//(b*b))
 cBound=max(v[8]for v in rec.values());fBound=max(v[9]for v in rec.values());records[b]=(cBound,fBound)
 lines.append(f'''
private theorem bounds_{b} (c e f : ℤ) (hz : isSolution ⟨3,{b},c,5,e,f⟩)
    (hm : 0 ≤ {15-b}*c-5*e+{50-5*b})
    (hi : 0 ≤ {15-b}*f-3*e+{84-7*b}) : c ≤ {cBound} ∧ f ≤ {fBound} := by
  have hq : q2 ⟨3,{b},c,5,e,f⟩=4 ∨ q2 ⟨3,{b},c,5,e,f⟩= -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
''')
 for q in(4,-4):
  px,pxy,py,kx,ky,C,MX,MY,cm,fm,den,R=rec[q]
  lines.append(f'''  · dsimp [q2] at hq
    let x : ℤ := {A}*c-15*f+({d*q+b*C1})
    let y : ℤ := {B}*f-15*c+({a*q+b*C2})
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hp : {px}*x^2+{pxy}*x*y+{py}*y^2-({kx})*x-({ky})*y+({C})=0 := by
      dsimp [x,y]
      linear_combination {den}*h1 - {R}*({3*b-5}*c-{b}*e+{5*b-3}*f+({q}))*hq
    have hb := conic_box {px} {pxy} {py} ({kx}) ({ky}) ({C}) {MX} {MY} x y hx hy hp
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
''')
lines.append('\ndef cBound : ℕ → ℕ\n'+''.join(f'  | {b} => {records[b][0]}\n'for b in records)+'  | _ => 0\n')
lines.append('\ndef fBound : ℕ → ℕ\n'+''.join(f'  | {b} => {records[b][1]}\n'for b in records)+'  | _ => 0\n')
lines.append('''
private theorem fixed_bounds (b c e f : ℤ) (hb : 4 ≤ b) (hb' : b ≤ 11)
    (hz : isSolution ⟨3,b,c,5,e,f⟩)
    (hm : 0 ≤ (15-b)*c-5*e+50-5*b)
    (hi : 0 ≤ (15-b)*f-3*e+84-7*b) :
    c ≤ (cBound b.toNat : ℤ) ∧ f ≤ (fBound b.toNat : ℤ) := by
  interval_cases b
''')
for b in records:lines.append(f'  · simpa only [cBound,fBound] using bounds_{b} c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])\n')
lines.append('''
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
''')
(root/'PositiveThreeFiveBounds.lean').write_text(''.join(lines))
