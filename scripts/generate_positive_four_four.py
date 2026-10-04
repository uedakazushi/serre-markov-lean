"""Generate exact integral conic certificates; every identity is checked in Lean."""
from pathlib import Path
from math import isqrt
import sympy as s
x,y=s.symbols('x y')
src=['''import SerreMarkov.PositiveShortWord
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
''']
for b in range(3,14):
 A=16*b-b*b-16;B=(16-b)*b*b-32*b+32;D=A*A-256;k=4;T=4*k+72*b-6*b*b
 cv=(A*x+16*y-(A+16)*T)/D;fv=(16*x+A*y-(A+16)*T)/D
 poly=s.Poly(s.expand((-A*(cv*cv+fv*fv)+B*cv*fv+(4*b-8)*k*(cv+fv)+k*k+b*b*(b*b-16*b+24))*D*D),x,y)
 g=s.igcd(*poly.coeffs());poly=s.Poly(poly.as_expr()/g,x,y);G=s.Rational(D*D,g);scale=int(s.denom(G));G=int(s.numer(G))
 p=int(poly.coeff_monomial(x*x))*scale;q=int(poly.coeff_monomial(x*y))*scale;K=-int(poly.coeff_monomial(x))*scale;C=int(poly.coeff_monomial(1))*scale
 pbase=p//scale;Kbase=K//scale;Cbase=C//scale;disc=Kbase*Kbase-4*pbase*Cbase
 M=(Kbase+isqrt(max(disc,0)))//(2*pbase)+2
 Bnd={3:102,4:73,5:59,6:49,7:40,8:32,9:26,10:20,11:15,12:12,13:0}[b]
 z=f'⟨4,{b},c,4,e,f⟩';t0=72*b-6*b*b
 src.append(f'''private theorem bounds_{b} (c e f : ℤ) (hz : isSolution {z})
    (hm : 0≤({16-b})*c-4*e+({72-6*b}))
    (hi : 0≤({16-b})*f-4*e+({72-6*b})) : c+f≤{Bnd} := by
  have hq : q2 {z}=4 ∨ q2 {z}= -4 := by
    have h : (q2 {z}-4)*(q2 {z}+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
''')
 for k in [4,-4]:
  T=4*k+t0;Ttxt=f'({T})';L=G*b*b
  src.append(f'''  · dsimp [q2] at hq
    let x : ℤ := {A}*c-16*f+{Ttxt}
    let y : ℤ := {A}*f-16*c+{Ttxt}
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : {p}*x^2+{q}*x*y+{p}*y^2-({K})*(x+y)+({C})=0 := by
      dsimp [x,y]
      linear_combination {L}*h1 - {G}*(({4*b-4})*(c+f)-{b}*e+({k}))*hq
''')
  if b!=13:
   src.append(f'''    have hb := conic_sum_bound {p} {q} ({K}) ({C}) {M} x y hx hy
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
''')
  else:
   src.append(f'''    have hp : 0<{p}*x^2+{q}*x*y+{p}*y^2-({K})*(x+y)+({C}) := by
      have hxy := mul_nonneg hx hy
      have hs : 0≤x+y := by omega
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega
''')
src.append('''private theorem slice_bounds (b c e f : ℤ) (hbLo : 3≤b) (hbHi : b≤13)
    (hz : isSolution ⟨4,b,c,4,e,f⟩)
    (hm : 0≤(16-b)*c-4*e+72-6*b)
    (hi : 0≤(16-b)*f-4*e+72-6*b) : c+f≤sumBound b := by
  interval_cases b
''')
for b in range(3,14):
 src.append(f'  · simpa [sumBound] using bounds_{b} c e f hz (by nlinarith only [hm]) (by nlinarith only [hi])\n')
src.append('''/-- The bounds follow from two actual length-two comparisons. -/
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

end SerreMarkov.PositiveFourFour
''')
target=Path('SerreMarkov/PositiveFourFour.lean')
text='\n'.join(src)
# Retain the separately developed consequences and finite checks.
if target.exists() and 'private theorem sumBound_le' in target.read_text():
 suffix=target.read_text().split('private theorem sumBound_le',1)[1]
 text=text.replace('end SerreMarkov.PositiveFourFour','private theorem sumBound_le'+suffix)
target.write_text(text)
