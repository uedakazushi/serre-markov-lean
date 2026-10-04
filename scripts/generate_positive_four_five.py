"""Generate exact integral conic identities for the positive a=4,d=5 slice."""
from pathlib import Path
from math import isqrt
import sympy as s
x,y=s.symbols('x y')
heads=['''import SerreMarkov.PositiveShortWord

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
''']
branches=[];bounds={}
for b in range(3,18):
 A=20*b-b*b-25;B=20*b-b*b-16;P=(20-b)*b*b-41*b+40;D=A*B-400;k=4;Tx=5*k+90*b-6*b*b;Ty=4*k+112*b-7*b*b
 cv=(B*(x-Tx)+20*(y-Ty))/D;fv=(20*(x-Tx)+A*(y-Ty))/D
 poly=s.Poly(s.expand((-A*cv*cv-B*fv*fv+P*cv*fv+(4*b-10)*k*cv+(5*b-8)*k*fv+k*k+b*b*(b*b-20*b+33))*D*D),x,y)
 g=s.igcd(*poly.coeffs());poly=s.Poly(poly.as_expr()/g,x,y);G=s.Rational(D*D,g);scale=int(s.denom(G));G=int(s.numer(G))
 px=int(poly.coeff_monomial(x*x))*scale;py=int(poly.coeff_monomial(y*y))*scale;q=int(poly.coeff_monomial(x*y))*scale;Kx=-int(poly.coeff_monomial(x))*scale;Ky=-int(poly.coeff_monomial(y))*scale;C=int(poly.coeff_monomial(1))*scale;p=min(px,py);K=max(Kx,Ky)
 disc=(K//scale)**2-4*(p//scale)*(C//scale);M=((K//scale)+isqrt(max(disc,0)))//(2*(p//scale))+2
 bound=(M-1-(-36+202*b-13*b*b)-27)//(A-20) if b!=17 else 0;bounds[b]=bound;z=f'⟨4,{b},c,5,e,f⟩'
 branches.append(f'''private theorem bounds_{b} (c e f : ℤ) (hz : isSolution {z}) ({'_hf' if b in [6,14,17] else 'hf'} : 3≤f)
    (hm : 0≤({20-b})*c-5*e+({90-6*b}))
    (hi : 0≤({20-b})*f-4*e+({112-7*b})) : c+f≤{bound} := by
  have hq : q2 {z}=4 ∨ q2 {z}= -4 := by
    have h : (q2 {z}-4)*(q2 {z}+4)=0 := by nlinarith [hz.2]
    rcases mul_eq_zero.mp h with h|h <;> omega
  have h1 := hz.1
  dsimp [q1] at h1
  rcases hq with hq|hq
''')
 for k in[4,-4]:
  Tx=5*k+90*b-6*b*b;Ty=4*k+112*b-7*b*b;L=G*b*b
  branches.append(f'''  · dsimp [q2] at hq
    let x : ℤ := {A}*c-20*f+({Tx})
    let y : ℤ := {B}*f-20*c+({Ty})
    have hx : 0≤x := by dsimp [x]; omega
    have hy : 0≤y := by dsimp [y]; omega
    have heq : {px}*x^2+{q}*x*y+{py}*y^2-({Kx})*x-({Ky})*y+({C})=0 := by
      dsimp [x,y]
      linear_combination {L}*h1 - {G}*(({4*b-5})*c+({5*b-4})*f-{b}*e+({k}))*hq
''')
  if b!=17:
   branches.append(f'''    have hb := asymmetric_conic_sum_bound {px} {q} {py} ({Kx}) ({Ky}) ({C}) {p} ({K}) {M} x y
      hx hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) heq (by norm_num) (by norm_num)
    dsimp [x,y] at hb
    omega
''')
  else:
   branches.append(f'''    have hxy := mul_nonneg hx hy
    have hp : 0<{px}*x^2+{q}*x*y+{py}*y^2-({Kx})*x-({Ky})*y+({C}) := by
      nlinarith only [hx,hy,hxy,sq_nonneg x,sq_nonneg y]
    omega
''')
heads.append('def sumBound (b : ℤ) : ℤ :=\n  '+ ' else '.join(f'if b={b} then {B}'for b,B in bounds.items())+' else 0\n')
heads+=branches
heads.append('''private theorem slice_bounds (b c e f : ℤ) (hbLo : 3≤b) (hbHi : b≤17)
    (hz : isSolution ⟨4,b,c,5,e,f⟩) (hf : 3≤f)
    (hm : 0≤(20-b)*c-5*e+90-6*b)
    (hi : 0≤(20-b)*f-4*e+112-7*b) : c+f≤sumBound b := by
  interval_cases b
''')
for b in range(3,18):heads.append(f'  · simpa [sumBound] using bounds_{b} c e f hz hf (by nlinarith only [hm]) (by nlinarith only [hi])\n')
heads.append('''/-- Each fixed first triangle gives a finite bound for the remaining coefficients. -/
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
''')
Path('SerreMarkov/PositiveFourFive.lean').write_text('\n'.join(heads))
