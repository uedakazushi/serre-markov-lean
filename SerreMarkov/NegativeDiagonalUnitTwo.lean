import SerreMarkov.NegativeTwoEdge
import SerreMarkov.CyclicMutation

/-! # A unique unit diagonal with all five other edges of absolute value at least two

Strict descent uses one or two elementary mutations in a positive crossing
phase. The polynomial certificates also cover the affine lower bound two.
Every transport compares the final word with the original height.
-/

namespace SerreMarkov.NegativeDiagonalUnitTwo

open NegativeDescent NegativePairDescent
set_option maxHeartbeats 1000000

private theorem phaseCertificate_le_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+2)*(C+1)-2*(E+2)) (hk : q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩=(-4)) : q1 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩<8 := by
  have hrel : q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩-(-4)=0 := by omega
  have hcert : 16*(8-q1 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩) =
      (16 + 13*E + 38*F + 26*D + 24*D*F + 8*D*F*E + 17*C*D + 8*C*D^2 + 4*C^2 + 4*C^2*D + 149*A + 6*A*E + 147*A*F + 16*A*F^2 + 4*A*D*F + 84*A*C + 20*A*C*F + 6*A*C*D + 18*A*C^2 + 48*A^2 + 40*A^2*F + 4*A^2*F^2 + 22*A^2*C + 6*A^2*C*F + 4*A^2*C^2) + (23 + 4*E + 4*F + 28*D + 12*D*F + 2*C + 4*C*D + 2*A*F)*((A+2)*(C+1)-2*(E+2)) + (39 + 8*E + 8*F - 8*D - 12*C + 10*A + 4*A*F - 4*A*C)*(q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(16 + 13*E + 38*F + 26*D + 24*D*F + 8*D*F*E + 17*C*D + 8*C*D^2 + 4*C^2 + 4*C^2*D + 149*A + 6*A*E + 147*A*F + 16*A*F^2 + 4*A*D*F + 84*A*C + 20*A*C*F + 6*A*C*D + 18*A*C^2 + 48*A^2 + 40*A^2*F + 4*A^2*F^2 + 22*A^2*C + 6*A^2*C*F + 4*A^2*C^2) := by positivity
  have hnn : 0≤(23 + 4*E + 4*F + 28*D + 12*D*F + 2*C + 4*C*D + 2*A*F)*((A+2)*(C+1)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_le_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+2)*(C+1)-2*(E+2)) (hk : q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩=4) : q1 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩<8 := by
  have hrel : q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩-4=0 := by omega
  have hcert : 40*(8-q1 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩) =
      (40 + 150*E + 28*F + 8*F*E + 24*F^2 + 322*D + 182*D*E + 8*D*F*E + 24*D^2 + 32*C*D^2 + 110*A*F + 56*A*F^2 + 105*A*D + 276*A*C + 20*A*C*F + 59*A*C*D + 4*A*C*D*F + 54*A*C^2 + 14*A*C^2*D + 77*A^2 + 12*A^2*F^2 + 106*A^2*C + 17*A^2*C^2) + (110 + 10*E + 8*F + 167*D + 24*D*F + 10*C*D + 43*A + 4*A*F + 7*A*C)*((A+2)*(C+1)-2*(E+2)) + (-50 + 20*E + 32*F - 32*D - 20*C - 76*A + 12*A*F - 24*A*C)*(q2 ⟨A+2,1,C+2,A+2+D,E+2,-(F+2)⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(40 + 150*E + 28*F + 8*F*E + 24*F^2 + 322*D + 182*D*E + 8*D*F*E + 24*D^2 + 32*C*D^2 + 110*A*F + 56*A*F^2 + 105*A*D + 276*A*C + 20*A*C*F + 59*A*C*D + 4*A*C*D*F + 54*A*C^2 + 14*A*C^2*D + 77*A^2 + 12*A^2*F^2 + 106*A^2*C + 17*A^2*C^2) := by positivity
  have hnn : 0≤(110 + 10*E + 8*F + 167*D + 24*D*F + 10*C*D + 43*A + 4*A*F + 7*A*C)*((A+2)*(C+1)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_ge_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(D+2+A)*(C+3)-2*(D+2)-2*(E+2)) (hk : q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩=(-4)) : q1 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩<8 := by
  have hrel : q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩-(-4)=0 := by omega
  have hcert : 4*(8-q1 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩) =
      (18 + 2*F*E + 51*D + 22*D*F + 2*D*F^2 + 10*D^2 + 4*D^2*F + 6*C + 31*C*D + C*D*E + 8*C*D*F + 9*C*D^2 + 3*C*D^2*F + 2*C^2*D + 15*A + 15*A*E + 26*A*F + 4*A*F*E + 6*A*F^2 + 8*A*D*F + 2*A*D*F^2 + A*C + 3*A*C*E + A*C*D*F + 8*A^2 + 10*A^2*F + 2*A^2*F^2) + (7 + E + 2*F + 2*D + D*F)*((D+2+A)*(C+3)-2*(D+2)-2*(E+2)) + (4 + 2*E + 2*F - 3*D - 2*C + 6*A + 2*A*F)*(q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(18 + 2*F*E + 51*D + 22*D*F + 2*D*F^2 + 10*D^2 + 4*D^2*F + 6*C + 31*C*D + C*D*E + 8*C*D*F + 9*C*D^2 + 3*C*D^2*F + 2*C^2*D + 15*A + 15*A*E + 26*A*F + 4*A*F*E + 6*A*F^2 + 8*A*D*F + 2*A*D*F^2 + A*C + 3*A*C*E + A*C*D*F + 8*A^2 + 10*A^2*F + 2*A^2*F^2) := by positivity
  have hnn : 0≤(7 + E + 2*F + 2*D + D*F)*((D+2+A)*(C+3)-2*(D+2)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_ge_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(D+2+A)*(C+3)-2*(D+2)-2*(E+2)) (hk : q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩=4) : q1 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩<8 := by
  have hrel : q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩-4=0 := by omega
  have hcert : 1120*(8-q1 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩) =
      (1120 + 3150*E + 280*F^2 + 6770*D + 6634*D*F + 1199*D*F*E + 1242*D*F^2 + 2770*D^2 + 596*D^2*F + 271*D^2*F^2 + 210*C*E + 9930*C*D + 385*C*D*E + 560*C*D*F + 2445*C*D^2 + 560*C^2*D + 2520*A + 2345*A*E + 4340*A*F + 350*A*F*E + 700*A*F^2 + 271*A*D*F^2 + 1400*A*C + 735*A*C*E + 1260*A*C*F + 1090*A*C*D + 271*A*C*D*F + 560*A^2*F) + (3080 + 385*E + 420*F + 590*D + 849*D*F)*((D+2+A)*(C+3)-2*(D+2)-2*(E+2)) + (-1400 + 350*E + 700*F - 795*D + 271*D*F - 560*C + 560*A)*(q2 ⟨D+2+A,1,C+2,D+2,E+2,-(F+2)⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(1120 + 3150*E + 280*F^2 + 6770*D + 6634*D*F + 1199*D*F*E + 1242*D*F^2 + 2770*D^2 + 596*D^2*F + 271*D^2*F^2 + 210*C*E + 9930*C*D + 385*C*D*E + 560*C*D*F + 2445*C*D^2 + 560*C^2*D + 2520*A + 2345*A*E + 4340*A*F + 350*A*F*E + 700*A*F^2 + 271*A*D*F^2 + 1400*A*C + 735*A*C*E + 1260*A*C*F + 1090*A*C*D + 271*A*C*D*F + 560*A^2*F) := by positivity
  have hnn : 0≤(3080 + 385*E + 420*F + 590*D + 849*D*F)*((D+2+A)*(C+3)-2*(D+2)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_fc_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+1)*(C+2)-2*(E+2)) (hk : q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩=(-4)) : q1 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩<8 := by
  have hrel : q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩-(-4)=0 := by omega
  have hcert : 4*(8-q1 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩) =
      (4 + E + 8*F + 2*D + 4*D^2 + 65*C + 19*C*F + 21*C*D + 4*C*D*F + 4*C*D^2 + 8*C^2 + 3*A*F + 2*A*F^2 + 34*A*C + 11*A*C*F + 6*A*C*D + 2*A*C*D*F + 11*A*C^2 + 2*A*C^2*D + 4*A^2*C + A^2*C^2) + (5 + E + 7*F + 2*D*F + 4*C + C*D + A*F)*((A+1)*(C+2)-2*(E+2)) + (9 + 2*E - 2*F + 4*D - 7*C - 2*A - A*C)*(q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(4 + E + 8*F + 2*D + 4*D^2 + 65*C + 19*C*F + 21*C*D + 4*C*D*F + 4*C*D^2 + 8*C^2 + 3*A*F + 2*A*F^2 + 34*A*C + 11*A*C*F + 6*A*C*D + 2*A*C*D*F + 11*A*C^2 + 2*A*C^2*D + 4*A^2*C + A^2*C^2) := by positivity
  have hnn : 0≤(5 + E + 7*F + 2*D*F + 4*C + C*D + A*F)*((A+1)*(C+2)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_fc_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+1)*(C+2)-2*(E+2)) (hk : q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩=4) : q1 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩<8 := by
  have hrel : q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩-4=0 := by omega
  have hcert : 8*(8-q1 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩) =
      (8 + 30*E + 74*F + 34*F*E + 12*D + 8*D^2 + 6*C + 21*C*F + 14*C*D + 8*C*D*F + 8*C*D^2 + 16*C^2 + 4*A*F^2 + 48*A*C + 13*A*C*F + 4*A*C*D + 4*A*C*D*F + 20*A*C^2 + 12*A^2*C + 4*A^2*C*F + 4*A^2*C^2) + (22 + 2*E + 31*F + 4*D*F + 8*C + 2*C*D + 2*A*F + 2*A*C)*((A+1)*(C+2)-2*(E+2)) + (-10 + 4*E - 4*F + 8*D - 14*C - 4*A - 6*A*C)*(q2 ⟨A+2,1,C+2,-(D+2),E+2,C+2+F⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(8 + 30*E + 74*F + 34*F*E + 12*D + 8*D^2 + 6*C + 21*C*F + 14*C*D + 8*C*D*F + 8*C*D^2 + 16*C^2 + 4*A*F^2 + 48*A*C + 13*A*C*F + 4*A*C*D + 4*A*C*D*F + 20*A*C^2 + 12*A^2*C + 4*A^2*C*F + 4*A^2*C^2) := by positivity
  have hnn : 0≤(22 + 2*E + 31*F + 4*D*F + 8*C + 2*C*D + 2*A*F + 2*A*C)*((A+1)*(C+2)-2*(E+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_cf_minus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(F+2+C)-2*(E+2)-2*(F+2)) (hk : q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩=(-4)) : q1 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩<8 := by
  have hrel : q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩-(-4)=0 := by omega
  have hcert : 4*(8-q1 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩) =
      (18 + 51*F + 10*F^2 + 2*D*E + 22*D*F + 4*D*F^2 + 2*D^2*F + 15*C + 15*C*E + 26*C*D + 4*C*D*E + 8*C*D*F + 6*C*D^2 + 2*C*D^2*F + 8*C^2 + 10*C^2*D + 2*C^2*D^2 + 6*A + 31*A*F + A*F*E + 9*A*F^2 + 8*A*D*F + 3*A*D*F^2 + A*C + 3*A*C*E + A*C*D*F + 2*A^2*F) + (7 + E + 2*F + 2*D + D*F)*((A+3)*(F+2+C)-2*(E+2)-2*(F+2)) + (4 + 2*E - 3*F + 2*D + 6*C + 2*C*D - 2*A)*(q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩-(-4)) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(18 + 51*F + 10*F^2 + 2*D*E + 22*D*F + 4*D*F^2 + 2*D^2*F + 15*C + 15*C*E + 26*C*D + 4*C*D*E + 8*C*D*F + 6*C*D^2 + 2*C*D^2*F + 8*C^2 + 10*C^2*D + 2*C^2*D^2 + 6*A + 31*A*F + A*F*E + 9*A*F^2 + 8*A*D*F + 3*A*D*F^2 + A*C + 3*A*C*E + A*C*D*F + 2*A^2*F) := by positivity
  have hnn : 0≤(7 + E + 2*F + 2*D + D*F)*((A+3)*(F+2+C)-2*(E+2)-2*(F+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem phaseCertificate_cf_plus (A C D F E : ℤ)
    (hA : 0≤A) (hC : 0≤C) (hD : 0≤D) (hF : 0≤F) (hE : 0≤E)
    (hg : 0≤(A+3)*(F+2+C)-2*(E+2)-2*(F+2)) (hk : q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩=4) : q1 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩<8 := by
  have hrel : q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩-4=0 := by omega
  have hcert : 1120*(8-q1 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩) =
      (1120 + 3150*E + 6770*F + 2770*F^2 + 6634*D*F + 1199*D*F*E + 596*D*F^2 + 280*D^2 + 1242*D^2*F + 271*D^2*F^2 + 2520*C + 2345*C*E + 4340*C*D + 350*C*D*E + 700*C*D^2 + 271*C*D^2*F + 560*C^2*D + 210*A*E + 9930*A*F + 385*A*F*E + 2445*A*F^2 + 560*A*D*F + 1400*A*C + 735*A*C*E + 1090*A*C*F + 1260*A*C*D + 271*A*C*D*F + 560*A^2*F) + (3080 + 385*E + 590*F + 420*D + 849*D*F)*((A+3)*(F+2+C)-2*(E+2)-2*(F+2)) + (-1400 + 350*E - 795*F + 700*D + 271*D*F + 560*C - 560*A)*(q2 ⟨A+2,1,F+2+C,-(D+2),E+2,F+2⟩-4) := by
    dsimp [q1,q2]
    ring
  rw [hrel,mul_zero,add_zero] at hcert
  have hpos : 0<(1120 + 3150*E + 6770*F + 2770*F^2 + 6634*D*F + 1199*D*F*E + 596*D*F^2 + 280*D^2 + 1242*D^2*F + 271*D^2*F^2 + 2520*C + 2345*C*E + 4340*C*D + 350*C*D*E + 700*C*D^2 + 271*C*D^2*F + 560*C^2*D + 210*A*E + 9930*A*F + 385*A*F*E + 2445*A*F^2 + 560*A*D*F + 1400*A*C + 735*A*C*E + 1090*A*C*F + 1260*A*C*D + 271*A*C*D*F + 560*A^2*F) := by positivity
  have hnn : 0≤(3080 + 385*E + 590*F + 420*D + 849*D*F)*((A+3)*(F+2+C)-2*(E+2)-2*(F+2)) := mul_nonneg (by positivity) hg
  nlinarith [hcert]

private theorem solution_q2_cases (z : Six) (hz : isSolution z) : q2 z=4 ∨ q2 z=-4 := by
  have h := hz.2
  have hp : (q2 z-4)*(q2 z+4)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with h|h <;> omega

private theorem phase_forbidden_le (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : z.a≤z.d) (hf : z.f≤-2) (hg : 0≤z.a*(z.c-1)-2*z.e) : False := by
  have hmodel : (⟨z.a-2+2,1,z.c-2+2,z.a-2+2+(z.d-z.a),z.e-2+2,-(-z.f-2+2)⟩ : Six)=z := by ext <;> simp [hb]
  have hgap : 0≤(z.a-2+2)*(z.c-2+1)-2*(z.e-2+2) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_le_plus (z.a-2) (z.c-2) (z.d-z.a) (-z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_le_minus (z.a-2) (z.c-2) (z.d-z.a) (-z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem phase_forbidden_ge (z : Six) (hz : isSolution z)
    (hb : z.b=1) (_ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : 2≤z.d) (hda : z.d≤z.a) (hf : z.f≤-2) (hg : 0≤z.a*(z.c+1)-2*z.d-2*z.e) : False := by
  have hmodel : (⟨z.d-2+2+(z.a-z.d),1,z.c-2+2,z.d-2+2,z.e-2+2,-(-z.f-2+2)⟩ : Six)=z := by ext <;> simp [hb]
  have hgap : 0≤(z.d-2+2+(z.a-z.d))*(z.c-2+3)-2*(z.d-2+2)-2*(z.e-2+2) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_ge_plus (z.a-z.d) (z.c-2) (z.d-2) (-z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_ge_minus (z.a-z.d) (z.c-2) (z.d-2) (-z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem positive_product_four (a b : ℤ) (ha : 2≤a) (hb : 2≤b) : 4≤a*b := by
  have h := mul_nonneg (by omega : 0≤a-2) (by omega : 0≤b-2)
  nlinarith

private theorem phase_forbidden_fc (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : z.d≤-2) (hf : z.c≤z.f) (hg : 0≤(z.a-1)*z.c-2*z.e) : False := by
  have hmodel : (⟨z.a-2+2,1,z.c-2+2,-(-z.d-2+2),z.e-2+2,z.c-2+2+(z.f-z.c)⟩ : Six)=z := by
    ext <;> simp [hb]
  have hgap : 0≤(z.a-2+1)*(z.c-2+2)-2*(z.e-2+2) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_fc_plus (z.a-2) (z.c-2) (-z.d-2) (z.f-z.c) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_fc_minus (z.a-2) (z.c-2) (-z.d-2) (z.f-z.c) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

private theorem phase_forbidden_cf (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hf : 2≤z.f) (he : 2≤z.e)
    (hd : z.d≤-2) (hc : z.f≤z.c) (hg : 0≤(z.a+1)*z.c-2*z.e-2*z.f) : False := by
  have hmodel : (⟨z.a-2+2,1,z.f-2+2+(z.c-z.f),-(-z.d-2+2),z.e-2+2,z.f-2+2⟩ : Six)=z := by
    ext <;> simp [hb]
  have hgap : 0≤(z.a-2+3)*(z.f-2+2+(z.c-z.f))-2*(z.e-2+2)-2*(z.f-2+2) := by nlinarith [hg]
  rcases solution_q2_cases z hz with hk | hk
  · have hh := phaseCertificate_cf_plus (z.a-2) (z.c-z.f) (-z.d-2) (z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega
  · have hh := phaseCertificate_cf_minus (z.a-2) (z.c-z.f) (-z.d-2) (z.f-2) (z.e-2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hgap (by simpa only [hmodel] using hk)
    rw [hmodel,hz.1] at hh
    omega

/-- Two forward braids bypass the plateau of an affine edge. -/
theorem opposed_forward_descent (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : z.d≤-2) (hf : 2≤z.f) :
    l1 (applyWord z [.m1,.m2])<l1 z := by
  rw [two_forward_word_formula,l1_lt_iff]
  dsimp [integerL1]
  simp only [hb,one_mul,abs_of_nonneg (by omega : 0≤z.a),
    abs_of_nonneg (by omega : 0≤z.c),abs_of_nonneg (by omega : 0≤z.e),
    abs_of_nonneg (by omega : 0≤z.f)]
  by_contra hn
  have hL : |z.c-z.f|≤z.c+z.f := by
    simpa [abs_of_nonneg (by omega : 0≤z.c),abs_of_nonneg (by omega : 0≤z.f)]
      using abs_sub_le z.c 0 z.f
  have hac : 0≤z.a*z.c-z.e := by
    by_contra hh
    rw [abs_of_nonpos (by omega : z.a*z.c-z.e≤0)] at hn
    have hp := mul_nonneg (by omega : 0≤z.a-1) (by omega : 0≤z.c)
    nlinarith
  rw [abs_of_nonneg hac] at hn
  rcases le_total z.c z.f with hcf|hfc
  · rw [abs_of_nonpos (by omega : z.c-z.f≤0)] at hn
    exact phase_forbidden_fc z hz hb ha hc he hd hcf (by nlinarith)
  · rw [abs_of_nonneg (by omega : 0≤z.c-z.f)] at hn
    exact phase_forbidden_cf z hz hb ha hf he hd hfc (by nlinarith)

theorem unit_b_positive_phase (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : 2≤|z.d|) (hf : 2≤|z.f|) :
    l1 (mu1 z)<l1 z ∨ l1 (inv2 z)<l1 z ∨ l1 (applyWord z [.m1,.m2])<l1 z := by
  have hd' : 2≤z.d ∨ z.d≤-2 := by rcases le_abs.mp hd with h|h <;> omega
  have hf' : 2≤z.f ∨ z.f≤-2 := by rcases le_abs.mp hf with h|h <;> omega
  have hac4 := positive_product_four z.a z.c ha hc
  have hL : |z.a-z.d|≤z.a+|z.d| := by
    simpa [abs_of_nonneg (by omega : 0≤z.a)] using abs_sub_le z.a 0 z.d
  rcases hd' with hd | hd <;> rcases hf' with hf | hf
  · have haf := positive_product_four z.a z.f ha hf
    have hcd := positive_product_four z.c z.d hc hd
    rcases le_total z.a z.d with had | hda
    · left
      rw [mu1_drop_iff]
      simp only [hb,mul_one,abs_of_nonneg (by omega : 0≤z.d),
        abs_of_nonneg (by omega : 0≤z.e),abs_of_nonpos (by omega : z.a-z.d≤0)]
      have hmul := mul_nonneg (by omega : 0≤z.d-z.a) (by omega : 0≤z.c)
      have hq : z.a*z.f+z.c*z.d-z.e≤4 := by
        rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> omega
      have hh : |z.a*z.c-z.e|<z.a+z.e := by
        apply abs_lt.mpr
        constructor <;> nlinarith
      linarith
    · right
      left
      rw [inv2_drop_iff]
      simp only [hb,one_mul,abs_of_nonneg (by omega : 0≤z.a),
        abs_of_nonneg (by omega : 0≤z.e),abs_of_nonpos (by omega : z.d-z.a≤0)]
      have hmul := mul_nonneg (by omega : 0≤z.a-z.d) (by omega : 0≤z.f)
      have hq : z.a*z.f+z.c*z.d-z.e≤4 := by
        rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> omega
      have hh : |z.d*z.f-z.e|<z.d+z.e := by
        apply abs_lt.mpr
        constructor <;> nlinarith
      have heq : |z.d-z.a|=z.a-z.d := by rw [abs_of_nonpos (by omega : z.d-z.a≤0)]; ring
      linarith
  · left
    by_contra hm
    rw [mu1_drop_iff] at hm
    simp only [hb,mul_one,abs_of_nonneg (by omega : 0≤z.d),
      abs_of_nonneg (by omega : 0≤z.e)] at hm
    have hac : 0≤z.a*z.c-z.e := by
      by_contra hh
      rw [abs_of_nonpos (by omega : z.a*z.c-z.e≤0)] at hm
      rw [abs_of_nonneg (by omega : 0≤z.d)] at hL
      have hh := mul_nonneg (by omega : 0≤z.a) (by omega : 0≤z.c-1)
      nlinarith
    rw [abs_of_nonneg hac] at hm
    rcases le_total z.a z.d with had | hda
    · rw [abs_of_nonpos (by omega : z.a-z.d≤0)] at hm
      exact phase_forbidden_le z hz hb ha hc he had hf (by linarith)
    · rw [abs_of_nonneg (by omega : 0≤z.a-z.d)] at hm
      exact phase_forbidden_ge z hz hb ha hc he hd hda hf (by linarith)
  · right
    right
    exact opposed_forward_descent z hz hb ha hc he hd hf
  · have haf := positive_product_four z.a (-z.f) ha (by omega)
    have hcd := positive_product_four z.c (-z.d) hc (by omega)
    rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> nlinarith

private theorem positive_phase_word (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c) (he : 2≤z.e)
    (hd : 2≤|z.d|) (hf : 2≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  rcases unit_b_positive_phase z hz hb ha hc he hd hf with h|h|h
  · exact ⟨[.m1],by simpa [applyWord,step] using h⟩
  · exact ⟨[.i2],by simpa [applyWord,step] using h⟩
  · exact ⟨[.m1,.m2],h⟩
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- Normalize the unit diagonal and both first-row signs. A negative crossing
coefficient is handled by two exact height-preserving cycles and a vertex gauge. -/
theorem unit_b_normalized_two_descent (z : Six) (hz : isSolution z)
    (hb : z.b=1) (ha : 2≤z.a) (hc : 2≤z.c)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  have hd' : 2≤z.d ∨ z.d≤-2 := by rcases le_abs.mp hd with h|h <;> omega
  have he' : 2≤z.e ∨ z.e≤-2 := by rcases le_abs.mp he with h|h <;> omega
  have hf' : 2≤z.f ∨ z.f≤-2 := by rcases le_abs.mp hf with h|h <;> omega
  rcases he' with he|he
  · obtain ⟨word,hdrop⟩ := positive_phase_word z hz hb ha hc he hd hf
    exact ⟨word,hdrop⟩
  · rcases hd' with hd|hd <;> rcases hf' with hf|hf
    · have haf := positive_product_four z.a z.f ha hf
      have hcd := positive_product_four z.c z.d hc hd
      rcases solution_q2_cases z hz with h|h <;> simp only [q2,hb,one_mul] at h <;> nlinarith
    · let w := CyclicMutation.cyclePower z 2
      let v := eps2 w
      have hwsol : isSolution w := CyclicMutation.cyclePower_solution z hz 2
      have hvsol : isSolution v := reachable_preserves_solution ⟨[.s2],rfl⟩ hwsol
      obtain ⟨word,hdrop⟩ := positive_phase_word v hvsol
        (by simp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle,hb])
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by
          dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.c)] using hc)
        (by
          dsimp [v,w,eps2,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.a)] using ha)
      let t : Fin 4 → ℤ := ![1,-1,1,1]
      have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> simp [t]
      have htv : PositiveNormalization.signedSix w t=v := by
        ext <;> simp [PositiveNormalization.signedSix,v,eps2,t]
      have hwDrop : l1 (applyWord w word)<l1 w :=
        SignGaugeDescent.descent_transfer w t ht word (by simpa only [htv] using hdrop)
      exact ⟨CyclicMutation.cycleWord 2 ++ word,CyclicMutation.word_descent_transfer z 2 word hwDrop⟩
    · let w := CyclicMutation.cyclePower z 2
      let v := eps4 w
      have hwsol : isSolution w := CyclicMutation.cyclePower_solution z hz 2
      have hvsol : isSolution v := reachable_preserves_solution ⟨[.s4],rfl⟩ hwsol
      obtain ⟨word,hdrop⟩ := positive_phase_word v hvsol
        (by simp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle,hb])
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]; omega)
        (by
          dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.c)] using hc)
        (by
          dsimp [v,w,eps4,CyclicMutation.cyclePower,CyclicMutation.cycle]
          simpa [abs_of_nonneg (by omega : 0≤z.a)] using ha)
      let t : Fin 4 → ℤ := ![1,1,1,-1]
      have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> simp [t]
      have htv : PositiveNormalization.signedSix w t=v := by
        ext <;> simp [PositiveNormalization.signedSix,v,eps4,t]
      have hwDrop : l1 (applyWord w word)<l1 w :=
        SignGaugeDescent.descent_transfer w t ht word (by simpa only [htv] using hdrop)
      exact ⟨CyclicMutation.cycleWord 2 ++ word,CyclicMutation.word_descent_transfer z 2 word hwDrop⟩
    · have hsum := SignChambers.q1_ge_square_sum_of_negative_tail z
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hz.1] at hsum
      nlinarith [sq_nonneg (z.a-2),sq_nonneg z.b,sq_nonneg z.c,
        sq_nonneg z.d,sq_nonneg z.e,sq_nonneg z.f,sq_nonneg (z.c-2)]

/-- A unit in the crossing position has strict original-height descent,
without any initial height-increasing transport. -/
theorem unit_b_two_descent (z : Six) (hz : isSolution z)
    (hb : |z.b|=1) (ha : 2≤|z.a|) (hc : 2≤|z.c|)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  obtain ⟨s,hs,ha',hb',hc',hr,hl⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  obtain ⟨habsA,habsB,habsC,habsD,habsE,habsF⟩ := SignGaugeDescent.signedSix_abs z s hs
  obtain ⟨word,hdrop⟩ := unit_b_normalized_two_descent (PositiveNormalization.signedSix z s)
    (reachable_preserves_solution hr hz) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  exact ⟨word,SignGaugeDescent.descent_transfer z s hs word hdrop⟩

/-- The other crossing position is brought to `b` by one height-preserving
actual cycle. -/
theorem unit_e_two_descent (z : Six) (hz : isSolution z)
    (he : |z.e|=1) (ha : 2≤|z.a|) (hb : 2≤|z.b|)
    (hc : 2≤|z.c|) (hd : 2≤|z.d|) (hf : 2≤|z.f|) :
    ∃ word : List Generator, l1 (applyWord z word)<l1 z := by
  obtain ⟨word,hdrop⟩ := unit_b_two_descent (CyclicMutation.cyclePower z 1)
    (CyclicMutation.cyclePower_solution z hz 1)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using he)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using ha)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hb)
    (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
  exact ⟨CyclicMutation.cycleWord 1 ++ word,CyclicMutation.word_descent_transfer z 1 word hdrop⟩

/-- A unique unit diagonal with all other edges at least two strictly descends. -/
theorem unit_b_two_family_or_drop (z : Six) (hz : isSolution z)
    (hb : |z.b|=1) (ha : 2≤|z.a|) (hc : 2≤|z.c|)
    (hd : 2≤|z.d|) (he : 2≤|z.e|) (hf : 2≤|z.f|) :
    NegativeTwoEdge.FamilyOrDrop z :=
  Or.inr (unit_b_two_descent z hz hb ha hc hd he hf)

/-- The other diagonal is carried to the first by a height-preserving cycle. -/
theorem unit_e_two_family_or_drop (z : Six) (hz : isSolution z)
    (he : |z.e|=1) (ha : 2≤|z.a|) (hb : 2≤|z.b|)
    (hc : 2≤|z.c|) (hd : 2≤|z.d|) (hf : 2≤|z.f|) :
    NegativeTwoEdge.FamilyOrDrop z :=
  Or.inr (unit_e_two_descent z hz he ha hb hc hd hf)

end SerreMarkov.NegativeDiagonalUnitTwo
