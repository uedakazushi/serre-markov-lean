import SerreMarkov.PositiveSortedTerminal
import SerreMarkov.PositiveTriangleLower

/-! Nonnegative guards for the ordered large-edge terminal certificate. -/
namespace SerreMarkov.PositiveSortedLarge
open PositiveChamber PositiveShortWord PositiveSortedTerminal NegativeDescent
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem braid_word_chamber (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) : Chamber (applyWord z word) := by
  exact applyWord_preserves_chamber z hz word
    (fun g hg => braidMoves_isBraid (hw g hg))

theorem word_height_nonnegative (z : Six) (hz : Chamber z) (ht : AllTerminal z)
    (word : List Generator) (hw : ∀ g∈word, g∈braidMoves) :
    0≤heightPolynomial z word := by
  apply (shortTerminal_iff_polynomial z hz word.length).mp (ht word.length)
  exact (mem_braidWords_iff _ _).mpr ⟨le_refl _,hw⟩

theorem word_coordinates (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) : Coordinates (applyWord z word) :=
  (braid_word_chamber z hz word hw).2.2

theorem word_triangle_bounds (z : Six) (hz : Chamber z) (word : List Generator)
    (hw : ∀ g∈word, g∈braidMoves) :
    triangleDefect (applyWord z word).a (applyWord z word).b (applyWord z word).d≤ -7 ∧
    triangleDefect (applyWord z word).a (applyWord z word).c (applyWord z word).e≤ -7 ∧
    triangleDefect (applyWord z word).b (applyWord z word).c (applyWord z word).f≤ -7 ∧
    triangleDefect (applyWord z word).d (applyWord z word).e (applyWord z word).f≤ -7 :=
  PositiveTriangleLower.chamber_all_triangle_bounds _ (braid_word_chamber z hz word hw)

theorem marker_nonnegative (z : Six) (hz : Chamber z) :
    0≤IntrinsicSigns.thirdMinorSum z-2 := by
  have h := hz.2.1
  dsimp [IntrinsicSigns.thirdMinorSum] at h ⊢
  omega

theorem normalized_nonnegative (n G R : ℤ) (hn : 0<n) (hR : 0≤R)
    (heq : R=n*G) : 0≤G := by
  have h : 0≤n*G := heq ▸ hR
  exact (mul_nonneg_iff_of_pos_left hn).mp h

set_option linter.unusedVariables false

def guard0 (A B C D E F : ℤ) : ℤ := 1*A+3
theorem guard0_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard0 A B C D E F := by
  have hc := word_coordinates _ hz [] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a-3 := by linarith only [hc.1]
  have heq : guard0 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a-3 := by
    dsimp only [guard0,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard1 (A B C D E F : ℤ) : ℤ := 1*A+1*D+3
theorem guard1_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard1 A B C D E F := by
  have hc := word_coordinates _ hz [] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).d-3 := by linarith only [hc.2.2.2.1]
  have heq : guard1 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).d-3 := by
    dsimp only [guard1,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard2 (A B C D E F : ℤ) : ℤ := 1*A+1*F+3
theorem guard2_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard2 A B C D E F := by
  have hc := word_coordinates _ hz [] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).f-3 := by linarith only [hc.2.2.2.2.2]
  have heq : guard2 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).f-3 := by
    dsimp only [guard2,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard3 (A B C D E F : ℤ) : ℤ := 1*A^2*B+2*A^2+12*A*B-1*A*D+24*A+35*B-6*D+66
theorem guard3_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard3 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1]).b-3 := by linarith only [hc.2.1]
  have heq : guard3 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1]).b-3 := by
    dsimp only [guard3,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard4 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+1*A^2*D+18*A^2+12*A*C+12*A*D-1*A*E+104*A+35*C+35*D-6*E+189
theorem guard4_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard4 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard4 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1]).c-3 := by
    dsimp only [guard4,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard5 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*C+1*A^3*D+24*A^3+18*A^2*C+18*A^2*D-1*A^2*E+211*A^2+106*A*C+106*A*D-12*A*E+804*A+204*C+204*D-35*E+1116
theorem guard5_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard5 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m1,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard5 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1]).c-3 := by
    dsimp only [guard5,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard6 (A B C D E F : ℤ) : ℤ := 1*A^4*B+2*A^4+24*A^3*B-1*A^3*D+48*A^3+213*A^2*B-18*A^2*D+425*A^2+828*A*B-106*A*D+1644*A+1189*B-204*D+2340
theorem guard6_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard6 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m1,.m1,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1,.m1]).b-3 := by linarith only [hc.2.1]
  have heq : guard6 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1,.m1]).b-3 := by
    dsimp only [guard6,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard7 (A B C D E F : ℤ) : ℤ := 1*A*B+2*A+1*B*C+1*B*D+6*B+3*C+3*D-1*F+9
theorem guard7_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard7 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard7 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2]).e-3 := by
    dsimp only [guard7,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard8 (A B C D E F : ℤ) : ℤ := 1*A^2*B+1*A^2+1*A*B*C+2*A*B*D+12*A*B+2*A*C+4*A*D-1*A*F+12*A+1*B*C*D+6*B*C+1*B*D^2+12*B*D+36*B+3*C*D+12*C+3*D^2-1*D*F+24*D+1*E-6*F+36
theorem guard8_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard8 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.m2,.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i1]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard8 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i1]).e-3 := by
    dsimp only [guard8,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard9 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+1*A^2*D+1*A^2*F+18*A^2-1*A*B+1*A*C*F+12*A*C+1*A*D*F+12*A*D-1*A*E+12*A*F+103*A-6*B+6*C*F+36*C+6*D*F+37*D-1*E*F-6*E+33*F+183
theorem guard9_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard9 A B C D E F := by
  have hc := word_coordinates _ hz [.m1,.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard9 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3]).c-3 := by
    dsimp only [guard9,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard10 (A B C D E F : ℤ) : ℤ := 1*A*B+2*A+6*B-1*D+9
theorem guard10_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard10 A B C D E F := by
  have hc := word_coordinates _ hz [.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1]).b-3 := by linarith only [hc.2.1]
  have heq : guard10 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1]).b-3 := by
    dsimp only [guard10,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard11 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*C+1*A*D+12*A+6*C+6*D-1*E+30
theorem guard11_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard11 A B C D E F := by
  have hc := word_coordinates _ hz [.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard11 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1]).c-3 := by
    dsimp only [guard11,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard12 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*D+18*A^2-1*A*B+12*A*D+104*A-6*B+35*D+189
theorem guard12_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard12 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1]).d-3 := by linarith only [hc.2.2.2.1]
  have heq : guard12 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1]).d-3 := by
    dsimp only [guard12,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard13 (A B C D E F : ℤ) : ℤ := 1*A^2*E+2*A^2-1*A*C-1*A*D+12*A*E+24*A-6*C-6*D+35*E+66
theorem guard13_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard13 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard13 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1]).e-3 := by
    dsimp only [guard13,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard14 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+24*A^3-1*A^2*B+18*A^2*D+211*A^2-12*A*B+106*A*D+804*A-35*B+204*D+1116
theorem guard14_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard14 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i1,.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1]).d-3 := by linarith only [hc.2.2.2.1]
  have heq : guard14 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1]).d-3 := by
    dsimp only [guard14,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard15 (A B C D E F : ℤ) : ℤ := 1*A^3*E+2*A^3-1*A^2*C-1*A^2*D+18*A^2*E+36*A^2-12*A*C-12*A*D+106*A*E+211*A-35*C-35*D+204*E+399
theorem guard15_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard15 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i1,.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard15 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1]).e-3 := by
    dsimp only [guard15,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard16 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+1*A^3*F+24*A^3-1*A^2*B+1*A^2*D*F+18*A^2*D-1*A^2*E+18*A^2*F+210*A^2-1*A*B*F-12*A*B+1*A*C+12*A*D*F+108*A*D-12*A*E+104*A*F+792*A-6*B*F-36*B+6*C+35*D*F+216*D-35*E+192*F+1080
theorem guard16_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard16 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i1,.i2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i2]).f-3 := by linarith only [hc.2.2.2.2.2]
  have heq : guard16 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i2]).f-3 := by
    dsimp only [guard16,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard17 (A B C D E F : ℤ) : ℤ := 1*A^3+2*A^2*D+18*A^2-1*A*B+1*A*D^2+24*A*D+104*A-1*B*D-6*B+6*D^2+69*D+189
theorem guard17_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard17 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2]).b-3 := by linarith only [hc.2.1]
  have heq : guard17 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2]).b-3 := by
    dsimp only [guard17,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard18 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*D+1*A^2*F+18*A^2-1*A*B+1*A*D*F+12*A*D-1*A*E+12*A*F+103*A-1*B*F-6*B+1*C+6*D*F+37*D-6*E+33*F+183
theorem guard18_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard18 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2]).f-3 := by linarith only [hc.2.2.2.2.2]
  have heq : guard18 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2]).f-3 := by
    dsimp only [guard18,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard19 (A B C D E F : ℤ) : ℤ := 1*A^4+3*A^3*D+24*A^3-1*A^2*B+3*A^2*D^2+54*A^2*D+211*A^2-2*A*B*D-12*A*B+1*A*D^3+36*A*D^2+316*A*D+804*A-1*B*D^2-12*B*D-35*B+6*D^3+105*D^2+600*D+1116
theorem guard19_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard19 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i2,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1]).b-3 := by linarith only [hc.2.1]
  have heq : guard19 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1]).b-3 := by
    dsimp only [guard19,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard20 (A B C D E F : ℤ) : ℤ := 1*A^5+4*A^4*D+30*A^4-1*A^3*B+6*A^3*D^2+96*A^3*D+354*A^3-3*A^2*B*D-18*A^2*B+4*A^2*D^3+108*A^2*D^2+849*A^2*D+2052*A^2-3*A*B*D^2-36*A*B*D-106*A*B+1*A*D^4+48*A*D^3+636*A*D^2+3276*A*D+5839*A-1*B*D^3-18*B*D^2-106*B*D-204*B+6*D^4+141*D^3+1224*D^2+4650*D+6519
theorem guard20_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard20 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i2,.m1,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1,.m1]).b-3 := by linarith only [hc.2.1]
  have heq : guard20 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1,.m1]).b-3 := by
    dsimp only [guard20,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard21 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+2*A^3*F+24*A^3-1*A^2*B+2*A^2*D*F+18*A^2*D-1*A^2*E+1*A^2*F^2+36*A^2*F+210*A^2-2*A*B*F-12*A*B+1*A*C+1*A*D*F^2+24*A*D*F+108*A*D-1*A*E*F-12*A*E+12*A*F^2+208*A*F+792*A-1*B*F^2-12*B*F-35*B+1*C*F+6*C+6*D*F^2+73*D*F+216*D-6*E*F-36*E+33*F^2+384*F+1080
theorem guard21_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard21 A B C D E F := by
  have hc := word_coordinates _ hz [.i1,.i2,.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.i3]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard21 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.i3]).e-3 := by
    dsimp only [guard21,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard22 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+12*A-1*B+6*D+30
theorem guard22_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard22 A B C D E F := by
  have hc := word_coordinates _ hz [.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1]).d-3 := by linarith only [hc.2.2.2.1]
  have heq : guard22 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1]).d-3 := by
    dsimp only [guard22,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard23 (A B C D E F : ℤ) : ℤ := 1*A*E+2*A-1*C-1*D+6*E+9
theorem guard23_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard23 A B C D E F := by
  have hc := word_coordinates _ hz [.i1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard23 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1]).e-3 := by
    dsimp only [guard23,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard24 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+2*A^2*D+18*A^2-1*A*B+1*A*C*D+12*A*C+1*A*D^2+24*A*D-1*A*E+103*A-1*B*C-1*B*D-6*B+6*C*D+33*C+6*D^2-1*D*E+66*D-6*E+1*F+183
theorem guard24_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard24 A B C D E F := by
  have hc := word_coordinates _ hz [.m2,.m1] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard24 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1]).c-3 := by
    dsimp only [guard24,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard25 (A B C D E F : ℤ) : ℤ := 1*A^3*E+2*A^3+1*A^2*C*E+3*A^2*C+2*A^2*D*E+5*A^2*D+18*A^2*E+36*A^2-1*A*B*E-2*A*B+1*A*C*D*E+3*A*C*D+12*A*C*E+36*A*C+1*A*D^2*E+3*A*D^2+24*A*D*E+60*A*D-1*A*E^2+100*A*E+205*A-1*B*C*E-3*B*C-1*B*D*E-3*B*D-6*B*E-12*B+6*C*D*E+18*C*D+33*C*E+99*C+6*D^2*E+18*D^2-1*D*E^2+63*D*E+163*D-6*E^2+1*E*F+168*E+3*F+363
theorem guard25_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard25 A B C D E F := by
  have hc := word_coordinates _ hz [.m2,.m1,.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard25 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3]).c-3 := by
    dsimp only [guard25,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard26 (A B C D E F : ℤ) : ℤ := 1*A^2*E+2*A^2+2*A*D*E+5*A*D+12*A*E-1*A*F+24*A+1*D^2*E+3*D^2+12*D*E-1*D*F+30*D+35*E-6*F+66
theorem guard26_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard26 A B C D E F := by
  have hc := word_coordinates _ hz [.m2,.m2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m2]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard26 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m2]).e-3 := by
    dsimp only [guard26,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard27 (A B C D E F : ℤ) : ℤ := 1*A*E+2*A+1*C*E+3*C+1*D*E+3*D+6*E+9
theorem guard27_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard27 A B C D E F := by
  have hc := word_coordinates _ hz [.m2,.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard27 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3]).c-3 := by
    dsimp only [guard27,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard28 (A B C D E F : ℤ) : ℤ := 1*A*E+2*A+1*D*E+3*D+6*E-1*F+9
theorem guard28_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard28 A B C D E F := by
  have hc := word_coordinates _ hz [.m2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard28 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2]).e-3 := by
    dsimp only [guard28,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard29 (A B C D E F : ℤ) : ℤ := 1*A*B+2*A+1*B*D+6*B+3*D+9
theorem guard29_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard29 A B C D E F := by
  have hc := word_coordinates _ hz [.i2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2]).b-3 := by linarith only [hc.2.1]
  have heq : guard29 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2]).b-3 := by
    dsimp only [guard29,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard30 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+1*A*F+12*A+1*D*F+6*D-1*E+6*F+30
theorem guard30_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard30 A B C D E F := by
  have hc := word_coordinates _ hz [.i2] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2]).f-3 := by linarith only [hc.2.2.2.2.2]
  have heq : guard30 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2]).f-3 := by
    dsimp only [guard30,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard31 (A B C D E F : ℤ) : ℤ := 1*A*B+2*A+1*B*F+6*B-1*C-1*D+3*F+9
theorem guard31_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard31 A B C D E F := by
  have hc := word_coordinates _ hz [.m3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3]).b-3 := by linarith only [hc.2.1]
  have heq : guard31 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3]).b-3 := by
    dsimp only [guard31,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard32 (A B C D E F : ℤ) : ℤ := 1*A^2*E+2*A^2-1*A*D+2*A*E*F+12*A*E+5*A*F+24*A-1*D*F-6*D+1*E*F^2+12*E*F+35*E+3*F^2+30*F+66
theorem guard32_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard32 A B C D E F := by
  have hc := word_coordinates _ hz [.i3,.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3,.i3]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard32 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3,.i3]).e-3 := by
    dsimp only [guard32,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard33 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*C+1*A*D+1*A*F+12*A-1*B+1*C*F+6*C+1*D*F+6*D+6*F+30
theorem guard33_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard33 A B C D E F := by
  have hc := word_coordinates _ hz [.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3]).c-3 := by linarith only [hc.2.2.1]
  have heq : guard33 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3]).c-3 := by
    dsimp only [guard33,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard34 (A B C D E F : ℤ) : ℤ := 1*A*E+2*A-1*D+1*E*F+6*E+3*F+9
theorem guard34_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard34 A B C D E F := by
  have hc := word_coordinates _ hz [.i3] (by decide +kernel)
  have hr : 0≤(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3]).e-3 := by linarith only [hc.2.2.2.2.1]
  have heq : guard34 A B C D E F=(applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3]).e-3 := by
    dsimp only [guard34,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard35 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*B+1*A^2*C+1*A^2*D+21*A^2+13*A*B+13*A*C+12*A*D-1*A*E+140*A+40*B+40*C+32*D-8*E+288
theorem guard35_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard35 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1] := word_height_nonnegative _ hz ht [.m1,.m1] (by decide +kernel)
  have heq : guard35 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1] := by
    dsimp only [guard35,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard36 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*B+1*A^3*C+1*A^3*D+27*A^3+19*A^2*B+19*A^2*C+18*A^2*D-1*A^2*E+267*A^2+118*A*B+118*A*C+105*A*D-13*A*E+1141*A+238*B+238*C+196*D-42*E+1764
theorem guard36_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard36 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1] := word_height_nonnegative _ hz ht [.m1,.m1,.m1] (by decide +kernel)
  have heq : guard36 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1] := by
    dsimp only [guard36,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard37 (A B C D E F : ℤ) : ℤ := 1*A^5+1*A^4*B+1*A^4*C+1*A^4*D+33*A^4+25*A^3*B+25*A^3*C+24*A^3*D-1*A^3*E+428*A^3+231*A^2*B+231*A^2*C+212*A^2*D-19*A^2*E+2724*A^2+934*A*B+934*A*C+816*A*D-118*A*E+8496*A+1392*B+1392*C+1152*D-240*E+10368
theorem guard37_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard37 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1,.m1] := word_height_nonnegative _ hz ht [.m1,.m1,.m1,.m1] (by decide +kernel)
  have heq : guard37 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m1,.m1] := by
    dsimp only [guard37,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard38 (A B C D E F : ℤ) : ℤ := 2*A^3+2*A^2*C+3*A^2*D+37*A^2-1*A*B+1*A*C*D+25*A*C+1*A*D^2+37*A*D-2*A*E+217*A-1*B*C-1*B*D-6*B+6*C*D+73*C+6*D^2-1*D*E+106*D-14*E+396
theorem guard38_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard38 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m2,.m1] := word_height_nonnegative _ hz ht [.m1,.m1,.m2,.m1] (by decide +kernel)
  have heq : guard38 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m2,.m1] := by
    dsimp only [guard38,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard39 (A B C D E F : ℤ) : ℤ := 1*A^3*B+1*A^3+1*A^2*B*F+20*A^2*B-1*A^2*C-2*A^2*D+2*A^2*F+21*A^2+13*A*B*F+132*A*B-13*A*C-1*A*D*F-27*A*D+1*A*E+26*A*F+145*A+41*B*F+286*B-42*C-7*D*F-92*D+6*E+81*F+324
theorem guard39_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard39 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m3] := word_height_nonnegative _ hz ht [.m1,.m1,.m3] (by decide +kernel)
  have heq : guard39 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.m3] := by
    dsimp only [guard39,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard40 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*C+1*A^3*D+1*A^3*F+26*A^3-1*A^2*B+1*A^2*C*F+20*A^2*C+1*A^2*D*F+20*A^2*D-1*A^2*E+19*A^2*F+247*A^2-13*A*B+13*A*C*F+132*A*C+13*A*D*F+133*A*D-1*A*E*F-14*A*E+116*A*F+1009*A-42*B+41*C*F+286*C+41*D*F+292*D-7*E*F-50*E+225*F+1476
theorem guard40_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard40 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.i3] := word_height_nonnegative _ hz ht [.m1,.m1,.i3] (by decide +kernel)
  have heq : guard40 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.i3] := by
    dsimp only [guard40,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard41 (A B C D E F : ℤ) : ℤ := 1*A^5+2*A^4*C+2*A^4*D+31*A^4+1*A^3*C^2+2*A^3*C*D+49*A^3*C+1*A^3*D^2+49*A^3*D-2*A^3*E+1*A^3*F+378*A^3-1*A^2*B+18*A^2*C^2+36*A^2*C*D-2*A^2*C*E+1*A^2*C*F+443*A^2*C+18*A^2*D^2-2*A^2*D*E+1*A^2*D*F+443*A^2*D-37*A^2*E+18*A^2*F+2263*A^2-11*A*B+107*A*C^2+214*A*C*D-24*A*C*E+12*A*C*F+1752*A*C+107*A*D^2-24*A*D*E+12*A*D*F+1753*A*D+1*A*E^2-1*A*E*F-222*A*E+104*A*F+6642*A-30*B+210*C^2+420*C*D-71*C*E+35*C*F+2557*C+210*D^2-71*D*E+35*D*F+2561*D+6*E^2-6*E*F-434*E+192*F+7626
theorem guard41_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard41 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.i3,.i2] := word_height_nonnegative _ hz ht [.m1,.m1,.i3,.i2] (by decide +kernel)
  have heq : guard41 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m1,.i3,.i2] := by
    dsimp only [guard41,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard42 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B+1*A*C+1*A*D+13*A+1*B*C+1*B*D+6*B+9*C+9*D-2*E-2*F+36
theorem guard42_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard42 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2] := word_height_nonnegative _ hz ht [.m1,.m2] (by decide +kernel)
  have heq : guard42 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2] := by
    dsimp only [guard42,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard43 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+2*A^2*D+20*A^2-1*A*B+1*A*C*D+13*A*C+1*A*D^2+26*A*D-1*A*E+126*A-1*B*C-1*B*D-8*B+6*C*D+39*C+6*D^2-1*D*E+78*D-8*E+240
theorem guard43_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard43 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1] := word_height_nonnegative _ hz ht [.m1,.m2,.m1] (by decide +kernel)
  have heq : guard43 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1] := by
    dsimp only [guard43,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard44 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*C+3*A^3*D+26*A^3-1*A^2*B+2*A^2*C*D+19*A^2*C+3*A^2*D^2+58*A^2*D-1*A^2*E+247*A^2-1*A*B*C-2*A*B*D-14*A*B+1*A*C*D^2+25*A*C*D+116*A*C+1*A*D^3+38*A*D^2-2*A*D*E+361*A*D-13*A*E+1*A*F+1009*A-1*B*C*D-7*B*C-1*B*D^2-14*B*D-50*B+6*C*D^2+75*C*D+225*C+6*D^3-1*D^2*E+114*D^2-13*D*E+1*D*F+717*D-42*E+6*F+1476
theorem guard44_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard44 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1,.m1] := word_height_nonnegative _ hz ht [.m1,.m2,.m1,.m1] (by decide +kernel)
  have heq : guard44 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1,.m1] := by
    dsimp only [guard44,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard45 (A B C D E F : ℤ) : ℤ := 1*A^4+2*A^3*C+3*A^3*D+26*A^3-1*A^2*B+1*A^2*C^2+4*A^2*C*D+39*A^2*C+3*A^2*D^2+58*A^2*D-1*A^2*E+247*A^2-2*A*B*C-2*A*B*D-13*A*B+1*A*C^2*D+13*A*C^2+2*A*C*D^2+51*A*C*D-1*A*C*E+245*A*C+1*A*D^3+38*A*D^2-2*A*D*E+361*A*D-14*A*E+1*A*F+1009*A-1*B*C^2-2*B*C*D-13*B*C-1*B*D^2-13*B*D-42*B+6*C^2*D+39*C^2+12*C*D^2-1*C*D*E+153*C*D-7*C*E+1*C*F+492*C+6*D^3-1*D^2*E+114*D^2-14*D*E+1*D*F+717*D-50*E+6*F+1476
theorem guard45_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard45 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1,.i3] := word_height_nonnegative _ hz ht [.m1,.m2,.m1,.i3] (by decide +kernel)
  have heq : guard45 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m1,.i3] := by
    dsimp only [guard45,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard46 (A B C D E F : ℤ) : ℤ := 1*A^2*B+1*A^2+1*A*B*C+2*A*B*D+14*A*B+2*A*C+4*A*D-1*A*F+14*A+1*B*C*D+7*B*C+1*B*D^2+14*B*D+48*B+3*C*D+15*C+3*D^2-1*D*F+30*D-8*F+48
theorem guard46_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard46 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i1] := word_height_nonnegative _ hz ht [.m1,.m2,.i1] (by decide +kernel)
  have heq : guard46 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i1] := by
    dsimp only [guard46,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard47 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B^2+7*A*B+1*A*C+1*A*D+18*A+1*B^2*C+1*B^2*D+6*B^2+7*B*C+8*B*D-1*B*F+42*B+16*C+19*D-2*E-5*F+66
theorem guard47_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard47 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m2] := word_height_nonnegative _ hz ht [.m1,.m2,.m2] (by decide +kernel)
  have heq : guard47 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m2] := by
    dsimp only [guard47,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard48 (A B C D E F : ℤ) : ℤ := 1*A^3*B+2*A^3+1*A^2*B*C+2*A^2*B*D+19*A^2*B+2*A^2*C+5*A^2*D+39*A^2-1*A*B^2+1*A*B*C*D+12*A*B*C+1*A*B*D^2+26*A*B*D-1*A*B*E+114*A*B+3*A*C*D+25*A*C+3*A*D^2+66*A*D-2*A*E+242*A-1*B^2*C-1*B^2*D-6*B^2+6*B*C*D+31*B*C+7*B*D^2-1*B*D*E+77*B*D-6*B*E+1*B*F+214*B+18*C*D+72*C+21*D^2-3*D*E+204*D-14*E+1*F+468
theorem guard48_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard48 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m2,.m1] := word_height_nonnegative _ hz ht [.m1,.m2,.m2,.m1] (by decide +kernel)
  have heq : guard48 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.m2,.m1] := by
    dsimp only [guard48,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard49 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*B+2*A^2*C+2*A^2*D+21*A^2+2*A*B*C+2*A*B*D+13*A*B+1*A*C^2+2*A*C*D+30*A*C+1*A*D^2+30*A*D-1*A*E-1*A*F+140*A+1*B*C^2+2*B*C*D+13*B*C+1*B*D^2+13*B*D+40*B+9*C^2+18*C*D-1*C*E-1*C*F+108*C+9*D^2-1*D*E-1*D*F+108*D-8*E-8*F+288
theorem guard49_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard49 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i3] := word_height_nonnegative _ hz ht [.m1,.m2,.i3] (by decide +kernel)
  have heq : guard49 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m2,.i3] := by
    dsimp only [guard49,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard50 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B^2+7*A*B+1*A*C+1*A*D+18*A+6*B^2-1*B*D+1*B*F+42*B+4*C-1*D-2*E+3*F+66
theorem guard50_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard50 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i2] := word_height_nonnegative _ hz ht [.m1,.i2] (by decide +kernel)
  have heq : guard50 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i2] := by
    dsimp only [guard50,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard51 (A B C D E F : ℤ) : ℤ := 1*A^3*B+3*A^3+1*A^2*B*C+1*A^2*B*D+1*A^2*B*F+18*A^2*B+2*A^2*C+2*A^2*D+4*A^2*F+55*A^2-1*A*B^2+1*A*B*C*F+12*A*B*C+1*A*B*D*F+12*A*B*D-1*A*B*E+12*A*B*F+100*A*B-1*A*C^2-2*A*C*D+4*A*C*F+25*A*C-1*A*D^2+4*A*D*F+25*A*D-3*A*E+48*A*F+319*A-6*B^2+6*B*C*F+36*B*C+6*B*D*F+37*B*D-1*B*E*F-6*B*E+34*B*F+168*B-6*C^2-12*C*D+1*C*E+24*C*F+79*C-6*D^2+1*D*E+24*D*F+82*D-4*E*F-20*E+135*F+576
theorem guard51_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard51 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i2,.i3,.i2] := word_height_nonnegative _ hz ht [.m1,.i2,.i3,.i2] (by decide +kernel)
  have heq : guard51 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i2,.i3,.i2] := by
    dsimp only [guard51,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard52 (A B C D E F : ℤ) : ℤ := 1*A^2*B+1*A^2+1*A*B*F+14*A*B-1*A*C-2*A*D+2*A*F+14*A+7*B*F+48*B-8*C-1*D*F-16*D+15*F+48
theorem guard52_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard52 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m3] := word_height_nonnegative _ hz ht [.m1,.m3] (by decide +kernel)
  have heq : guard52 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.m3] := by
    dsimp only [guard52,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard53 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+1*A^2*D+1*A^2*F+20*A^2-1*A*B+1*A*C*F+14*A*C+1*A*D*F+14*A*D-1*A*E+13*A*F+126*A-8*B+7*C*F+48*C+7*D*F+48*D-1*E*F-8*E+39*F+240
theorem guard53_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard53 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3] := word_height_nonnegative _ hz ht [.m1,.i3] (by decide +kernel)
  have heq : guard53 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3] := by
    dsimp only [guard53,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard54 (A B C D E F : ℤ) : ℤ := 2*A^3+3*A^2*C+3*A^2*D+1*A^2*F+37*A^2-1*A*B+1*A*C^2+2*A*C*D+1*A*C*F+37*A*C+1*A*D^2+1*A*D*F+37*A*D-2*A*E+12*A*F+217*A-6*B+6*C^2+12*C*D-1*C*E+6*C*F+111*C+6*D^2-1*D*E+6*D*F+111*D-1*E*F-14*E+33*F+396
theorem guard54_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard54 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3,.i2] := word_height_nonnegative _ hz ht [.m1,.i3,.i2] (by decide +kernel)
  have heq : guard54 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1,.i3,.i2] := by
    dsimp only [guard54,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard55 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B+1*A*C+1*A*D+13*A+6*B+6*C+4*D-2*E+36
theorem guard55_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard55 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1] := word_height_nonnegative _ hz ht [.m1] (by decide +kernel)
  have heq : guard55 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m1] := by
    dsimp only [guard55,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard56 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*D+1*A^2*E+21*A^2-1*A*B-1*A*C+12*A*D+13*A*E+140*A-8*B-8*C+32*D+40*E+288
theorem guard56_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard56 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1] := word_height_nonnegative _ hz ht [.i1,.i1] (by decide +kernel)
  have heq : guard56 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1] := by
    dsimp only [guard56,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard57 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+1*A^3*E+27*A^3-1*A^2*B-1*A^2*C+18*A^2*D+19*A^2*E+267*A^2-13*A*B-13*A*C+105*A*D+118*A*E+1141*A-42*B-42*C+196*D+238*E+1764
theorem guard57_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard57 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1] := word_height_nonnegative _ hz ht [.i1,.i1,.i1] (by decide +kernel)
  have heq : guard57 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1] := by
    dsimp only [guard57,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard58 (A B C D E F : ℤ) : ℤ := 1*A^5+1*A^4*D+1*A^4*E+33*A^4-1*A^3*B-1*A^3*C+24*A^3*D+25*A^3*E+428*A^3-19*A^2*B-19*A^2*C+212*A^2*D+231*A^2*E+2724*A^2-118*A*B-118*A*C+816*A*D+934*A*E+8496*A-240*B-240*C+1152*D+1392*E+10368
theorem guard58_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard58 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1,.i1] := word_height_nonnegative _ hz ht [.i1,.i1,.i1,.i1] (by decide +kernel)
  have heq : guard58 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1,.i1] := by
    dsimp only [guard58,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard59 (A B C D E F : ℤ) : ℤ := 1*A^4*E+1*A^4-1*A^3*C-2*A^3*D+1*A^3*E*F+26*A^3*E+2*A^3*F+27*A^3+1*A^2*B-1*A^2*C*F-20*A^2*C-1*A^2*D*F-39*A^2*D+19*A^2*E*F+251*A^2*E+38*A^2*F+272*A^2+13*A*B-13*A*C*F-132*A*C-13*A*D*F-250*A*D+118*A*E*F+1065*A*E+235*A*F+1206*A+40*B-41*C*F-288*C-41*D*F-528*D+239*E*F+1672*E+471*F+1968
theorem guard59_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard59 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1,.i3] := word_height_nonnegative _ hz ht [.i1,.i1,.i1,.i3] (by decide +kernel)
  have heq : guard59 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i1,.i3] := by
    dsimp only [guard59,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard60 (A B C D E F : ℤ) : ℤ := 1*A^5+1*A^4*D+31*A^4-1*A^3*B+25*A^3*D+379*A^3-19*A^2*B+1*A^2*C+233*A^2*D+1*A^2*E+2283*A^2-119*A*B+1*A*C*D+11*A*C+1*A*D^2+957*A*D+12*A*E+6769*A-1*B*C-1*B*D-246*B+6*C*D+25*C+6*D^2-1*D*E+1450*D+34*E+7884
theorem guard60_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard60 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.m2,.m1] := word_height_nonnegative _ hz ht [.i1,.i1,.m2,.m1] (by decide +kernel)
  have heq : guard60 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.m2,.m1] := by
    dsimp only [guard60,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard61 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+1*A^3*F+26*A^3-1*A^2*B+1*A^2*D*F+20*A^2*D-1*A^2*E+19*A^2*F+247*A^2-1*A*B*F-14*A*B+1*A*C+13*A*D*F+133*A*D-13*A*E+116*A*F+1009*A-7*B*F-50*B+6*C+41*D*F+292*D-42*E+225*F+1476
theorem guard61_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard61 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.m3] := word_height_nonnegative _ hz ht [.i1,.i1,.m3] (by decide +kernel)
  have heq : guard61 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.m3] := by
    dsimp only [guard61,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard62 (A B C D E F : ℤ) : ℤ := 1*A^3*E+1*A^3-1*A^2*C-2*A^2*D+1*A^2*E*F+20*A^2*E+2*A^2*F+21*A^2+1*A*B-1*A*C*F-14*A*C-1*A*D*F-27*A*D+13*A*E*F+132*A*E+26*A*F+145*A+6*B-7*C*F-50*C-7*D*F-92*D+41*E*F+286*E+81*F+324
theorem guard62_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard62 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i3] := word_height_nonnegative _ hz ht [.i1,.i1,.i3] (by decide +kernel)
  have heq : guard62 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i1,.i3] := by
    dsimp only [guard62,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard63 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+26*A^3-1*A^2*B+1*A^2*C+21*A^2*D+247*A^2-14*A*B+1*A*C*D+12*A*C+1*A*D^2+142*A*D+1010*A-1*B*C-1*B*D-48*B+6*C*D+31*C+6*D^2-1*D*E+302*D+1488
theorem guard63_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard63 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m2,.m1] := word_height_nonnegative _ hz ht [.i1,.m2,.m1] (by decide +kernel)
  have heq : guard63 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m2,.m1] := by
    dsimp only [guard63,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard64 (A B C D E F : ℤ) : ℤ := 2*A^3+3*A^2*D+1*A^2*F+37*A^2-2*A*B+1*A*D^2+1*A*D*F+37*A*D-1*A*E+12*A*F+217*A-1*B*D-1*B*F-14*B+6*D^2+6*D*F+111*D-6*E+33*F+396
theorem guard64_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard64 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2] := word_height_nonnegative _ hz ht [.i1,.i2] (by decide +kernel)
  have heq : guard64 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2] := by
    dsimp only [guard64,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard65 (A B C D E F : ℤ) : ℤ := 1*A^4+3*A^3*D+26*A^3-1*A^2*B+3*A^2*D^2+57*A^2*D+1*A^2*F+247*A^2-2*A*B*D-14*A*B+1*A*D^3+37*A*D^2+1*A*D*F+352*A*D+12*A*F+1010*A-1*B*D^2-13*B*D-1*B*F-48*B+6*D^3+111*D^2+1*D*E+6*D*F+708*D+31*F+1488
theorem guard65_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard65 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1] := word_height_nonnegative _ hz ht [.i1,.i2,.m1] (by decide +kernel)
  have heq : guard65 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.m1] := by
    dsimp only [guard65,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard66 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+1*A^3*E+2*A^3*F+27*A^3-1*A^2*B+1*A^2*D*E+2*A^2*D*F+20*A^2*D+1*A^2*E*F+17*A^2*E+1*A^2*F^2+40*A^2*F+264*A^2-1*A*B*E-2*A*B*F-15*A*B+1*A*C-1*A*D^2+1*A*D*E*F+12*A*D*E+1*A*D*F^2+28*A*D*F+132*A*D-1*A*E^2+11*A*E*F+87*A*E+12*A*F^2+256*A*F+1098*A+1*B*D-1*B*E*F-6*B*E-1*B*F^2-16*B*F-54*B+1*C*E+1*C*F+9*C-6*D^2+6*D*E*F+37*D*E+6*D*F^2+97*D*F+294*D-6*E^2+27*E*F+126*E+33*F^2+516*F+1620
theorem guard66_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard66 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.i3] := word_height_nonnegative _ hz ht [.i1,.i2,.i3] (by decide +kernel)
  have heq : guard66 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i2,.i3] := by
    dsimp only [guard66,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard67 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*D+1*A^2*F+20*A^2-1*A*B+1*A*D*F+14*A*D-1*A*E+13*A*F+126*A-1*B*F-8*B+7*D*F+48*D-8*E+39*F+240
theorem guard67_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard67 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m3] := word_height_nonnegative _ hz ht [.i1,.m3] (by decide +kernel)
  have heq : guard67 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m3] := by
    dsimp only [guard67,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard68 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*D+2*A^3*F+26*A^3-1*A^2*B+2*A^2*D*F+20*A^2*D-1*A^2*E+1*A^2*F^2+39*A^2*F+247*A^2-2*A*B*F-13*A*B+1*A*C+1*A*D*F^2+27*A*D*F+133*A*D-1*A*E*F-14*A*E+13*A*F^2+245*A*F+1009*A-1*B*F^2-13*B*F-42*B+1*C*F+6*C+7*D*F^2+92*D*F+292*D-7*E*F-50*E+39*F^2+492*F+1476
theorem guard68_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard68 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m3,.m3] := word_height_nonnegative _ hz ht [.i1,.m3,.m3] (by decide +kernel)
  have heq : guard68 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.m3,.m3] := by
    dsimp only [guard68,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard69 (A B C D E F : ℤ) : ℤ := 1*A^2*E+1*A^2-1*A*C-2*A*D+1*A*E*F+14*A*E+2*A*F+14*A-1*C*F-8*C-1*D*F-16*D+7*E*F+48*E+15*F+48
theorem guard69_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard69 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3] := word_height_nonnegative _ hz ht [.i1,.i3] (by decide +kernel)
  have heq : guard69 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3] := by
    dsimp only [guard69,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard70 (A B C D E F : ℤ) : ℤ := 2*A^3*E+4*A^3+1*A^2*C*E+1*A^2*D*E+1*A^2*E*F+38*A^2*E+2*A^2*F+75*A^2-1*A*B*E-2*A*B-1*A*C^2-2*A*C*D+1*A*C*E*F+12*A*C*E+1*A*C*F-2*A*C-1*A*D^2+1*A*D*E*F+12*A*D*E+1*A*D*F-3*A*D-1*A*E^2+13*A*E*F+231*A*E+26*A*F+451*A+1*B*C+1*B*D-6*B*E-12*B-1*C^2*F-6*C^2-2*C*D*F-12*C*D+6*C*E*F+36*C*E+5*C*F-9*C-1*D^2*F-6*D^2+6*D*E*F+37*D*E+5*D*F-14*D-1*E^2*F-6*E^2+37*E*F+448*E+78*F+864
theorem guard70_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard70 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3,.m2,.m1] := word_height_nonnegative _ hz ht [.i1,.i3,.m2,.m1] (by decide +kernel)
  have heq : guard70 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3,.m2,.m1] := by
    dsimp only [guard70,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard71 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+1*A*E^2+7*A*E+18*A-2*B-1*C*E-5*C-1*D*E-1*D+6*E^2+1*E*F+42*E+3*F+66
theorem guard71_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard71 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3,.i2] := word_height_nonnegative _ hz ht [.i1,.i3,.i2] (by decide +kernel)
  have heq : guard71 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1,.i3,.i2] := by
    dsimp only [guard71,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard72 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+1*A*E+13*A-2*B-2*C+4*D+6*E+36
theorem guard72_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard72 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1] := word_height_nonnegative _ hz ht [.i1] (by decide +kernel)
  have heq : guard72 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i1] := by
    dsimp only [guard72,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard73 (A B C D E F : ℤ) : ℤ := 2*A^3+1*A^2*C+3*A^2*D+37*A^2-2*A*B+1*A*C*D+12*A*C+1*A*D^2+37*A*D-1*A*E+217*A-1*B*C-1*B*D-14*B+6*C*D+33*C+6*D^2-1*D*E+106*D-6*E+396
theorem guard73_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard73 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1] := word_height_nonnegative _ hz ht [.m2,.m1] (by decide +kernel)
  have heq : guard73 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1] := by
    dsimp only [guard73,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard74 (A B C D E F : ℤ) : ℤ := 1*A^3*E+2*A^3+1*A^2*C*E+3*A^2*C+2*A^2*D*E+5*A^2*D+19*A^2*E+39*A^2-1*A*B*E-2*A*B+1*A*C*D*E+3*A*C*D+14*A*C*E+41*A*C+1*A*D^2*E+3*A*D^2+26*A*D*E+66*A*D-1*A*E^2+114*A*E+242*A-1*B*C*E-3*B*C-1*B*D*E-3*B*D-6*B*E-14*B+1*C^2*E+3*C^2+8*C*D*E+24*C*D+46*C*E+132*C+7*D^2*E+21*D^2-1*D*E^2+77*D*E+204*D-6*E^2+1*E*F+214*E+1*F+468
theorem guard74_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard74 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3,.m2] := word_height_nonnegative _ hz ht [.m2,.m1,.i3,.m2] (by decide +kernel)
  have heq : guard74 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3,.m2] := by
    dsimp only [guard74,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard75 (A B C D E F : ℤ) : ℤ := 1*A^4+2*A^3*C+3*A^3*D+1*A^3*E+27*A^3-1*A^2*B+1*A^2*C^2+4*A^2*C*D+1*A^2*C*E+40*A^2*C+3*A^2*D^2+2*A^2*D*E+61*A^2*D+17*A^2*E+264*A^2-2*A*B*C-2*A*B*D-1*A*B*E-15*A*B+1*A*C^2*D+12*A*C^2+2*A*C*D^2+1*A*C*D*E+52*A*C*D+11*A*C*E+256*A*C+1*A*D^3+1*A*D^2*E+40*A*D^2+22*A*D*E+396*A*D-1*A*E^2+87*A*E+1*A*F+1098*A-1*B*C^2-2*B*C*D-1*B*C*E-16*B*C-1*B*D^2-1*B*D*E-16*B*D-6*B*E-54*B+6*C^2*D+33*C^2+12*C*D^2+5*C*D*E+159*C*D+27*C*E+1*C*F+516*C+6*D^3+5*D^2*E+126*D^2-1*D*E^2+50*D*E+1*D*F+804*D-6*E^2+1*E*F+126*E+9*F+1620
theorem guard75_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard75 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3,.i2] := word_height_nonnegative _ hz ht [.m2,.m1,.i3,.i2] (by decide +kernel)
  have heq : guard75 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m1,.i3,.i2] := by
    dsimp only [guard75,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard76 (A B C D E F : ℤ) : ℤ := 1*A^3+2*A^2*D+1*A^2*E+21*A^2-1*A*B+1*A*D^2+2*A*D*E+30*A*D+13*A*E-1*A*F+140*A-1*B*D-8*B+1*D^2*E+9*D^2+13*D*E-1*D*F+108*D+40*E-8*F+288
theorem guard76_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard76 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m2] := word_height_nonnegative _ hz ht [.m2,.m2] (by decide +kernel)
  have heq : guard76 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.m2] := by
    dsimp only [guard76,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard77 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+1*A*E^2+7*A*E+18*A-2*B+1*C*E+3*C+1*D*E^2+8*D*E+19*D+6*E^2-1*E*F+42*E-5*F+66
theorem guard77_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard77 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3] := word_height_nonnegative _ hz ht [.m2,.i3] (by decide +kernel)
  have heq : guard77 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3] := by
    dsimp only [guard77,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard78 (A B C D E F : ℤ) : ℤ := 1*A^2*E+1*A^2+1*A*C*E+2*A*C+2*A*D*E+4*A*D+14*A*E-1*A*F+14*A+1*C*D*E+3*C*D+7*C*E-1*C*F+15*C+1*D^2*E+3*D^2+14*D*E-1*D*F+30*D+48*E-8*F+48
theorem guard78_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard78 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3,.i2] := word_height_nonnegative _ hz ht [.m2,.i3,.i2] (by decide +kernel)
  have heq : guard78 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2,.i3,.i2] := by
    dsimp only [guard78,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard79 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*D+1*A*E+13*A-2*B+1*D*E+9*D+6*E-2*F+36
theorem guard79_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard79 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2] := word_height_nonnegative _ hz ht [.m2] (by decide +kernel)
  have heq : guard79 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m2] := by
    dsimp only [guard79,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard80 (A B C D E F : ℤ) : ℤ := 1*A^3*B+3*A^3+1*A^2*B*C+2*A^2*B*D+1*A^2*B*F+18*A^2*B+4*A^2*C+7*A^2*D+2*A^2*F+55*A^2-1*A*B^2+1*A*B*C*D+1*A*B*C*F+12*A*B*C+1*A*B*D^2+2*A*B*D*F+24*A*B*D-1*A*B*E+12*A*B*F+100*A*B+4*A*C*D+4*A*C*F+48*A*C+4*A*D^2+6*A*D*F+85*A*D-3*A*E-1*A*F^2+25*A*F+319*A-1*B^2*D-6*B^2+1*B*C*D*F+6*B*C*D-1*B*C*E+6*B*C*F+34*B*C+1*B*D^2*F+6*B*D^2-1*B*D*E+12*B*D*F+63*B*D-6*B*E+36*B*F+168*B+4*C*D*F+24*C*D-4*C*E+24*C*F+135*C+4*D^2*F+24*D^2-4*D*E-1*D*F^2+37*D*F+237*D+1*E*F-20*E-6*F^2+79*F+576
theorem guard80_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard80 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.m1,.i3] := word_height_nonnegative _ hz ht [.i2,.m1,.i3] (by decide +kernel)
  have heq : guard80 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.m1,.i3] := by
    dsimp only [guard80,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard81 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*B+2*A^2*D+1*A^2*F+21*A^2+2*A*B*D+13*A*B+1*A*D^2+2*A*D*F+30*A*D-1*A*E+13*A*F+140*A+1*B*D^2+13*B*D+40*B+1*D^2*F+9*D^2-1*D*E+13*D*F+108*D-8*E+40*F+288
theorem guard81_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard81 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.i2] := word_height_nonnegative _ hz ht [.i2,.i2] (by decide +kernel)
  have heq : guard81 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.i2] := by
    dsimp only [guard81,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard82 (A B C D E F : ℤ) : ℤ := 1*A^3+1*A^2*C+2*A^2*D+1*A^2*F+20*A^2-1*A*B+1*A*C*D+1*A*C*F+13*A*C+1*A*D^2+2*A*D*F+26*A*D-1*A*E+14*A*F+126*A-1*B*D-8*B+1*C*D*F+6*C*D-1*C*E+7*C*F+39*C+1*D^2*F+6*D^2-1*D*E+14*D*F+78*D-8*E+48*F+240
theorem guard82_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard82 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.i3,.i2] := word_height_nonnegative _ hz ht [.i2,.i3,.i2] (by decide +kernel)
  have heq : guard82 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2,.i3,.i2] := by
    dsimp only [guard82,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard83 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B+1*A*D+1*A*F+13*A+1*B*D+6*B+1*D*F+9*D-2*E+6*F+36
theorem guard83_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard83 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2] := word_height_nonnegative _ hz ht [.i2] (by decide +kernel)
  have heq : guard83 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i2] := by
    dsimp only [guard83,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard84 (A B C D E F : ℤ) : ℤ := 2*A^3+3*A^2*D+2*A^2*F+37*A^2-1*A*B+1*A*D^2+3*A*D*F+37*A*D-2*A*E+25*A*F+217*A-1*B*F-6*B+1*D^2*F+6*D^2-1*D*E+19*D*F+111*D-14*E+73*F+396
theorem guard84_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard84 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3,.m2] := word_height_nonnegative _ hz ht [.m3,.m2] (by decide +kernel)
  have heq : guard84 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3,.m2] := by
    dsimp only [guard84,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard85 (A B C D E F : ℤ) : ℤ := 1*A^4+1*A^3*B+1*A^3*D+1*A^3*F+27*A^3+1*A^2*B*D+1*A^2*B*F+17*A^2*B+1*A^2*D*F+20*A^2*D-1*A^2*E+21*A^2*F+264*A^2-1*A*B^2+1*A*B*D*F+12*A*B*D-1*A*B*E+11*A*B*F+87*A*B+1*A*C-1*A*D^2+14*A*D*F+132*A*D-15*A*E+140*A*F+1098*A-1*B^2*F-6*B^2+1*B*C+6*B*D*F+37*B*D-6*B*E+23*B*F+126*B+9*C-1*D^2*F-6*D^2+1*D*E+47*D*F+294*D-54*E+288*F+1620
theorem guard85_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard85 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3,.m2,.m1] := word_height_nonnegative _ hz ht [.m3,.m2,.m1] (by decide +kernel)
  have heq : guard85 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3,.m2,.m1] := by
    dsimp only [guard85,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard86 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*B+1*A*D+1*A*F+13*A+1*B*F+6*B-2*C+1*D*F+4*D-2*E+9*F+36
theorem guard86_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard86 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3] := word_height_nonnegative _ hz ht [.m3] (by decide +kernel)
  have heq : guard86 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.m3] := by
    dsimp only [guard86,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard87 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*C+1*A*D+1*A*E+1*A*F+13*A-2*B+1*C*E+1*C*F+9*C+1*D*E+1*D*F+9*D+6*E+6*F+36
theorem guard87_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard87 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3,.i2] := word_height_nonnegative _ hz ht [.i3,.i2] (by decide +kernel)
  have heq : guard87 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3,.i2] := by
    dsimp only [guard87,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard88 (A B C D E F : ℤ) : ℤ := 1*A^2+1*A*C+1*A*D+1*A*E+1*A*F+13*A-2*B+1*C*F+6*C+1*D*F+4*D+1*E*F+6*E+9*F+36
theorem guard88_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard88 A B C D E F := by
  have hr : 0≤heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3] := word_height_nonnegative _ hz ht [.i3] (by decide +kernel)
  have heq : guard88 A B C D E F=heightPolynomial ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ [.i3] := by
    dsimp only [guard88,heightPolynomial,coordinateSum,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard89 (A B C D E F : ℤ) : ℤ := 1*A
theorem guard89_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard89 A B C D E F := by
  dsimp only [guard89]
  positivity

def guard90 (A B C D E F : ℤ) : ℤ := 1*B
theorem guard90_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard90 A B C D E F := by
  dsimp only [guard90]
  positivity

def guard91 (A B C D E F : ℤ) : ℤ := 1*D
theorem guard91_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard91 A B C D E F := by
  dsimp only [guard91]
  positivity

def guard92 (A B C D E F : ℤ) : ℤ := 1*E
theorem guard92_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard92 A B C D E F := by
  dsimp only [guard92]
  positivity

def guard93 (A B C D E F : ℤ) : ℤ := 1*A^2*B+1*A^2+1*A*B*D+12*A*B+1*A*D+12*A-1*B^2+6*B*D+30*B-1*D^2+6*D+20
theorem guard93_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard93 A B C D E F := by
  have hc := word_triangle_bounds _ hz [] (by decide +kernel)
  have hr : 0≤-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).b (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).d := by linarith only [hc.1]
  have heq : guard93 A B C D E F=-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).b (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).d := by
    dsimp only [guard93,triangleDefect,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard94 (A B C D E F : ℤ) : ℤ := 1*A^2*E+1*A^2+1*A*C*E+1*A*C+1*A*D*E+1*A*D+12*A*E+12*A-1*C^2-2*C*D+6*C*E+6*C-1*D^2+6*D*E+6*D-1*E^2+30*E+20
theorem guard94_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard94 A B C D E F := by
  have hc := word_triangle_bounds _ hz [] (by decide +kernel)
  have hr : 0≤-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).c (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).e := by linarith only [hc.2.1]
  have heq : guard94 A B C D E F=-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).a (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).c (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).e := by
    dsimp only [guard94,triangleDefect,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard95 (A B C D E F : ℤ) : ℤ := 1*A^2*B+1*A^2+1*A*B*C+1*A*B*D+1*A*B*F+12*A*B+1*A*C+1*A*D+1*A*F+12*A-1*B^2+1*B*C*F+6*B*C+1*B*D*F+6*B*D+6*B*F+30*B-1*C^2-2*C*D+3*C*F+6*C-1*D^2+3*D*F+6*D-1*F^2+6*F+20
theorem guard95_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard95 A B C D E F := by
  have hc := word_triangle_bounds _ hz [] (by decide +kernel)
  have hr : 0≤-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).b (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).c (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).f := by linarith only [hc.2.2.1]
  have heq : guard95 A B C D E F=-7-triangleDefect (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).b (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).c (applyWord ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩ []).f := by
    dsimp only [guard95,triangleDefect,applyWord,step,mu1,mu2,mu3,inv1,inv2,inv3]
    ring
  rw [heq]
  exact hr

def guard96 (A B C D E F : ℤ) : ℤ := 1*A+1*C+1*D+3
theorem guard96_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard96 A B C D E F := by
  dsimp only [guard96]
  positivity

def guard97 (A B C D E F : ℤ) : ℤ := 1*A+1*D
theorem guard97_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard97 A B C D E F := by
  dsimp only [guard97]
  positivity

def guard98 (A B C D E F : ℤ) : ℤ := 1*A+1*F
theorem guard98_nonnegative (A B C D E F : ℤ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hF : 0≤F)
    (hz : Chamber ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) (ht : AllTerminal ⟨A+6,B+3,A+C+D+6,A+D+6,E+3,A+F+6⟩) :
    0≤guard98 A B C D E F := by
  dsimp only [guard98]
  positivity

end SerreMarkov.PositiveSortedLarge
