import SerreMarkov.PositiveChamber
import Mathlib.Data.ZMod.Basic

/-! # Consecutive adjacent pairings cannot both equal three

The positive integral chamber makes `9-b` at least three when `a=d=3`.
For `b=3,6` the equation for `q₂` is impossible modulo three. For `b=4,5`
eliminating the fifth coordinate gives a binary conic with no roots modulo
twenty-seven. Every residue check is reduced in Lean's kernel. This is an
unconditional obstruction and does not assume a short-word terminal bound.
-/

namespace SerreMarkov.PositiveAdjacentThrees

open PositiveChamber
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

private theorem conic_four_mod27 : ∀ c f : ZMod 27,
    (-11*c^2+26*c*f+24*(c+f)-11*f^2-144 ≠ 0) ∧
    (-11*c^2+26*c*f-24*(c+f)-11*f^2-144 ≠ 0) := by decide +kernel

private theorem conic_five_mod27 : ∀ c f : ZMod 27,
    (-11*c^2+28*c*f+36*(c+f)-11*f^2-234 ≠ 0) ∧
    (-11*c^2+28*c*f-36*(c+f)-11*f^2-234 ≠ 0) := by decide +kernel

theorem no_solution_three_four_three (c e f : ℤ) :
    ¬ isSolution ⟨3,4,c,3,e,f⟩ := by
  intro hz
  have h1 := hz.1
  have hq : q2 ⟨3,4,c,3,e,f⟩ = 4 ∨ q2 ⟨3,4,c,3,e,f⟩ = -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  dsimp [q1] at h1
  rcases hq with hq | hq
  · dsimp [q2] at hq
    have hconic : -11*c^2+26*c*f+24*(c+f)-11*f^2-144=0 := by
      linear_combination 16*h1 - (9*c-4*e+9*f+4)*hq
    have hmod := congrArg (fun n : ℤ => (n : ZMod 27)) hconic
    push_cast at hmod
    exact (conic_four_mod27 (c : ZMod 27) (f : ZMod 27)).1 hmod
  · dsimp [q2] at hq
    have hconic : -11*c^2+26*c*f-24*(c+f)-11*f^2-144=0 := by
      linear_combination 16*h1 - (9*c-4*e+9*f-4)*hq
    have hmod := congrArg (fun n : ℤ => (n : ZMod 27)) hconic
    push_cast at hmod
    exact (conic_four_mod27 (c : ZMod 27) (f : ZMod 27)).2 hmod

theorem no_solution_three_five_three (c e f : ℤ) :
    ¬ isSolution ⟨3,5,c,3,e,f⟩ := by
  intro hz
  have h1 := hz.1
  have hq : q2 ⟨3,5,c,3,e,f⟩ = 4 ∨ q2 ⟨3,5,c,3,e,f⟩ = -4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hz.2)
  dsimp [q1] at h1
  rcases hq with hq | hq
  · dsimp [q2] at hq
    have hconic : -11*c^2+28*c*f+36*(c+f)-11*f^2-234=0 := by
      linear_combination 25*h1 - (12*c-5*e+12*f+4)*hq
    have hmod := congrArg (fun n : ℤ => (n : ZMod 27)) hconic
    push_cast at hmod
    exact (conic_five_mod27 (c : ZMod 27) (f : ZMod 27)).1 hmod
  · dsimp [q2] at hq
    have hconic : -11*c^2+28*c*f-36*(c+f)-11*f^2-234=0 := by
      linear_combination 25*h1 - (12*c-5*e+12*f-4)*hq
    have hmod := congrArg (fun n : ℤ => (n : ZMod 27)) hconic
    push_cast at hmod
    exact (conic_five_mod27 (c : ZMod 27) (f : ZMod 27)).2 hmod

/-- No positive integral chamber point has its first two adjacent braid
pairings both equal to three. No no-drop hypothesis is required. -/
theorem chamber_no_adjacent_threes (z : Six) (hz : Chamber z)
    (ha : z.a=3) (hd : z.d=3) : False := by
  have hsol := hz.1
  have hbLo : 3 ≤ z.b := hz.2.2.2.1
  have hmut := step_preserves_chamber .i1 True.intro z hz
  have hbHi : z.b ≤ 6 := by
    have hmutd : 3 ≤ (step .i1 z).d := hmut.2.2.2.2.2.1
    simp only [step,inv1,ha,hd] at hmutd
    omega
  have hb : z.b=3 ∨ z.b=4 ∨ z.b=5 ∨ z.b=6 := by omega
  have hq : q2 z=4 ∨ q2 z=-4 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by norm_num; exact hsol.2)
  rcases hb with hb | hb | hb | hb
  · rcases hq with hq | hq <;> simp only [q2,ha,hd,hb] at hq <;> omega
  · have heq : z=⟨3,4,z.c,3,z.e,z.f⟩ := by ext <;> simp [ha,hd,hb]
    exact no_solution_three_four_three z.c z.e z.f (heq ▸ hsol)
  · have heq : z=⟨3,5,z.c,3,z.e,z.f⟩ := by ext <;> simp [ha,hd,hb]
    exact no_solution_three_five_three z.c z.e z.f (heq ▸ hsol)
  · rcases hq with hq | hq <;> simp only [q2,ha,hd,hb] at hq <;> omega

def reverseSix (z : Six) : Six := ⟨z.f,z.e,z.c,z.d,z.b,z.a⟩

theorem reverseSix_chamber (z : Six) (hz : Chamber z) : Chamber (reverseSix z) := by
  obtain ⟨hsol,hpos,ha,hb,hc,hd,he,hf⟩ := hz
  have hq1 : q1 (reverseSix z)=q1 z := by dsimp [q1,reverseSix]; ring
  have hq2 : q2 (reverseSix z)=q2 z := by dsimp [q2,reverseSix]; ring
  have hmarker : IntrinsicSigns.thirdMinorSum (reverseSix z)=IntrinsicSigns.thirdMinorSum z := by
    dsimp [IntrinsicSigns.thirdMinorSum,reverseSix]
    ring
  refine ⟨⟨by rw [hq1]; exact hsol.1, by rw [hq2]; exact hsol.2⟩,?_,?_⟩
  · rw [hmarker]
    exact hpos
  · exact ⟨hf,he,hc,hd,hb,ha⟩

theorem chamber_no_last_adjacent_threes (z : Six) (hz : Chamber z)
    (hd : z.d=3) (hf : z.f=3) : False :=
  chamber_no_adjacent_threes (reverseSix z) (reverseSix_chamber z hz) hf hd

end SerreMarkov.PositiveAdjacentThrees
