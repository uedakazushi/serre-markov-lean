import SerreMarkov.IntrinsicSigns
import SerreMarkov.DescentTrap

/-! # Unbounded positive one-step local minima and their two-step descent

The sequence exhibits a precise obstruction to a finite bound based solely on
six elementary braid moves. Every term is a positive solution, and no single
generator reduces its coordinate height. The same terms all descend by the
fixed two-letter word `[m1,m2]`. No global classification or descent cutpoint
is assumed here.
-/

namespace SerreMarkov.PositiveLocalMinima

structure State where
  a : ℤ
  b : ℤ
  e : ℤ
  f : ℤ

def toSix (s : State) : Six := ⟨s.a,s.b,3,3,s.e,s.f⟩
def advance (s : State) : State := ⟨s.e,s.f,3*s.e-s.a,3*s.f-s.b⟩
def states : ℕ → State
  | 0 => ⟨7,6,15,11⟩
  | n+1 => advance (states n)
def localMinimum (n : ℕ) : Six := toSix (states n)

/-- A linear invariant cone for the four changing coordinates. -/
structure GrowthCone (s : State) : Prop where
  a_ge : 7 ≤ s.a
  b_ge : 6 ≤ s.b
  b_le_a : s.b ≤ s.a
  f_le_e : s.f ≤ s.e
  difference_monotone : s.a-s.b ≤ s.e-s.f
  a_lt_e : s.a+1 ≤ s.e
  b_lt_f : s.b+1 ≤ s.f
  e_upper : s.e ≤ 3*s.a-3
  f_upper : s.f ≤ 3*s.b-3
  a_le_f : s.a ≤ s.f
  ratio_first : 0 < 3*s.b-2*s.a
  ratio_second : 0 < 3*s.f-2*s.e
  ratio_balanced : 3*s.b-2*s.a ≤ 2*(3*s.f-2*s.e)
  sum_growth : 2*(s.a+s.b) ≤ s.e+s.f

theorem advance_cone (s : State) (hs : GrowthCone s) : GrowthCone (advance s) := by
  rcases hs with ⟨ha,hb,hba,hfe,hd,hae,hbf,he,hf,haf,hr,hs,hrt,hsum⟩
  constructor <;> dsimp [advance] <;> linarith

theorem states_cone (n : ℕ) : GrowthCone (states n) := by
  induction n with
  | zero => constructor <;> norm_num [states]
  | succ n ih => exact advance_cone _ ih

theorem advance_q1 (s : State) : q1 (toSix (advance s)) = q1 (toSix s) := by
  rcases s with ⟨a,b,e,f⟩
  dsimp [advance,toSix,q1]
  ring

theorem advance_q2 (s : State) : q2 (toSix (advance s)) = q2 (toSix s) := by
  rcases s with ⟨a,b,e,f⟩
  dsimp [advance,toSix,q2]
  ring

theorem localMinimum_isSolution (n : ℕ) : isSolution (localMinimum n) := by
  induction n with
  | zero => norm_num [localMinimum,states,toSix,isSolution,q1,q2]
  | succ n ih =>
    unfold isSolution localMinimum at *
    simpa only [states,advance_q1,advance_q2] using ih

def pairNorm (x y : ℤ) : ℤ := x^2+y^2-3*x*y

theorem pairNorm_advance (x y : ℤ) : pairNorm y (3*y-x) = pairNorm x y := by
  dsimp [pairNorm]
  ring

theorem states_pairNorms (n : ℕ) :
    pairNorm (states n).a (states n).e = -41 ∧
    pairNorm (states n).b (states n).f = -41 := by
  induction n with
  | zero => norm_num [states,pairNorm]
  | succ n ih => simpa only [states,advance,pairNorm_advance] using ih

theorem marker_of_pairNorms (s : State)
    (ha : pairNorm s.a s.e = -41) (hb : pairNorm s.b s.f = -41) :
    IntrinsicSigns.thirdMinorSum (toSix s) = 288+6*(s.f-s.a)*(s.e-s.b) := by
  dsimp [pairNorm] at ha hb
  dsimp [IntrinsicSigns.thirdMinorSum,toSix]
  linear_combination -4*ha-4*hb

theorem localMinimum_positive_marker (n : ℕ) :
    0 < IntrinsicSigns.thirdMinorSum (localMinimum n) := by
  have h := states_cone n
  have hn := states_pairNorms n
  rw [localMinimum,marker_of_pairNorms _ hn.1 hn.2]
  have hp : 0 ≤ ((states n).f-(states n).a)*((states n).e-(states n).b) :=
    mul_nonneg (by linarith [h.a_le_f]) (by linarith [h.f_le_e,h.b_lt_f])
  linarith

theorem localMinimum_coordinates_ge_three (n : ℕ) :
    3 ≤ (localMinimum n).a ∧ 3 ≤ (localMinimum n).b ∧
    3 ≤ (localMinimum n).c ∧ 3 ≤ (localMinimum n).d ∧
    3 ≤ (localMinimum n).e ∧ 3 ≤ (localMinimum n).f := by
  have h := states_cone n
  dsimp [localMinimum,toSix]
  exact ⟨by linarith [h.a_ge],by linarith [h.b_ge],le_rfl,le_rfl,
    by linarith [h.a_ge,h.a_lt_e],by linarith [h.b_ge,h.b_lt_f]⟩

def integerHeight (z : Six) : ℤ := |z.a|+|z.b|+|z.c|+|z.d|+|z.e|+|z.f|

theorem integerHeight_cast (z : Six) : integerHeight z = (coordinateHeight z : ℤ) := by
  simp [integerHeight,coordinateHeight]

private theorem product_ge_nine (x y : ℤ) (hx : 3 ≤ x) (hy : 3 ≤ y) : 9 ≤ x*y := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ x-3) (by linarith : 0 ≤ y-3)]

/-- Every point in the invariant cone is a one-step height minimum. -/
theorem cone_one_step_integer_minimum (s : State) (hs : GrowthCone s) (g : Generator) :
    integerHeight (toSix s) ≤ integerHeight (step g (toSix s)) := by
  rcases s with ⟨a,b,e,f⟩
  rcases hs with ⟨ha,hb,hba,hfe,hd,hae,hbf,he,hf,haf,hr,hs,hrt,hsum⟩
  dsimp at ha hb hba hfe hd hae hbf he hf haf hr hs hrt hsum
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have he0 : 0 ≤ e := by omega
  have hf0 : 0 ≤ f := by omega
  have hab9 : 9 ≤ a*b := product_ge_nine _ _ (by omega) (by omega)
  have hae9 : 9 ≤ a*e := product_ge_nine _ _ (by omega) (by omega)
  have hfb9 : 9 ≤ f*b := product_ge_nine _ _ (by omega) (by omega)
  have hfe9 : 9 ≤ f*e := product_ge_nine _ _ (by omega) (by omega)
  have hab3 : 0 ≤ a*b-3 := by linarith
  have hae3 : 0 ≤ a*e-3 := by linarith
  have hfb3 : 0 ≤ f*b-3 := by linarith
  have hfe3 : 0 ≤ f*e-3 := by linarith
  have h3ae : 0 ≤ 3*a-e := by omega
  have h3ab : 0 ≤ 3*a-b := by omega
  have h3ef : 0 ≤ 3*e-f := by omega
  have h3ba : 0 ≤ 3*b-a := by omega
  have h3fe : 0 ≤ 3*f-e := by omega
  have h3fb : 0 ≤ 3*f-b := by omega
  have hp : 0 ≤ a*(b-3) := mul_nonneg ha0 (by omega)
  cases g <;> dsimp [step,integerHeight,toSix,mu1,inv1,mu2,inv2,mu3,inv3,eps1,eps2,eps3,eps4]
  all_goals try simp only [mul_comm a 3,mul_comm b 3,mul_comm f 3]
  all_goals simp only [abs_neg,abs_of_nonneg ha0,abs_of_nonneg hb0,
    abs_of_nonneg he0,abs_of_nonneg hf0,abs_of_nonneg hab3,abs_of_nonneg hae3,
    abs_of_nonneg hfb3,abs_of_nonneg hfe3,abs_of_nonneg h3ae,abs_of_nonneg h3ab,
    abs_of_nonneg h3ef,abs_of_nonneg h3ba,abs_of_nonneg h3fe,abs_of_nonneg h3fb,
    abs_of_nonneg (by decide : 0 ≤ (3:ℤ))]
  all_goals nlinarith

theorem cone_one_step_minimum (s : State) (hs : GrowthCone s) (g : Generator) :
    coordinateHeight (toSix s) ≤ coordinateHeight (step g (toSix s)) := by
  have h := cone_one_step_integer_minimum s hs g
  rw [integerHeight_cast,integerHeight_cast] at h
  exact_mod_cast h

theorem localMinimum_one_step_minimum (n : ℕ) (g : Generator) :
    coordinateHeight (localMinimum n) ≤ coordinateHeight (step g (localMinimum n)) :=
  cone_one_step_minimum _ (states_cone n) g

/-- A fixed two-letter word reduces the entire slice to four simpler coordinates. -/
theorem two_steps_literal (s : State) :
    applyWord (toSix s) [.m1,.m2] = ⟨3,s.a,3*s.a-s.e,s.b,3*s.b-s.f,3⟩ := by
  ext <;> dsimp [applyWord,step,toSix,mu1,mu2] <;> ring

theorem cone_two_step_height_difference (s : State) (hs : GrowthCone s) :
    integerHeight (toSix s)-integerHeight (applyWord (toSix s) [.m1,.m2]) =
      2*(s.e+s.f)-3*(s.a+s.b) := by
  rw [two_steps_literal]
  have ha0 : 0 ≤ s.a := by linarith [hs.a_ge]
  have hb0 : 0 ≤ s.b := by linarith [hs.b_ge]
  have he0 : 0 ≤ s.e := by linarith [hs.a_ge,hs.a_lt_e]
  have hf0 : 0 ≤ s.f := by linarith [hs.b_ge,hs.b_lt_f]
  have h3ae : 0 ≤ 3*s.a-s.e := by linarith [hs.e_upper]
  have h3bf : 0 ≤ 3*s.b-s.f := by linarith [hs.f_upper]
  simp only [integerHeight,toSix,abs_of_nonneg ha0,abs_of_nonneg hb0,
    abs_of_nonneg he0,abs_of_nonneg hf0,abs_of_nonneg h3ae,abs_of_nonneg h3bf,
    abs_of_nonneg (by decide : 0 ≤ (3:ℤ))]
  ring

/-- The two-step descent is universal on the cone, with no solution hypothesis. -/
theorem cone_two_steps_decrease (s : State) (hs : GrowthCone s) :
    coordinateHeight (applyWord (toSix s) [.m1,.m2]) < coordinateHeight (toSix s) := by
  have hd := cone_two_step_height_difference s hs
  have hp : 0 < 2*(s.e+s.f)-3*(s.a+s.b) := by
    linarith [hs.sum_growth,hs.a_ge,hs.b_ge]
  rw [integerHeight_cast,integerHeight_cast] at hd
  exact_mod_cast (show (coordinateHeight (applyWord (toSix s) [.m1,.m2]) : ℤ) <
    (coordinateHeight (toSix s) : ℤ) by linarith)

theorem localMinimum_two_steps_decrease (n : ℕ) :
    coordinateHeight (applyWord (localMinimum n) [.m1,.m2]) < coordinateHeight (localMinimum n) :=
  cone_two_steps_decrease _ (states_cone n)

theorem states_a_lower_bound (n : ℕ) : (n:ℤ)+7 ≤ (states n).a := by
  induction n with
  | zero => norm_num [states]
  | succ n ih =>
    have h := (states_cone n).a_lt_e
    change (n+1:ℤ)+7 ≤ (states n).e
    linarith

theorem localMinimum_height_lower_bound (n : ℕ) : n+7 ≤ coordinateHeight (localMinimum n) := by
  have ha := states_a_lower_bound n
  have hs := states_cone n
  have hheight : (n:ℤ)+7 ≤ integerHeight (localMinimum n) := by
    dsimp [integerHeight,localMinimum,toSix]
    have hapos : 0 ≤ (states n).a := by linarith [hs.a_ge]
    rw [abs_of_nonneg hapos]
    linarith [abs_nonneg (states n).b,abs_nonneg (states n).e,abs_nonneg (states n).f,
      abs_nonneg (3:ℤ)]
  rw [integerHeight_cast] at hheight
  exact_mod_cast hheight

/-- One-step local minima cannot have a finite coordinate-height bound on
positive solutions. The obstruction is compatible with fixed two-step descent. -/
theorem positive_one_step_minima_unbounded (B : ℕ) :
    ∃ z : Six, isSolution z ∧ 0 < IntrinsicSigns.thirdMinorSum z ∧
      (3 ≤ z.a ∧ 3 ≤ z.b ∧ 3 ≤ z.c ∧ 3 ≤ z.d ∧ 3 ≤ z.e ∧ 3 ≤ z.f) ∧
      (∀ g : Generator, coordinateHeight z ≤ coordinateHeight (step g z)) ∧
      B < coordinateHeight z := by
  refine ⟨localMinimum B,localMinimum_isSolution B,localMinimum_positive_marker B,
    localMinimum_coordinates_ge_three B,localMinimum_one_step_minimum B,?_⟩
  have h := localMinimum_height_lower_bound B
  omega

end SerreMarkov.PositiveLocalMinima
