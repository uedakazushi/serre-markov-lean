import SerreMarkov.NegativeEndpointUnits
import SerreMarkov.CyclicMutation

/-! # Reductions at the crossed unit edges

The proofs below use integer equations, inequalities, and explicit finite words.
No unproved unit or zero branch is a premise.
-/

namespace SerreMarkov.NegativeCrossingUnits

open NegativeDescent NegativeTwoEdge NegativeUnitSmall
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem opposed_pair_bound (r s t u : ℤ)
    (hr : 2≤r) (hs : 2≤s) (ht : 2≤t) (hu : 2≤u)
    (hk : r*s-t*u=5 ∨ r*s-t*u=-3) :
    -r*s*t*u+r^2+s^2+t^2+u^2+(r+s)*(t+u-4)+2<8 := by
  have hr2 : 0≤r^2-4 := by nlinarith [sq_nonneg (r-2)]
  have hs2 : 0≤s^2-4 := by nlinarith [sq_nonneg (s-2)]
  have ht2 : 0≤t^2-4 := by nlinarith [sq_nonneg (t-2)]
  have hu2 : 0≤u^2-4 := by nlinarith [sq_nonneg (u-2)]
  have hRS : 4*(r^2+s^2)≤(r*s)^2+16 := by
    nlinarith [mul_nonneg hr2 hs2]
  have hTU : 4*(t^2+u^2)≤(t*u)^2+16 := by
    nlinarith [mul_nonneg ht2 hu2]
  have hU : 0≤r*s-2*(r+s)+4 := by
    nlinarith [mul_nonneg (by omega : 0≤r-2) (by omega : 0≤s-2)]
  have hV : 0≤t*u-2*(t+u)+4 := by
    nlinarith [mul_nonneg (by omega : 0≤t-2) (by omega : 0≤u-2)]
  have hA : 4≤r*s := by nlinarith [hU]
  have hB : 4≤t*u := by nlinarith [hV]
  have hP : 16≤r*s*t*u := by
    nlinarith [mul_nonneg (by nlinarith : 0≤r*s-4) (by nlinarith : 0≤t*u-4)]
  have hcross : 4*(r+s)*(t+u-4)≤(r*s+4)*(t*u-4) := by
    nlinarith [mul_nonneg hU (by nlinarith : 0≤t*u-4),
      mul_nonneg hV (by omega : 0≤2*(r+s))]
  rcases hk with hk | hk
  · have hsq : (r*s-t*u)^2=25 := by rw [hk]; norm_num
    nlinarith [hRS,hTU,hcross,hP,hsq]
  · have hsq : (r*s-t*u)^2=9 := by rw [hk]; norm_num
    nlinarith [hRS,hTU,hcross,hP,hsq]

/-- Crossed unit pairings cannot coexist with four outer pairings of absolute value at least two. -/
theorem crossing_outer_all_two_impossible (a c d f : ℤ)
    (ha2 : 2≤|a|) (hc2 : 2≤|c|) (hd2 : 2≤|d|) (hf2 : 2≤|f|)
    (hq : a*c*d*f-a*d-a*c-c*f-d*f+a^2+c^2+d^2+f^2+2=8)
    (hk : a*f+c*d=5 ∨ a*f+c*d=-3) : False := by
  by_cases ha : 0≤a
  ·
    by_cases hf : 0≤f
    ·
      by_cases hc : 0≤c
      ·
        by_cases hd : 0≤d
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hAF : 4≤a*f := by nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤f-2)]
          have hCD : 4≤c*d := by nlinarith [mul_nonneg (by omega : 0≤c-2) (by omega : 0≤d-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hk' : a*f-c*(-d)=5 ∨ a*f-c*(-d)=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound a f c (-d) hapos hfpos hcpos hdpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤c-2) (by omega : 0≤a+f)
          have hcross2 := mul_nonneg (by omega : 0≤(-d)-2) (by omega : 0≤a+f)
          nlinarith [hq,hbound,hcross1,hcross2]
      ·
        by_cases hd : 0≤d
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hk' : a*f-(-c)*d=5 ∨ a*f-(-c)*d=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound a f (-c) d hapos hfpos hcpos hdpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤a+f)
          have hcross2 := mul_nonneg (by omega : 0≤d-2) (by omega : 0≤a+f)
          nlinarith [hq,hbound,hcross1,hcross2]
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hAF : 4≤a*f := by nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤f-2)]
          have hCD : 4≤(-c)*(-d) := by nlinarith [mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤(-d)-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
    ·
      by_cases hc : 0≤c
      ·
        by_cases hd : 0≤d
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hk' : c*d-a*(-f)=5 ∨ c*d-a*(-f)=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound c d a (-f) hcpos hdpos hapos hfpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤a-2) (by omega : 0≤c+d)
          have hcross2 := mul_nonneg (by omega : 0≤(-f)-2) (by omega : 0≤c+d)
          nlinarith [hq,hbound,hcross1,hcross2]
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hAF : 4≤a*(-f) := by nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤(-f)-2)]
          have hCD : 4≤c*(-d) := by nlinarith [mul_nonneg (by omega : 0≤c-2) (by omega : 0≤(-d)-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
      ·
        by_cases hd : 0≤d
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hAF : 4≤a*(-f) := by nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤(-f)-2)]
          have hCD : 4≤(-c)*d := by nlinarith [mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤d-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
        ·
          have hapos : 2≤a := by simpa only [abs_of_nonneg ha] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hk' : (-c)*(-d)-a*(-f)=5 ∨ (-c)*(-d)-a*(-f)=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound (-c) (-d) a (-f) hcpos hdpos hapos hfpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤a-2) (by omega : 0≤(-c)+(-d))
          have hcross2 := mul_nonneg (by omega : 0≤(-f)-2) (by omega : 0≤(-c)+(-d))
          nlinarith [hq,hbound,hcross1,hcross2]
  ·
    by_cases hf : 0≤f
    ·
      by_cases hc : 0≤c
      ·
        by_cases hd : 0≤d
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hk' : c*d-(-a)*f=5 ∨ c*d-(-a)*f=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound c d (-a) f hcpos hdpos hapos hfpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤c+d)
          have hcross2 := mul_nonneg (by omega : 0≤f-2) (by omega : 0≤c+d)
          nlinarith [hq,hbound,hcross1,hcross2]
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hAF : 4≤(-a)*f := by nlinarith [mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤f-2)]
          have hCD : 4≤c*(-d) := by nlinarith [mul_nonneg (by omega : 0≤c-2) (by omega : 0≤(-d)-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
      ·
        by_cases hd : 0≤d
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hAF : 4≤(-a)*f := by nlinarith [mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤f-2)]
          have hCD : 4≤(-c)*d := by nlinarith [mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤d-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfpos : 2≤f := by simpa only [abs_of_nonneg hf] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hk' : (-c)*(-d)-(-a)*f=5 ∨ (-c)*(-d)-(-a)*f=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound (-c) (-d) (-a) f hcpos hdpos hapos hfpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤(-c)+(-d))
          have hcross2 := mul_nonneg (by omega : 0≤f-2) (by omega : 0≤(-c)+(-d))
          nlinarith [hq,hbound,hcross1,hcross2]
    ·
      by_cases hc : 0≤c
      ·
        by_cases hd : 0≤d
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hAF : 4≤(-a)*(-f) := by nlinarith [mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤(-f)-2)]
          have hCD : 4≤c*d := by nlinarith [mul_nonneg (by omega : 0≤c-2) (by omega : 0≤d-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcpos : 2≤c := by simpa only [abs_of_nonneg hc] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hk' : (-a)*(-f)-c*(-d)=5 ∨ (-a)*(-f)-c*(-d)=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound (-a) (-f) c (-d) hapos hfpos hcpos hdpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤c-2) (by omega : 0≤(-a)+(-f))
          have hcross2 := mul_nonneg (by omega : 0≤(-d)-2) (by omega : 0≤(-a)+(-f))
          nlinarith [hq,hbound,hcross1,hcross2]
      ·
        by_cases hd : 0≤d
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdpos : 2≤d := by simpa only [abs_of_nonneg hd] using hd2
          have hk' : (-a)*(-f)-(-c)*d=5 ∨ (-a)*(-f)-(-c)*d=-3 := by
            rcases hk with hk | hk
            · left; nlinarith [hk]
            · right; nlinarith [hk]
          have hbound := opposed_pair_bound (-a) (-f) (-c) d hapos hfpos hcpos hdpos hk'
          have hcross1 := mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤(-a)+(-f))
          have hcross2 := mul_nonneg (by omega : 0≤d-2) (by omega : 0≤(-a)+(-f))
          nlinarith [hq,hbound,hcross1,hcross2]
        ·
          have haneg : a≤0 := by omega
          have hapos : 2≤-a := by simpa only [abs_of_nonpos haneg] using ha2
          have hfneg : f≤0 := by omega
          have hfpos : 2≤-f := by simpa only [abs_of_nonpos hfneg] using hf2
          have hcneg : c≤0 := by omega
          have hcpos : 2≤-c := by simpa only [abs_of_nonpos hcneg] using hc2
          have hdneg : d≤0 := by omega
          have hdpos : 2≤-d := by simpa only [abs_of_nonpos hdneg] using hd2
          have hAF : 4≤(-a)*(-f) := by nlinarith [mul_nonneg (by omega : 0≤(-a)-2) (by omega : 0≤(-f)-2)]
          have hCD : 4≤(-c)*(-d) := by nlinarith [mul_nonneg (by omega : 0≤(-c)-2) (by omega : 0≤(-d)-2)]
          rcases hk with hk | hk <;> nlinarith [hAF,hCD]

private theorem square_twelve_bounds (x : ℤ) (hx : x^2≤12) : -3≤x ∧ x≤3 := by
  constructor <;> nlinarith [sq_nonneg (x-3),sq_nonneg (x+3)]

/-- A zero outer pairing is incompatible with the crossed positive unit pair. -/
theorem crossing_zero_outer_impossible (c d f : ℤ)
    (hq : c^2+d^2+f^2-(c+d)*f+2=8) (hk : c*d=5 ∨ c*d=-3) : False := by
  have hs : (2*f-c-d)^2+3*c^2+3*d^2-2*c*d=24 := by nlinarith [hq]
  have hc2 : c^2≤12 := by
    rcases hk with hk | hk <;> nlinarith [hs,sq_nonneg (2*f-c-d),sq_nonneg d]
  have hd2 : d^2≤12 := by
    rcases hk with hk | hk <;> nlinarith [hs,sq_nonneg (2*f-c-d),sq_nonneg c]
  obtain ⟨hc0,hc3⟩ := square_twelve_bounds c hc2
  obtain ⟨hd0,hd3⟩ := square_twelve_bounds d hd2
  interval_cases c <;> interval_cases d <;> norm_num at hk
  all_goals nlinarith [hs,sq_nonneg (2*f-c-d)]

private theorem dvd_twenty_seven_cases (x : ℤ) (hx : x∣27) :
    x=-27 ∨ x=-9 ∨ x=-3 ∨ x=-1 ∨ x=1 ∨ x=3 ∨ x=9 ∨ x=27 := by
  have hn : x.natAbs≤27 := Int.natAbs_le_of_dvd_ne_zero hx (by decide)
  have hh : |x|≤27 := by
    have hh : (x.natAbs:ℤ)≤27 := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hh
  obtain ⟨hlo,hhi⟩ := abs_le.mp hh
  interval_cases x <;> norm_num at hx
  all_goals norm_num

private theorem shifted_dvd_twenty_seven_cases (x : ℤ) (hx : (x+1)∣27) :
    x=-28 ∨ x=-10 ∨ x=-4 ∨ x=-2 ∨ x=0 ∨ x=2 ∨ x=8 ∨ x=26 := by
  have h := dvd_twenty_seven_cases (x+1) hx
  omega

/-- A first outer unit forces a finite factorization, not a bounded-search assumption. -/
theorem crossing_first_unit_cases (c d f : ℤ)
    (hq : c*d*f-d-c-c*f-d*f+c^2+d^2+f^2+3=8)
    (hk : f+c*d=5 ∨ f+c*d=-3) :
    (c=-2 ∧ d=-2 ∧ f=-7) ∨ (c=-2 ∧ d=2 ∧ f=1) ∨
      (c=2 ∧ d=-2 ∧ f=1) ∨ (c=2 ∧ d=2 ∧ f=1) := by
  have hdivs : (c+1)∣27 ∧ (d+1)∣27 := by
    rcases hk with hk | hk
    · have hf : f=5-c*d := by nlinarith [hk]
      have hfac : (c+d-7)*(c+1)*(d+1)=-27 := by rw [hf] at hq; nlinarith [hq]
      constructor
      · have hdiv : c+1∣(-27:ℤ) := ⟨(c+d-7)*(d+1),by nlinarith [hfac]⟩
        simpa only [dvd_neg] using hdiv
      · have hdiv : d+1∣(-27:ℤ) := ⟨(c+d-7)*(c+1),by nlinarith [hfac]⟩
        simpa only [dvd_neg] using hdiv
    · have hf : f=-3-c*d := by nlinarith [hk]
      have hfac : (c+d+1)*(c+1)*(d+1)=-3 := by rw [hf] at hq; nlinarith [hq]
      constructor
      · have hdiv : c+1∣(-3:ℤ) := ⟨(c+d+1)*(d+1),by nlinarith [hfac]⟩
        exact dvd_trans hdiv (by decide : (-3:ℤ)∣27)
      · have hdiv : d+1∣(-3:ℤ) := ⟨(c+d+1)*(c+1),by nlinarith [hfac]⟩
        exact dvd_trans hdiv (by decide : (-3:ℤ)∣27)
  have hc := shifted_dvd_twenty_seven_cases c hdivs.1
  have hd := shifted_dvd_twenty_seven_cases d hdivs.2
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
  all_goals rcases hd with hd | hd | hd | hd | hd | hd | hd | hd
  all_goals rcases hk with hk | hk
  all_goals have hf : f=5-c*d ∨ f=-3-c*d := by omega
  all_goals rcases hf with hf | hf
  all_goals subst c <;> subst d <;> subst f
  all_goals norm_num at hq
  all_goals norm_num


private theorem crossing_equations (z : Six) (hz : isSolution z)
    (hb : z.b=1) (he : z.e=1) :
    z.a*z.c*z.d*z.f-z.a*z.d-z.a*z.c-z.c*z.f-z.d*z.f+
      z.a^2+z.c^2+z.d^2+z.f^2+2=8 ∧
      (z.a*z.f+z.c*z.d=5 ∨ z.a*z.f+z.c*z.d=-3) := by
  constructor
  · have h := hz.1
    simp only [q1,hb,he] at h
    nlinarith [h]
  · have h : (q2 z)^2=(4:ℤ)^2 := by norm_num; exact hz.2
    have hcases := eq_or_eq_neg_of_sq_eq_sq (q2 z) (4:ℤ) h
    simp only [q2,hb,he] at hcases
    rcases hcases with h | h
    · left; nlinarith [h]
    · right; nlinarith [h]

/-- The normalized first-unit branch consists of four explicit solutions. -/
theorem first_unit_crossing_family_or_drop (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (he : z.e=1) : FamilyOrDrop z := by
  obtain ⟨hq,hk⟩ := crossing_equations z hz hb he
  have hc := crossing_first_unit_cases z.c z.d z.f
    (by rw [ha] at hq; nlinarith [hq]) (by simpa [ha] using hk)
  rcases hc with ⟨hc,hd,hf⟩ | ⟨hc,hd,hf⟩ | ⟨hc,hd,hf⟩ | ⟨hc,hd,hf⟩
  · have htuple : z=⟨1,1,-2,-2,1,-7⟩ := by ext <;> simp [ha,hb,he,hc,hd,hf]
    rw [htuple]
    right
    exact ⟨[.i1,.m2],by decide +kernel⟩
  all_goals
    left
    apply unit_boundary_triangle_reachable_family z hz
    have htuple : z=⟨1,1,z.c,z.d,1,1⟩ := by ext <;> simp [ha,hb,he,hf]
    rw [htuple,hc,hd]
    norm_num [UnitBoundaryTriangle,HasTwoUnits,NegativeTriangles.cayleyDefect]

private theorem signed_first_unit_crossing_family_or_drop (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hb : z.b=1) (he : z.e=1) : FamilyOrDrop z := by
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp ha with ha | ha
  · exact first_unit_crossing_family_or_drop z hz ha hb he
  · have hr : Reachable z (eps3 (eps1 z)) := ⟨[.s1,.s3],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr
      (by simp [l1,eps3,eps1])
    exact first_unit_crossing_family_or_drop (eps3 (eps1 z))
      (reachable_preserves_solution hr hz)
      (by simp [eps3,eps1,ha]) (by simp [eps3,eps1,hb]) (by simp [eps3,eps1,he])

private theorem small_first_crossing_family_or_drop (z : Six) (hz : isSolution z)
    (ha : |z.a|≤1) (hb : z.b=1) (he : z.e=1) : FamilyOrDrop z := by
  by_cases ha0 : z.a=0
  · obtain ⟨hq,hk⟩ := crossing_equations z hz hb he
    exact False.elim (crossing_zero_outer_impossible z.c z.d z.f
      (by rw [ha0] at hq; nlinarith [hq]) (by simpa [ha0] using hk))
  · apply signed_first_unit_crossing_family_or_drop z hz (by
      have h := abs_pos.mpr ha0
      omega) hb he

/-- Crossed positive units always reduce, with no bound on the other coefficients. -/
theorem positive_crossing_units_family_or_drop (z : Six) (hz : isSolution z)
    (hb : z.b=1) (he : z.e=1) : FamilyOrDrop z := by
  have hsmall : |z.a|≤1 ∨ |z.c|≤1 ∨ |z.d|≤1 ∨ |z.f|≤1 := by
    by_contra hn
    have ha2 : 2≤|z.a| := by omega
    have hc2 : 2≤|z.c| := by omega
    have hd2 : 2≤|z.d| := by omega
    have hf2 : 2≤|z.f| := by omega
    obtain ⟨hq,hk⟩ := crossing_equations z hz hb he
    exact crossing_outer_all_two_impossible z.a z.c z.d z.f ha2 hc2 hd2 hf2 hq hk
  rcases hsmall with ha | hc | hd | hf
  · exact small_first_crossing_family_or_drop z hz ha hb he
  · apply CyclicMutation.family_or_drop_transfer z 3
    exact small_first_crossing_family_or_drop (CyclicMutation.cyclePower z 3)
      (CyclicMutation.cyclePower_solution z hz 3)
      (by simpa using hc)
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])
  · apply CyclicMutation.family_or_drop_transfer z 1
    exact small_first_crossing_family_or_drop (CyclicMutation.cyclePower z 1)
      (CyclicMutation.cyclePower_solution z hz 1)
      (by simpa using hd)
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])
  · apply CyclicMutation.family_or_drop_transfer z 2
    exact small_first_crossing_family_or_drop (CyclicMutation.cyclePower z 2)
      (CyclicMutation.cyclePower_solution z hz 2)
      (by simpa using hf)
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])
      (by simp [CyclicMutation.cyclePower,CyclicMutation.cycle,hb,he])

/-- Either sign is permitted on both crossed unit edges. This is an actual
family reachability or strict original-height descent, without a classification premise. -/
theorem signed_crossing_units_family_or_drop (z : Six) (hz : isSolution z)
    (hb : |z.b|=1) (he : |z.e|=1) : FamilyOrDrop z := by
  have normalized_b (w : Six) (hw : isSolution w) (hwb : w.b=1)
      (hwe : |w.e|=1) : FamilyOrDrop w := by
    rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hwe with hwe | hwe
    · exact positive_crossing_units_family_or_drop w hw hwb hwe
    · have hr : Reachable w (eps2 w) := ⟨[.s2],rfl⟩
      apply familyOrDrop_of_reachable_same_height hr (l1_eps2 w)
      exact positive_crossing_units_family_or_drop (eps2 w)
        (reachable_preserves_solution hr hw) (by simpa [eps2] using hwb)
        (by simp [eps2,hwe])
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hb with hb | hb
  · exact normalized_b z hz hb he
  · have hr : Reachable z (eps1 z) := ⟨[.s1],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (by simp [l1,eps1])
    exact normalized_b (eps1 z) (reachable_preserves_solution hr hz)
      (by simp [eps1,hb]) (by simpa [eps1] using he)

end SerreMarkov.NegativeCrossingUnits
