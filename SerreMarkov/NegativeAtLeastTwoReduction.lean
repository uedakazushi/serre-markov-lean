import SerreMarkov.NegativeTwoPositive
import SerreMarkov.NegativeDiagonalDescent
import SerreMarkov.NegativePositiveDescent
import SerreMarkov.CyclicMutation

/-! # Positive reductions at edges of size two

All descent conclusions compare with the height of the original tuple.
-/

namespace SerreMarkov.NegativeAtLeastTwoReduction

open NegativeDescent NegativeTriangles NegativeBoundary NegativeTwoEdge
open NegativeDiagonalDescent

def AtLeastTwoPositive (z : Six) : Prop :=
  2 ≤ z.a ∧ 2 ≤ z.b ∧ 2 ≤ z.c ∧ 2 ≤ z.d ∧ 2 ≤ z.e ∧ 2 ≤ z.f

theorem oneStepDrop_familyOrDrop (z : Six) (h : OneStepDrop z) : FamilyOrDrop z := by
  right
  rcases h with h | h | h | h | h | h
  · exact ⟨[.m1],h⟩
  · exact ⟨[.i1],h⟩
  · exact ⟨[.m2],h⟩
  · exact ⟨[.i2],h⟩
  · exact ⟨[.m3],h⟩
  · exact ⟨[.i3],h⟩

theorem triangle_weak_descent (u v w : ℤ) (hu : 2 ≤ u) (hv : 2 ≤ v)
    (hw : 2 ≤ w) (hum : u ≤ w) (hvm : v ≤ w)
    (ht : 4 ≤ cayleyDefect u v w) : |u*v-w| ≤ w := by
  by_cases hu2 : u=2
  · subst u
    exact abs_le.mpr ⟨by omega,by omega⟩
  by_cases hv2 : v=2
  · subst v
    exact abs_le.mpr ⟨by omega,by omega⟩
  exact (cayley_positive_abs_descent u v w (by omega) (by omega) (by omega)
    ⟨hum,hvm⟩ ht).le

theorem b_two_opposite_max (z : Six) (hz : isSolution z)
    (hp : AtLeastTwoPositive z) (hb : z.b=2) :
    z.a ≤ z.e ∧ z.c ≤ z.e ∧ z.d ≤ z.e ∧ z.f ≤ z.e := by
  obtain ⟨ha,hb',hc,hd,he,hf⟩ := hp
  have hq : q2 z ≤ 4 := by nlinarith [hz.2]
  simp only [q2,hb] at hq
  have haf4 : 4 ≤ z.a*z.f := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.a-2) (by omega : 0 ≤ z.f-2)]
  have hcd4 : 4 ≤ z.c*z.d := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.c-2) (by omega : 0 ≤ z.d-2)]
  have ha2 : 2*z.a ≤ z.a*z.f := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.a) (by omega : 0 ≤ z.f-2)]
  have hf2 : 2*z.f ≤ z.a*z.f := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.a-2) (by omega : 0 ≤ z.f)]
  have hc2 : 2*z.c ≤ z.c*z.d := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.c) (by omega : 0 ≤ z.d-2)]
  have hd2 : 2*z.d ≤ z.c*z.d := by
    nlinarith [mul_nonneg (by omega : 0 ≤ z.c-2) (by omega : 0 ≤ z.d)]
  omega

theorem b_two_equal_family (z : Six) (hz : isSolution z)
    (hb : z.b=2) (heq : z.a=z.d) : ∃ x y : ℤ, Reachable z (family x y) := by
  let w := inv2 z
  have hr : Reachable z w := ⟨[.i2],rfl⟩
  obtain ⟨x,y,hw⟩ := affine_edge_equal_reachable_family w
    (reachable_preserves_solution hr hz) (by simp [w,inv2,hb])
    (Or.inl (by simp [w,inv2,hb,heq]; ring))
  exact ⟨x,y,reachable_trans hr hw⟩

theorem b_two_unequal_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z)
    (hb : z.b=2) (heq : z.a≠z.d) : OneStepDrop z := by
  obtain ⟨ha,hb',hc,hd,he,hf⟩ := hp
  obtain ⟨hae,hce,hde,hfe⟩ := b_two_opposite_max z hz ⟨ha,hb',hc,hd,he,hf⟩ hb
  obtain ⟨ht1,ht2,ht3,ht4⟩ := negative_triangle_inequalities z hz hneg
  by_cases had : z.a ≤ z.d
  · have hstrict : |2*z.a-z.d| < z.d := abs_lt.mpr ⟨by omega,by omega⟩
    have hweak := triangle_weak_descent z.a z.c z.e ha hc he hae hce ht2
    left
    apply (mu1_drop_iff z).mpr
    simpa only [hb,mul_comm z.a (2:ℤ),abs_of_nonneg (by omega : 0 ≤ z.d),
      abs_of_nonneg (by omega : 0 ≤ z.e)] using add_lt_add_of_lt_of_le hstrict hweak
  · have hstrict : |2*z.d-z.a| < z.a := abs_lt.mpr ⟨by omega,by omega⟩
    have ht4' : 4 ≤ cayleyDefect z.d z.f z.e := by
      convert ht4 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hweak := triangle_weak_descent z.d z.f z.e hd hf he hde hfe ht4'
    right; right; right; left
    apply (inv2_drop_iff z).mpr
    simpa only [hb,abs_of_nonneg (by omega : 0 ≤ z.a),
      abs_of_nonneg (by omega : 0 ≤ z.e)] using add_lt_add_of_lt_of_le hstrict hweak

theorem positive_b_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z)
    (hb : z.b=2) : FamilyOrDrop z := by
  by_cases heq : z.a=z.d
  · exact Or.inl (b_two_equal_family z hz hb heq)
  exact oneStepDrop_familyOrDrop z (b_two_unequal_drop z hz hneg hp hb heq)

theorem reverse_solution (z : Six) (hz : isSolution z) : isSolution (reverse z) := by
  constructor
  · convert hz.1 using 1 <;> dsimp [reverse,q1] <;> ring
  · simpa only [reverse_q2] using hz.2

theorem reverse_negative (z : Six) (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    IntrinsicSigns.thirdMinorSum (reverse z) < 0 := by
  change negativeMarker (reverse z) < 0
  have heq : negativeMarker (reverse z)=negativeMarker z := by
    dsimp [reverse,negativeMarker]; ring
  rw [heq]
  exact hneg

theorem positive_e_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z)
    (he : z.e=2) : FamilyOrDrop z := by
  obtain ⟨ha,hb,hc,hd,he',hf⟩ := hp
  by_cases heq : z.f=z.d
  · left
    let w := mu2 z
    have hr : Reachable z w := ⟨[.m2],rfl⟩
    obtain ⟨x,y,hw⟩ := right_affine_equal_family w (reachable_preserves_solution hr hz)
      (by simp [w,mu2,he]) (Or.inr (by simp [w,mu2,he,heq]; ring))
    exact ⟨x,y,reachable_trans hr hw⟩
  · apply oneStepDrop_familyOrDrop
    apply oneStepDrop_of_reverse
    exact b_two_unequal_drop (reverse z) (reverse_solution z hz) (reverse_negative z hneg)
      ⟨hf,he',hc,hd,hb,ha⟩ (by simpa [reverse] using he) (by simpa [reverse] using heq)

theorem positive_f_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z)
    (hf : z.f=2) : FamilyOrDrop z := by
  obtain ⟨ha,hb,hc,hd,he,hf'⟩ := hp
  by_cases ha2 : z.a=2
  · exact Or.inl (endpoint_two_reachable_family z hz (Or.inl ha2) (Or.inl hf))
  by_cases hbc : z.b=z.c
  · exact Or.inl (right_affine_equal_family z hz hf (Or.inl hbc))
  by_cases hde : z.d=z.e
  · exact Or.inl (right_affine_equal_family z hz hf (Or.inr hde))
  apply oneStepDrop_familyOrDrop
  apply oneStepDrop_of_reverse
  exact NegativeTwoPositive.positive_two_edge_descent (reverse z)
    (reverse_solution z hz) (reverse_negative z hneg) (by simpa [reverse] using hf)
    he hc hd hb (by simp [reverse]; omega) (by simp [reverse]; omega)
    (by simp [reverse]; omega)

theorem positive_cyclic_two_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z)
    (n : ℕ) (ha : (CyclicMutation.cyclePower z n).a=2) : FamilyOrDrop z := by
  have hp' := CyclicMutation.cyclePower_coordinates (fun t : ℤ => 2 ≤ t) z n hp
  obtain ⟨ha',hb,hc,hd,he,hf⟩ := hp'
  have hred := NegativeTwoPositive.positive_two_edge_reduction
    (CyclicMutation.cyclePower z n) (CyclicMutation.cyclePower_solution z hz n)
    (CyclicMutation.cyclePower_negative z hneg n) ha hb hc hd he hf
  exact CyclicMutation.family_or_drop_transfer z n hred

/-- Every positive chamber whose six coefficients are at least two has an
actual family reduction or an actual strict decrease of the original height. -/
theorem positive_atLeastTwo_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hp : AtLeastTwoPositive z) : FamilyOrDrop z := by
  by_cases ha2 : z.a=2
  · exact positive_cyclic_two_reduction z hz hneg hp 0 ha2
  by_cases hb2 : z.b=2
  · exact positive_b_two_reduction z hz hneg hp hb2
  by_cases hc2 : z.c=2
  · exact positive_cyclic_two_reduction z hz hneg hp 3 (by simpa using hc2)
  by_cases hd2 : z.d=2
  · exact positive_cyclic_two_reduction z hz hneg hp 1 (by simpa using hd2)
  by_cases he2 : z.e=2
  · exact positive_e_two_reduction z hz hneg hp he2
  by_cases hf2 : z.f=2
  · exact positive_cyclic_two_reduction z hz hneg hp 2 (by simpa using hf2)
  apply oneStepDrop_familyOrDrop
  apply NegativePositiveDescent.negative_large_positive_descent z hz hneg
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := hp
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- The sign gauge and all eight tail chambers are fully covered. -/
theorem negative_atLeastTwo_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : 2 ≤ |z.a|) (hb : 2 ≤ |z.b|) (hc : 2 ≤ |z.c|)
    (hd : 2 ≤ |z.d|) (he : 2 ≤ |z.e|) (hf : 2 ≤ |z.f|) : FamilyOrDrop z := by
  obtain ⟨s,hs,ha',hb',hc',hr,hl⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  obtain ⟨habsA,habsB,habsC,habsD,habsE,habsF⟩ := SignGaugeDescent.signedSix_abs z s hs
  let w := PositiveNormalization.signedSix z s
  have hwa : 2 ≤ w.a := by dsimp [w]; omega
  have hwb : 2 ≤ w.b := by dsimp [w]; omega
  have hwc : 2 ≤ w.c := by dsimp [w]; omega
  have hwd : 2 ≤ |w.d| := by dsimp [w]; omega
  have hwe : 2 ≤ |w.e| := by dsimp [w]; omega
  have hwf : 2 ≤ |w.f| := by dsimp [w]; omega
  have hw : isSolution w := reachable_preserves_solution hr hz
  have hwn : IntrinsicSigns.thirdMinorSum w < 0 := by
    change negativeMarker (PositiveNormalization.signedSix z s) < 0
    rw [SignGaugeDescent.negativeMarker_signedSix z s hs]
    exact hneg
  apply familyOrDrop_of_gauge z s hs
  by_cases hminus : w.d<0 ∨ w.e<0 ∨ w.f<0
  · exact nonpositive_tail_atLeastTwo_reduction w hw hwn hwa hwb hwc hwd hwe hwf hminus
  · apply positive_atLeastTwo_reduction w hw hwn
    have hdn : 0 ≤ w.d := by omega
    have hen : 0 ≤ w.e := by omega
    have hfn : 0 ≤ w.f := by omega
    rw [abs_of_nonneg hdn] at hwd
    rw [abs_of_nonneg hen] at hwe
    rw [abs_of_nonneg hfn] at hwf
    exact ⟨hwa,hwb,hwc,hwd,hwe,hwf⟩

end SerreMarkov.NegativeAtLeastTwoReduction
