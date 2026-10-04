import SerreMarkov.ZeroIncidentBoundary
import SerreMarkov.CyclicMutation
import SerreMarkov.NegativeZeroOffdiagonal
import SerreMarkov.DescentTransfer

/-! # Crossing zero edges with nonunit outer pairings

This file proves actual nonincreasing mutation to an adjacent zero edge. The
outer four absolute pairings need only be at least two, and the remaining
crossing pairing is unrestricted. It assumes no local-descent principle.
-/
namespace SerreMarkov.ZeroCrossingBoundary
open NegativeDescent
set_option linter.unusedSimpArgs false

private theorem positive_phase_of_discriminant (T U E : ℤ)
    (hT : 0<T) (hU : U<0) (hE : 0 ≤ E)
    (hDT : T^2 ≤ (2*E-T-U)^2) (hDU : U^2 ≤ (2*E-T-U)^2) :
    |T-E| ≤ |E| := by
  have hTE : T ≤ 2*E := by
    by_contra h
    have hsmall : 2*E<T := by omega
    have hP : 0 ≤ (2*E-U)*(2*E-U-2*T) := by nlinarith [hDT]
    have hQ : 0 ≤ (2*E-T)*(2*E-T-2*U) := by nlinarith [hDU]
    have hA : 0<2*E-U := by omega
    have hB : 0 ≤ 2*E-U-2*T := by
      by_contra hn
      have hp := mul_neg_of_pos_of_neg hA (by omega : 2*E-U-2*T<0)
      omega
    have hC : 2*E-T<0 := by omega
    have hD : 2*E-T-2*U ≤ 0 := by
      by_contra hn
      have hp := mul_neg_of_neg_of_pos hC (by omega : 0<2*E-T-2*U)
      omega
    omega
  rw [abs_of_nonneg hE]
  exact abs_le.mpr ⟨by omega,by omega⟩

/-- Opposite-sign quadratic phases need only weak discriminant inequalities
for a nonincreasing reflection to exist. -/
theorem quadratic_phase_of_discriminant (T U E : ℤ) (hTU : T*U<0)
    (hDT : T^2 ≤ (2*E-T-U)^2) (hDU : U^2 ≤ (2*E-T-U)^2) :
    |T-E| ≤ |E| ∨ |U-E| ≤ |E| := by
  have positive_negative (T U : ℤ) (hT : 0<T) (hU : U<0)
      (hDT : T^2 ≤ (2*E-T-U)^2) (hDU : U^2 ≤ (2*E-T-U)^2) :
      |T-E| ≤ |E| ∨ |U-E| ≤ |E| := by
    by_cases hE : 0 ≤ E
    · exact Or.inl (positive_phase_of_discriminant T U E hT hU hE hDT hDU)
    · have h := positive_phase_of_discriminant (-U) (-T) (-E) (by omega)
        (by omega) (by omega) (by nlinarith [hDU]) (by nlinarith [hDT])
      right
      calc
        |U-E|=|E-U| := abs_sub_comm U E
        _ = |-U- -E| := by congr 1; ring
        _  ≤  |-E| := h
        _ = |E| := abs_neg E
  rcases mul_neg_iff.mp hTU with ⟨hT,hU⟩ | ⟨hT,hU⟩
  · exact positive_negative T U hT hU hDT hDU
  · rcases positive_negative U T hU hT
      (by nlinarith [hDU]) (by nlinarith [hDT]) with h | h
    · exact Or.inr h
    · exact Or.inl h

private theorem abs_two_square (n : ℤ) (h : 2 ≤ |n|) : 4 ≤ n^2 := by
  nlinarith [sq_abs n,sq_nonneg (|n|-2)]

/-- Determinant four forces a nonincreasing crossing phase when each outer
absolute factor is at least two. -/
theorem crossing_phase_nonincrease (a c d f E : ℤ)
    (ha : 2 ≤ |a|) (hc : 2 ≤ |c|) (hd : 2 ≤ |d|) (hf : 2 ≤ |f|)
    (hp : (a*f+c*d)^2=16)
    (hq : E^2-(a*c+d*f)*E+a*c*d*f+(a^2+c^2+d^2+f^2)=8) :
    |a*c-E| ≤ |E| ∨ |d*f-E| ≤ |E| := by
  have ha4 := abs_two_square a ha
  have hc4 := abs_two_square c hc
  have hd4 := abs_two_square d hd
  have hf4 := abs_two_square f hf
  have hAF : 4 ≤ |a*f| := by
    rw [abs_mul]
    nlinarith [mul_nonneg (by omega : 0 ≤ |a|-2) (by omega : 0 ≤ |f|-2)]
  have hCD : 4 ≤ |c*d| := by
    rw [abs_mul]
    nlinarith [mul_nonneg (by omega : 0 ≤ |c|-2) (by omega : 0 ≤ |d|-2)]
  have hAFsq : 16 ≤ (a*f)^2 := by nlinarith [sq_abs (a*f),sq_nonneg (|a*f|-4)]
  have hCDsq : 16 ≤ (c*d)^2 := by nlinarith [sq_abs (c*d),sq_nonneg (|c*d|-4)]
  have hTU : (a*c)*(d*f)<0 := by
    by_contra hn
    have hn0 : 0 ≤ (a*c)*(d*f) := by omega
    nlinarith only [hp,hAFsq,hCDsq,hn0]
  have hfactorAF := mul_nonneg (by omega : 0 ≤ a^2-4) (by omega : 0 ≤ f^2-4)
  have hfactorCD := mul_nonneg (by omega : 0 ≤ c^2-4) (by omega : 0 ≤ d^2-4)
  have hbound : 2*((a*c)*(d*f))+4*(a^2+c^2+d^2+f^2) ≤ 48 := by
    nlinarith only [hp,hfactorAF,hfactorCD]
  have hACsq : 16 ≤ (a*c)^2 := by
    have hAC : 4 ≤ |a*c| := by
      rw [abs_mul]
      nlinarith [mul_nonneg (by omega : 0 ≤ |a|-2) (by omega : 0 ≤ |c|-2)]
    nlinarith [sq_abs (a*c),sq_nonneg (|a*c|-4)]
  have hDFsq : 16 ≤ (d*f)^2 := by
    have hDF : 4 ≤ |d*f| := by
      rw [abs_mul]
      nlinarith [mul_nonneg (by omega : 0 ≤ |d|-2) (by omega : 0 ≤ |f|-2)]
    nlinarith [sq_abs (d*f),sq_nonneg (|d*f|-4)]
  apply quadratic_phase_of_discriminant (a*c) (d*f) E hTU
  · nlinarith only [hq,hbound,hDFsq]
  · nlinarith only [hq,hbound,hACsq]

private theorem integer_height_le (z w : Six) (h : integerL1 w ≤ integerL1 z) : l1 w ≤ l1 z := by
  rw [integerL1_cast,integerL1_cast] at h
  exact_mod_cast h

/-- One actual forward or inverse move takes the crossing zero `b=0` to an
adjacent zero while never increasing L1. -/
theorem zero_b_nonincreasing_to_adjacent (z : Six) (hz : isSolution z)
    (hzero : z.b=0) (ha : 2 ≤ |z.a|) (hc : 2 ≤ |z.c|)
    (hd : 2 ≤ |z.d|) (hf : 2 ≤ |z.f|) :
    ∃ w : Six,Reachable z w ∧ l1 w ≤ l1 z ∧ (w.a=0 ∨ w.d=0) := by
  have hq1 := hz.1
  have hq2 := hz.2
  simp only [q1,q2,hzero,zero_mul,mul_zero,add_zero,sub_zero,
    zero_pow (by decide : 2≠0)] at hq1 hq2
  rcases crossing_phase_nonincrease z.a z.c z.d z.f z.e ha hc hd hf hq2
    (by nlinarith only [hq1]) with hphase | hphase
  · refine ⟨mu1 z,⟨[.m1],rfl⟩,?_,Or.inr ?_⟩
    · apply integer_height_le
      simp [integerL1,mu1,hzero]
      omega
    · simp [mu1,hzero]
  · refine ⟨inv2 z,⟨[.i2],rfl⟩,?_,Or.inl ?_⟩
    · apply integer_height_le
      simp [integerL1,inv2,hzero]
      omega
    · simp [inv2,hzero]

/-- The second crossing zero has the same nonincreasing adjacent-zero reduction. -/
theorem zero_e_nonincreasing_to_adjacent (z : Six) (hz : isSolution z)
    (hzero : z.e=0) (ha : 2 ≤ |z.a|) (hc : 2 ≤ |z.c|)
    (hd : 2 ≤ |z.d|) (hf : 2 ≤ |z.f|) :
    ∃ w : Six,Reachable z w ∧ l1 w ≤ l1 z ∧ (w.d=0 ∨ w.f=0) := by
  have hq1 := hz.1
  have hq2 := hz.2
  simp only [q1,q2,hzero,zero_mul,mul_zero,add_zero,sub_zero,
    zero_pow (by decide : 2≠0)] at hq1 hq2
  rcases crossing_phase_nonincrease z.a z.d z.c z.f z.b ha hd hc hf
    (by nlinarith only [hq2]) (by nlinarith only [hq1]) with hphase | hphase
  · refine ⟨mu2 z,⟨[.m2],rfl⟩,?_,Or.inr ?_⟩
    · apply integer_height_le
      simp [integerL1,mu2,hzero]
      omega
    · simp [mu2,hzero]
  · refine ⟨inv3 z,⟨[.i3],rfl⟩,?_,Or.inl ?_⟩
    · apply integer_height_le
      simp [integerL1,inv3,hzero,mul_comm]
      omega
    · simp [inv3,hzero]


private theorem reachable_negative {z w : Six} (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hr : Reachable z w) :
    IntrinsicSigns.thirdMinorSum w<0 := by
  have hw := reachable_preserves_solution hr hz
  apply (intrinsicKind_negative_iff w hw).mp
  rw [← reachable_intrinsicKind hz hr]
  exact (intrinsicKind_negative_iff z hz).mpr hneg

/-- Complete crossing-zero reduction when the four outer edges are nonunit.
The crossing edge opposite the zero is arbitrary. -/
theorem zero_b_outer_atLeastTwo_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hzero : z.b=0)
    (ha : 2 ≤ |z.a|) (hc : 2 ≤ |z.c|) (hd : 2 ≤ |z.d|) (hf : 2 ≤ |z.f|) :
    NegativeTwoEdge.FamilyOrDrop z := by
  obtain ⟨w,hr,hle,hzero⟩ := zero_b_nonincreasing_to_adjacent z hz hzero ha hc hd hf
  apply DescentTransfer.family_or_drop_of_nonincrease hr hle
  apply NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop w
    (reachable_preserves_solution hr hz) (reachable_negative hz hneg hr)
  tauto

/-- The other crossing zero is handled by the same weak-discriminant reduction. -/
theorem zero_e_outer_atLeastTwo_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hzero : z.e=0)
    (ha : 2 ≤ |z.a|) (hc : 2 ≤ |z.c|) (hd : 2 ≤ |z.d|) (hf : 2 ≤ |z.f|) :
    NegativeTwoEdge.FamilyOrDrop z := by
  obtain ⟨w,hr,hle,hzero⟩ := zero_e_nonincreasing_to_adjacent z hz hzero ha hc hd hf
  apply DescentTransfer.family_or_drop_of_nonincrease hr hle
  apply NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop w
    (reachable_preserves_solution hr hz) (reachable_negative hz hneg hr)
  tauto


private theorem abs_atLeastTwo_of_nonunit (n : ℤ) (hn : n≠0) (hunit : |n|≠1) :
    2 ≤ |n| := by
  have hp := abs_pos.mpr hn
  omega

/-- Every negative solution with a zero edge and no unit edge has an actual
family reduction or an actual strict finite-word descent, in all six positions. -/
theorem zero_nonunit_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hzero : z.a=0 ∨ z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0)
    (hunit : |z.a|≠1 ∧ |z.b|≠1 ∧ |z.c|≠1 ∧ |z.d|≠1 ∧ |z.e|≠1 ∧ |z.f|≠1) :
    NegativeTwoEdge.FamilyOrDrop z := by
  by_cases hoff : z.a=0 ∨ z.c=0 ∨ z.d=0 ∨ z.f=0
  · exact NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop z hz hneg hoff
  · have ha0 : z.a≠0 := by tauto
    have hc0 : z.c≠0 := by tauto
    have hd0 : z.d≠0 := by tauto
    have hf0 : z.f≠0 := by tauto
    obtain ⟨ha1,_,hc1,hd1,_,hf1⟩ := hunit
    have ha := abs_atLeastTwo_of_nonunit z.a ha0 ha1
    have hc := abs_atLeastTwo_of_nonunit z.c hc0 hc1
    have hd := abs_atLeastTwo_of_nonunit z.d hd0 hd1
    have hf := abs_atLeastTwo_of_nonunit z.f hf0 hf1
    have hbOrE : z.b=0 ∨ z.e=0 := by tauto
    rcases hbOrE with hb0 | he0
    · exact zero_b_outer_atLeastTwo_family_or_drop z hz hneg hb0 ha hc hd hf
    · exact zero_e_outer_atLeastTwo_family_or_drop z hz hneg he0 ha hc hd hf

/-- The only zero-edge cases not settled in this module carry an outer unit
at a crossing zero. The remaining case is exposed as data, not postulated. -/
theorem zero_family_or_crossing_unit (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hzero : z.a=0 ∨ z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0) :
    NegativeTwoEdge.FamilyOrDrop z ∨
      ((z.b=0 ∨ z.e=0) ∧ (|z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1)) := by
  by_cases hoff : z.a=0 ∨ z.c=0 ∨ z.d=0 ∨ z.f=0
  · exact Or.inl (NegativeZeroOffdiagonal.offdiagonal_zero_family_or_drop z hz hneg hoff)
  · have ha0 : z.a≠0 := by tauto
    have hc0 : z.c≠0 := by tauto
    have hd0 : z.d≠0 := by tauto
    have hf0 : z.f≠0 := by tauto
    have hbOrE : z.b=0 ∨ z.e=0 := by tauto
    by_cases hunit : |z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1
    · exact Or.inr ⟨hbOrE,hunit⟩
    · left
      have ha := abs_atLeastTwo_of_nonunit z.a ha0 (by tauto)
      have hc := abs_atLeastTwo_of_nonunit z.c hc0 (by tauto)
      have hd := abs_atLeastTwo_of_nonunit z.d hd0 (by tauto)
      have hf := abs_atLeastTwo_of_nonunit z.f hf0 (by tauto)
      rcases hbOrE with hb0 | he0
      · exact zero_b_outer_atLeastTwo_family_or_drop z hz hneg hb0 ha hc hd hf
      · exact zero_e_outer_atLeastTwo_family_or_drop z hz hneg he0 ha hc hd hf


/-- Finite fundamental unit-zero configurations have actual braid certificates. -/
theorem unit_zero_seed_one_reachable_family :
    Reachable (⟨1,0,1,2,2,2⟩ : Six) (family 1 (-2)) := by
  refine ⟨[.i3,.s1],?_⟩
  decide

theorem unit_zero_seed_two_reachable_family :
    Reachable (⟨1,0,2,2,1,0⟩ : Six) (family 1 0) := by
  refine ⟨[.m1,.m3,.s2],?_⟩
  decide

theorem unit_zero_seed_three_reachable_family :
    Reachable (⟨1,0,1,2,3,2⟩ : Six) (family 1 (-2)) := by
  refine ⟨[.i1,.m3,.s1],?_⟩
  decide

theorem unit_zero_seed_four_reachable_family :
    Reachable (⟨1,0,3,2,1,-2⟩ : Six) (family (-1) 2) := by
  refine ⟨[.i1,.m2,.m2,.i3,.s2],?_⟩
  decide

end SerreMarkov.ZeroCrossingBoundary
