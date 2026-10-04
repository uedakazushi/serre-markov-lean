import SerreMarkov.UnitZeroMonodromy
import SerreMarkov.ZeroCrossingBoundary
import SerreMarkov.ZeroUnitConicImpossible

/-! # Actual reduction of the unit-zero Pell conic
The arithmetic reductions here are realized by six-letter braid loops.
-/
namespace SerreMarkov.ZeroUnitConic
open NegativeDescent UnitZeroMonodromy
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

private theorem conic_swap (c e : ℤ) : unitZeroConic 2 e c=unitZeroConic 2 c e := by
  unfold unitZeroConic
  ring

private theorem positive_difference (P N : ℤ) (hP : 4 ≤ P) (hN : 1 ≤ N)
    (hNP : N ≤ P) (hF : unitZeroConic 2 P (-N)=0) : 5 ≤ P-N := by
  unfold unitZeroConic at hF
  norm_num at hF
  by_contra hn
  have hsmall : P-N ≤ 4 := by omega
  have hfactor := mul_nonpos_of_nonneg_of_nonpos
    (by omega : 0 ≤ P-N) (by omega : P-N-4 ≤ 0)
  have hfactor2 := mul_nonneg (by omega : 0 ≤ P-4) (by omega : 0 ≤ N)
  nlinarith only [hF,hfactor,hfactor2,hP]

private theorem forward_positive_root (P N : ℤ) (hP : 4 ≤ P) (hN : 4 ≤ N)
    (hNP : N ≤ P) (hF : unitZeroConic 2 P (-N)=0) :
    0 < 8-P+3*N ∧ 8-P+3*N < N ∧ 5 ≤ P-N := by
  have hgap := positive_difference P N hP (by omega) hNP hF
  have hraw := hF
  unfold unitZeroConic at hraw
  norm_num at hraw
  have hprod : P*(8-P+3*N)=N^2+8*N+13 := by nlinarith only [hraw]
  have hpositive : 0 < 8-P+3*N := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ P)
      (by omega : 8-P+3*N ≤ 0)
    nlinarith [sq_nonneg N]
  have hdiag : (N-P)*(N-(8-P+3*N))<0 := by
    nlinarith only [hraw,hN,sq_nonneg (N-4)]
  have hless : 8-P+3*N < N := by
    by_contra hn
    have hm := mul_nonneg_of_nonpos_of_nonpos
      (by omega : N-P ≤ 0) (by omega : N-(8-P+3*N) ≤ 0)
    omega
  exact ⟨hpositive,hless,hgap⟩

private theorem inverse_positive_root (P N : ℤ) (hP : 4 ≤ P) (hN : 4 ≤ N)
    (hPN : P < N) (hF : unitZeroConic 2 P (-N)=0) :
    0 < 3*P-8-N ∧ 3*P-8-N < P ∧ 5 ≤ P-(3*P-8-N) := by
  have hraw := hF
  unfold unitZeroConic at hraw
  norm_num at hraw
  have hP6 : 6 ≤ P := by
    by_contra hn
    have hPsmall : P=4 ∨ P=5 := by omega
    rcases hPsmall with rfl | rfl
    · have hp := mul_nonneg (by omega : 0 ≤ N-5) (by omega : 0 ≤ N+1)
      nlinarith only [hraw,hp]
    · have hN8 : N < 8 := by
        by_contra hn
        have hp := mul_nonneg (by omega : 0 ≤ N-8) (by omega : 0 ≤ N+1)
        nlinarith only [hraw,hp]
      interval_cases N <;> norm_num at hraw
  have hprod : N*(3*P-8-N)=P^2-8*P+13 := by nlinarith only [hraw]
  have hpositive : 0 < 3*P-8-N := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (by omega : 0 ≤ N)
      (by omega : 3*P-8-N ≤ 0)
    have hs := mul_nonneg (by omega : 0 ≤ P-6) (by omega : 0 ≤ P-2)
    nlinarith only [hprod,hm,hs]
  have hdiag : (P-N)*(P-(3*P-8-N))<0 := by
    nlinarith only [hraw,hP,sq_nonneg (P-4)]
  have hless : 3*P-8-N < P := by
    by_contra hn
    have hm := mul_nonneg_of_nonpos_of_nonpos
      (by omega : P-N ≤ 0) (by omega : P-(3*P-8-N) ≤ 0)
    omega
  have hnew : unitZeroConic 2 P (-(3*P-8-N))=0 := by
    unfold unitZeroConic
    nlinarith only [hraw]
  have hgap := positive_difference P (3*P-8-N) hP (by omega) (by omega) hnew
  exact ⟨hpositive,hless,hgap⟩

private theorem conic_same_sign_impossible (c e : ℤ) (hc : 4 ≤ |c|) (he : 4 ≤ |e|)
    (hF : unitZeroConic 2 c e=0) : c*e<0 := by
  unfold unitZeroConic at hF
  norm_num at hF
  by_contra hn
  have hnonneg : 0 ≤ c*e := by omega
  have hcne : c≠0 := by intro h; simp [h] at hc
  have hene : e≠0 := by intro h; simp [h] at he
  rcases lt_or_gt_of_ne hcne with hcneg | hcpos <;>
    rcases lt_or_gt_of_ne hene with heneg | hepos
  · rw [abs_of_neg hcneg] at hc
    rw [abs_of_neg heneg] at he
    have hp := mul_nonneg (by omega : 0 ≤ -c-4) (by omega : 0 ≤ -e-4)
    nlinarith [sq_nonneg c,sq_nonneg e]
  · have hp := mul_neg_of_neg_of_pos hcneg hepos
    omega
  · have hp := mul_neg_of_pos_of_neg hcpos heneg
    omega
  · rw [abs_of_pos hcpos] at hc
    rw [abs_of_pos hepos] at he
    have hp := mul_nonneg (by omega : 0 ≤ c-4) (by omega : 0 ≤ e-4)
    nlinarith [sq_nonneg (c-4),sq_nonneg (e-4)]

/-- Outside a finite fundamental region, a six-letter actual braid loop
strictly decreases the full six-coordinate L1 height of the Pell slice. -/
theorem conic_large_actual_descent (c e : ℤ) (hF : unitZeroConic 2 c e=0)
    (hc : 4 ≤ |c|) (he : 4 ≤ |e|) :
    (l1 (unitZeroSlice 2 e (8-c-3*e))<l1 (unitZeroSlice 2 c e)) ∨
      (l1 (unitZeroSlice 2 (8-e-3*c) c)<l1 (unitZeroSlice 2 c e)) := by
  have hop := conic_same_sign_impossible c e hc he hF
  rcases mul_neg_iff.mp hop with ⟨hcpos,heneg⟩ | ⟨hcneg,hepos⟩
  · have hP : 4 ≤ c := by simpa [abs_of_pos hcpos] using hc
    have hN : 4 ≤ -e := by simpa [abs_of_neg heneg] using he
    by_cases horder : -e ≤ c
    · obtain ⟨hRpos,hRN,hgap⟩ := forward_positive_root c (-e) hP hN horder (by simpa using hF)
      left
      rw [l1_lt_iff]
      simp [integerL1,unitZeroSlice]
      rw [abs_of_neg heneg,abs_of_pos hcpos,
        abs_of_pos (by omega : 0<8-c-3*e),
        abs_of_pos (by omega : 0<4-2*e),abs_of_neg (by omega : 4-2*c<0)]
      omega
    · obtain ⟨hMpos,hMP,hgap⟩ := inverse_positive_root c (-e) hP hN (by omega) (by simpa using hF)
      right
      rw [l1_lt_iff]
      simp [integerL1,unitZeroSlice]
      rw [abs_of_neg heneg,abs_of_pos hcpos,
        abs_of_neg (by omega : 8-e-3*c<0),
        abs_of_pos (by omega : 0<4-2*(8-e-3*c)),abs_of_neg (by omega : 4-2*c<0)]
      omega
  · have hP : 4 ≤ -c := by simpa [abs_of_neg hcneg] using hc
    have hN : 4 ≤ e := by simpa [abs_of_pos hepos] using he
    have hswap : unitZeroConic 2 e c=0 := by rw [conic_swap]; exact hF
    by_cases horder : -c ≤ e
    · obtain ⟨hRpos,hRP,hgap⟩ := forward_positive_root e (-c) hN hP horder (by simpa using hswap)
      right
      rw [l1_lt_iff]
      have htail : |4-2*(8-e-3*c)| ≤ 4+2*(8-e-3*c) := by
        exact abs_le.mpr ⟨by omega,by omega⟩
      simp [integerL1,unitZeroSlice]
      rw [abs_of_neg hcneg,abs_of_pos hepos,abs_of_pos (by omega : 0<8-e-3*c),
        abs_of_pos (by omega : 0<4-2*c)]
      omega
    · obtain ⟨hMpos,hMN,hgap⟩ := inverse_positive_root e (-c) hN hP (by omega) (by simpa using hswap)
      left
      rw [l1_lt_iff]
      simp [integerL1,unitZeroSlice]
      rw [abs_of_neg hcneg,abs_of_pos hepos,abs_of_neg (by omega : 8-c-3*e<0),
        abs_of_pos (by omega : 0<4-2*c),abs_of_neg (by omega : 4-2*e<0)]
      omega


private def Fundamental (c e : ℤ) : Prop :=
  (c=1 ∧ e=2) ∨ (c=2 ∧ e=1) ∨ (c=1 ∧ e=3) ∨ (c=3 ∧ e=1) ∨
  (c=3 ∧ e= -2) ∨ (c=11 ∧ e= -2) ∨ (c= -2 ∧ e=3) ∨ (c= -2 ∧ e=11)

private theorem fundamental_swap (c e : ℤ) : Fundamental e c ↔ Fundamental c e := by
  simp only [Fundamental]
  tauto

private theorem conic_fundamental_cases (c e : ℤ) (hF : unitZeroConic 2 c e=0)
    (hsmall : |c| ≤ 3 ∨ |e| ≤ 3) : Fundamental c e := by
  have first_small (c e : ℤ) (hF : unitZeroConic 2 c e=0) (hc : |c| ≤ 3) :
      Fundamental c e := by
    obtain ⟨hcl,hcu⟩ := abs_le.mp hc
    unfold unitZeroConic at hF
    norm_num at hF
    interval_cases c
    all_goals
      have hel : -10 ≤ e := by nlinarith [sq_nonneg (e+10)]
      have heu : e ≤ 20 := by nlinarith [sq_nonneg (e-10)]
      interval_cases e <;> norm_num [Fundamental] at *
  rcases hsmall with hc | he
  · exact first_small c e hF hc
  · apply (fundamental_swap c e).mp
    exact first_small e c (by rw [conic_swap]; exact hF) he

private theorem fundamental_reachable_family (c e : ℤ) (h : Fundamental c e) :
    ∃ x y : ℤ,Reachable (unitZeroSlice 2 c e) (family x y) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨1,-2,ZeroCrossingBoundary.unit_zero_seed_one_reachable_family⟩
  · exact ⟨1,0,ZeroCrossingBoundary.unit_zero_seed_two_reachable_family⟩
  · exact ⟨1,-2,ZeroCrossingBoundary.unit_zero_seed_three_reachable_family⟩
  · exact ⟨-1,2,ZeroCrossingBoundary.unit_zero_seed_four_reachable_family⟩
  · refine ⟨1,-2,inverseFullTwistWord++[.i1,.m3,.s1],?_⟩
    decide
  · refine ⟨-1,2,fullTwistWord++fullTwistWord++[.i1,.m2,.m2,.i3,.s2],?_⟩
    decide
  · refine ⟨-1,2,fullTwistWord++[.i1,.m2,.m2,.i3,.s2],?_⟩
    decide
  · refine ⟨1,-2,inverseFullTwistWord++inverseFullTwistWord++[.i1,.m3,.s1],?_⟩
    decide

/-- Every integer point of the unit-zero Pell conic reaches the family by
actual braid and sign moves. The recursion uses strict L1 descent. -/
theorem conic_reachable_family (c e : ℤ) (hF : unitZeroConic 2 c e=0) :
    ∃ x y : ℤ,Reachable (unitZeroSlice 2 c e) (family x y) := by
  have general : ∀ n : ℕ,∀ c e : ℤ,l1 (unitZeroSlice 2 c e)=n →
      unitZeroConic 2 c e=0 → ∃ x y : ℤ,Reachable (unitZeroSlice 2 c e) (family x y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c e heq hF
      by_cases hsmall : |c| ≤ 3 ∨ |e| ≤ 3
      · exact fundamental_reachable_family c e (conic_fundamental_cases c e hF hsmall)
      · have hc : 4 ≤ |c| := by omega
        have he : 4 ≤ |e| := by omega
        rcases conic_large_actual_descent c e hF hc he with hnext | hprev
        · have hn : l1 (unitZeroSlice 2 e (8-c-3*e))<n := by omega
          have hFnext : unitZeroConic 2 e (8-c-3*e)=0 := by
            convert conic_forward 2 c e using 1 <;> norm_num <;> linarith
          obtain ⟨x,y,hr⟩ := ih (l1 (unitZeroSlice 2 e (8-c-3*e))) hn e (8-c-3*e) rfl hFnext
          refine ⟨x,y,reachable_trans ?_ hr⟩
          simpa using reachable_fullTwist 2 c e
        · have hn : l1 (unitZeroSlice 2 (8-e-3*c) c)<n := by omega
          have hFprev : unitZeroConic 2 (8-e-3*c) c=0 := by
            convert conic_inverse 2 c e using 1 <;> norm_num <;> linarith
          obtain ⟨x,y,hr⟩ := ih (l1 (unitZeroSlice 2 (8-e-3*c) c)) hn (8-e-3*c) c rfl hFprev
          refine ⟨x,y,reachable_trans ?_ hr⟩
          simpa using reachable_inverseFullTwist 2 c e
  exact general (l1 (unitZeroSlice 2 c e)) c e rfl hF


private theorem reachable_negative {z w : Six} (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hr : Reachable z w) :
    IntrinsicSigns.thirdMinorSum w<0 := by
  have hw := reachable_preserves_solution hr hz
  apply (intrinsicKind_negative_iff w hw).mp
  rw [← reachable_intrinsicKind hz hr]
  exact (intrinsicKind_negative_iff z hz).mpr hneg

private theorem positive_unit_zero_q4_family (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=0) (hd : 2 ≤ z.d) (hk : q2 z=4) :
    ∃ x y : ℤ,Reachable z (family x y) := by
  have heq := eq_slice_of_coordinates z ha hb hk
  have hF : unitZeroConic z.d z.c z.e=0 := by
    apply (solution_slice_iff_conic z.d z.c z.e).mp
    rwa [← heq]
  have hd2 : z.d=2 := by
    by_contra hn
    have hd3 : 3 ≤ z.d := by omega
    change ZeroUnitConicImpossible.conic z.d z.c z.e=0 at hF
    exact ZeroUnitConicImpossible.conic_no_integer_root z.d z.c z.e hd3 hF
  rw [hd2] at heq hF
  rw [heq]
  exact conic_reachable_family z.c z.e hF

/-- A first unit edge and crossing zero reach the family, with all other
integer pairings unrestricted. -/
theorem positive_unit_zero_b_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (hb : z.b=0) :
    ∃ x y : ℤ,Reachable z (family x y) := by
  have htri := (NegativeTriangles.negative_triangle_inequalities z hz hneg).1
  simp only [NegativeTriangles.cayleyDefect,ha,hb] at htri
  have hdabs : 2 ≤ |z.d| := by
    have hs := sq_abs z.d
    have hn := abs_nonneg z.d
    by_contra h
    have hl : |z.d| ≤ 1 := by omega
    have hp := mul_nonpos_of_nonneg_of_nonpos hn (by omega : |z.d|-1 ≤ 0)
    nlinarith
  have positive_d (w : Six) (hw : isSolution w) (hwa : w.a=1) (hwb : w.b=0)
      (hwd : 2 ≤ w.d) : ∃ x y : ℤ,Reachable w (family x y) := by
    have hk : q2 w=4 ∨ q2 w= -4 := by
      have hq := hw.2
      have hp : (q2 w-4)*(q2 w+4)=0 := by nlinarith only [hq]
      rcases mul_eq_zero.mp hp with h | h
      · left; omega
      · right; omega
    rcases hk with hk | hk
    · exact positive_unit_zero_q4_family w hw hwa hwb hwd hk
    · have hr : Reachable w (eps4 w) := ⟨[.s4],rfl⟩
      obtain ⟨x,y,hxy⟩ := positive_unit_zero_q4_family (eps4 w)
        (reachable_preserves_solution hr hw)
        (by simpa [eps4] using hwa) (by simpa [eps4] using hwb)
        (by simpa [eps4] using hwd) (by rw [q2_eps4,hk]; norm_num)
      exact ⟨x,y,reachable_trans hr hxy⟩
  by_cases hdpos : 0 ≤ z.d
  · rw [abs_of_nonneg hdpos] at hdabs
    exact positive_d z hz ha hb hdabs
  · rw [abs_of_neg (by omega : z.d<0)] at hdabs
    have hr : Reachable z (eps3 z) := ⟨[.s3],rfl⟩
    obtain ⟨x,y,hxy⟩ := positive_d (eps3 z) (reachable_preserves_solution hr hz)
      (by simpa [eps3] using ha) (by simp [eps3,hb]) (by simpa [eps3] using hdabs)
    exact ⟨x,y,reachable_trans hr hxy⟩

/-- Two inverse braids turn the other crossing zero into `b=0` while retaining
its first unit edge. The goal is actual family reachability. -/
theorem positive_unit_zero_e_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (he : z.e=0) :
    ∃ x y : ℤ,Reachable z (family x y) := by
  let w := inv3 (inv1 z)
  have hr : Reachable z w := ⟨[.i1,.i3],rfl⟩
  have hwa : w.a=1 := by simpa [w,inv1,inv3] using ha
  have hwb : w.b=0 := by simp [w,inv1,inv3,he]
  obtain ⟨x,y,hxy⟩ := positive_unit_zero_b_reachable_family w
    (reachable_preserves_solution hr hz) (reachable_negative hz hneg hr) hwa hwb
  exact ⟨x,y,reachable_trans hr hxy⟩

private theorem cycle_crossing_zero (z : Six) (n : ℕ) (hz : z.b=0 ∨ z.e=0) :
    (CyclicMutation.cyclePower z n).b=0 ∨ (CyclicMutation.cyclePower z n).e=0 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    simpa only [CyclicMutation.cyclePower,CyclicMutation.cycle] using ih.symm

/-- All four possible outer units at either crossing zero reach the family.
Cyclic mutation transports the unit, and explicit vertex gauges handle its sign. -/
theorem crossing_zero_outer_unit_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (hzero : z.b=0 ∨ z.e=0)
    (hunit : |z.a|=1 ∨ |z.c|=1 ∨ |z.d|=1 ∨ |z.f|=1) :
    ∃ x y : ℤ,Reachable z (family x y) := by
  have transport (n : ℕ) (ha : |(CyclicMutation.cyclePower z n).a|=1) :
      ∃ x y : ℤ,Reachable z (family x y) := by
    let w := CyclicMutation.cyclePower z n
    change |w.a|=1 at ha
    have hr := CyclicMutation.reachable_cyclePower z n
    have hw := CyclicMutation.cyclePower_solution z hz n
    have hn := CyclicMutation.cyclePower_negative z hneg n
    have hcross := cycle_crossing_zero z n hzero
    have first_positive (v : Six) (hv : isSolution v)
        (hvn : IntrinsicSigns.thirdMinorSum v<0) (hva : v.a=1) (hvc : v.b=0 ∨ v.e=0) :
        ∃ x y : ℤ,Reachable v (family x y) := by
      rcases hvc with hb | he
      · exact positive_unit_zero_b_reachable_family v hv hvn hva hb
      · exact positive_unit_zero_e_reachable_family v hv hvn hva he
    have hsign : w.a=1 ∨ w.a= -1 := by
      have hab := abs_le.mp ha.le
      have hge := le_abs_self w.a
      have hne : w.a≠0 := by intro h; simp [w,h] at ha
      omega
    rcases hsign with hpos | hnegative
    · obtain ⟨x,y,hxy⟩ := first_positive w hw hn hpos hcross
      exact ⟨x,y,reachable_trans hr hxy⟩
    · have hr2 : Reachable w (eps2 w) := ⟨[.s2],rfl⟩
      have hu := reachable_preserves_solution hr2 hw
      have hun := reachable_negative hw hn hr2
      have hua : (eps2 w).a=1 := by simp [eps2,hnegative]
      have huc : (eps2 w).b=0 ∨ (eps2 w).e=0 := by simp [eps2]; tauto
      obtain ⟨x,y,hxy⟩ := first_positive (eps2 w) hu hun hua huc
      exact ⟨x,y,reachable_trans hr (reachable_trans hr2 hxy)⟩
  rcases hunit with ha | hc | hd | hf
  · exact transport 0 ha
  · exact transport 3 (by simpa using hc)
  · exact transport 1 (by simpa using hd)
  · exact transport 2 (by simpa using hf)

/-- Complete unconditional family-or-descent reduction at every zero edge,
including all positions and all arbitrary integer values of the other edges. -/
theorem zero_edge_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hzero : z.a=0 ∨ z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0) :
    NegativeTwoEdge.FamilyOrDrop z := by
  rcases ZeroCrossingBoundary.zero_family_or_crossing_unit z hz hneg hzero with h | ⟨hzero,hunit⟩
  · exact h
  · exact Or.inl (crossing_zero_outer_unit_reachable_family z hz hneg hzero hunit)

end SerreMarkov.ZeroUnitConic
