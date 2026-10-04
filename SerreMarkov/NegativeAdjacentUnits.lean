import SerreMarkov.NegativeUnitSmall
import SerreMarkov.DescentTransfer
import SerreMarkov.CyclicMutation
import SerreMarkov.MirrorDescent
import SerreMarkov.NegativeAdjacentReduction
import SerreMarkov.NegativeDiagonalAdjacentUnits

/-! # Genuine height reduction at two neighboring unit edges

The two intermediate moves are compared with the original height. Their
simultaneous failure is excluded by the solution equations, except for an
already classified affine triangle.
-/

namespace SerreMarkov.NegativeAdjacentUnits
open NegativeDescent NegativeTwoEdge NegativeUnitSmall NegativeTriangles

set_option maxHeartbeats 1000000

private theorem q2_cases (z : Six) (hz : isSolution z) : q2 z=4 ∨ q2 z=-4 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num
  exact hz.2

private theorem abs_sub_strong (e c : ℤ) (he : 0≤e)
    (h : |c|+2≤|e-c|) : 2≤e ∧ 2*c≤e-2 := by
  have ht : |e-c|≤|e|+|c| := by simpa using abs_sub_le e 0 c
  rw [abs_of_nonneg he] at ht
  have hl := le_abs_self c
  constructor
  · omega
  · by_cases hce : c≤e
    · rw [abs_of_nonneg (by omega : 0≤e-c)] at h
      omega
    · rw [abs_of_nonpos (by omega : e-c≤0),abs_of_nonneg (by omega : 0≤c)] at h
      omega

private theorem abs_sub_weak (e c : ℤ) (he : 0<e)
    (h : |c|≤|e-c|) : 2*c≤e := by
  have hl := le_abs_self c
  by_cases hce : c≤e
  · rw [abs_of_nonneg (by omega : 0≤e-c)] at h
    omega
  · rw [abs_of_nonpos (by omega : e-c≤0),abs_of_nonneg (by omega : 0≤c)] at h
    omega

private def lowerPolynomial (B e k : ℤ) : ℤ :=
  2*B^2*e^2+4*B^2+5*B*e^2-6*B*e*k+4*B+5*e^2-6*e*k+4*k^2-24

private theorem lowerPolynomial_shift_three (U T : ℤ) (hU : 0≤U) (hT : 0≤T) :
    0<lowerPolynomial (U+2) (T+3) 4 := by
  dsimp [lowerPolynomial]
  ring_nf
  positivity

private theorem lowerPolynomial_shift_small (U : ℤ) (hU : 0≤U) (e : ℤ)
    (he : e=0 ∨ e=1 ∨ e=2) : 0<lowerPolynomial (U+2) e 4 := by
  rcases he with rfl | rfl | rfl
  all_goals
    dsimp [lowerPolynomial]
    ring_nf
    positivity

private theorem lowerPolynomial_positive (B e k : ℤ)
    (hB : 2≤B) (he : 0≤e) (hk : k=4 ∨ k=-4) : 0<lowerPolynomial B e k := by
  rcases hk with rfl | rfl
  · by_cases he3 : 3≤e
    · have h := lowerPolynomial_shift_three (B-2) (e-3) (by omega) (by omega)
      simpa only [sub_add_cancel] using h
    · have h := lowerPolynomial_shift_small (B-2) (by omega) e (by omega)
      simpa only [sub_add_cancel] using h
  · dsimp [lowerPolynomial]
    have hB0 : 0≤B := by omega
    ring_nf
    positivity

private theorem negative_b_zero_e_impossible (B c f : ℤ)
    (hB : 2≤B) (hz : isSolution ⟨1,-B,c,1,0,f⟩) : False := by
  have hq := hz.1
  obtain hk | hk := q2_cases ⟨1,-B,c,1,0,f⟩ hz
  all_goals
    simp only [q2,one_mul,mul_zero,sub_zero,mul_one] at hk
    let T := -c*f-B-2
    have hcert : (B-1)*T=12 := by
      dsimp [T]
      dsimp [q1] at hq
      nlinarith [sq_nonneg (c+f)]
    have hT : 1≤T := by
      by_contra hn
      have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤B-1 by omega) (show T≤0 by omega)
      nlinarith
    have hT12 : T≤12 := by
      have hp := mul_nonneg (show 0≤B-2 by omega) (show 0≤T by omega)
      nlinarith
    have hB13 : B≤13 := by
      have hp := mul_nonneg (show 0≤B-1 by omega) (show 0≤T-1 by omega)
      nlinarith
    have hcf : -27≤c*f := by dsimp [T] at hT12; nlinarith
    have hcq : c^2-4*c≤27 ∨ c^2+4*c≤27 := by
      first | left; nlinarith [hk,hcf] | right; nlinarith [hk,hcf]
    have hc : -7≤c ∧ c≤7 := by
      constructor
      · by_contra hn
        have hp := mul_nonneg (show 0≤-(c+8) by omega) (show 0≤-(c-4) by omega)
        rcases hcq with h|h <;> nlinarith
      · by_contra hn
        have hp := mul_nonneg (show 0≤c-8 by omega) (show 0≤c+4 by omega)
        rcases hcq with h|h <;> nlinarith
    obtain ⟨hclo,hchi⟩ := hc
    have hf : f=4-c ∨ f=-4-c := by omega
    rcases hf with rfl | rfl
    all_goals
      interval_cases B <;> interval_cases c <;> norm_num [q1] at hq

/-- At a negative third coefficient, one of the two unit-triangle moves
is nonincreasing in the full six-coordinate height. -/
theorem negative_b_nonincrease (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hd : z.d=1) (hb : z.b≤-2) (he : 0≤z.e) :
    l1 (inv1 z)≤l1 z ∨ l1 (mu2 z)≤l1 z := by
  by_contra hn
  have hn1 : l1 z<l1 (inv1 z) := by omega
  have hn2 : l1 z<l1 (mu2 z) := by omega
  have h1 : |z.c|≤|z.e-z.c| := by
    have h := (l1_lt_iff (inv1 z) z).mp hn1
    dsimp [integerL1,inv1] at h
    simp only [ha,hd,mul_one,one_mul,abs_one,
      abs_of_nonneg (by omega : 0≤1-z.b),abs_of_nonpos (by omega : z.b≤0)] at h
    omega
  have h2 : |z.f|≤|z.e-z.f| := by
    have h := (l1_lt_iff (mu2 z) z).mp hn2
    dsimp [integerL1,mu2] at h
    simp only [ha,hd,mul_one,one_mul,abs_one,
      abs_of_nonneg (by omega : 0≤1-z.b),abs_of_nonpos (by omega : z.b≤0)] at h
    omega
  by_cases he0 : z.e=0
  · have ht : z=⟨1,-(-z.b),z.c,1,0,z.f⟩ := by ext <;> simp [ha,hd,he0]
    exact negative_b_zero_e_impossible (-z.b) z.c z.f (by omega) (ht ▸ hz)
  have hc := abs_sub_weak z.e z.c (by omega) h1
  have hf := abs_sub_weak z.e z.f (by omega) h2
  obtain ⟨k,hk,hq⟩ : ∃ k : ℤ,(k=4 ∨ k=-4) ∧ q2 z=k := by
    rcases q2_cases z hz with h|h
    · exact ⟨4,Or.inl rfl,h⟩
    · exact ⟨-4,Or.inr rfl,h⟩
  have hP := lowerPolynomial_positive (-z.b) z.e k (by omega) he hk
  have hprod : 0≤(-z.b-1)*(z.e-2*z.c)*(z.e-2*z.f) := by
    have hB : 0≤-z.b-1 := by omega
    have hC : 0≤z.e-2*z.c := by omega
    have hF : 0≤z.e-2*z.f := by omega
    positivity
  have hcert : 4*(q1 z-8)=lowerPolynomial (-z.b) z.e k+
      (-z.b-1)*(z.e-2*z.c)*(z.e-2*z.f)+
      2*(q2 z-k)*(z.b*z.e+2*z.c-3*z.e+2*z.f+2*k) := by
    dsimp [q1,q2,lowerPolynomial]
    rw [ha,hd]
    ring
  rw [hq,sub_self,mul_zero,zero_mul,add_zero] at hcert
  rw [hz.1] at hcert
  nlinarith

/-- A positive large third coefficient also forces a nonincreasing move. -/
theorem positive_b_nonincrease (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hd : z.d=1) (hb : 3≤z.b) (he : 0≤z.e) :
    l1 (inv1 z)≤l1 z ∨ l1 (mu2 z)≤l1 z := by
  by_contra hn
  have hn1 : l1 z<l1 (inv1 z) := by omega
  have hn2 : l1 z<l1 (mu2 z) := by omega
  have h1 : |z.c|+2≤|z.e-z.c| := by
    have h := (l1_lt_iff (inv1 z) z).mp hn1
    dsimp [integerL1,inv1] at h
    simp only [ha,hd,mul_one,one_mul,abs_one,
      abs_of_nonpos (by omega : 1-z.b≤0),abs_of_nonneg (by omega : 0≤z.b)] at h
    omega
  have h2 : |z.f|+2≤|z.e-z.f| := by
    have h := (l1_lt_iff (mu2 z) z).mp hn2
    dsimp [integerL1,mu2] at h
    simp only [ha,hd,mul_one,one_mul,abs_one,
      abs_of_nonpos (by omega : 1-z.b≤0),abs_of_nonneg (by omega : 0≤z.b)] at h
    omega
  obtain ⟨he2,hc⟩ := abs_sub_strong z.e z.c he h1
  have hf := (abs_sub_strong z.e z.f he h2).2
  have hq : z.c+z.f-z.b*z.e≥-4 := by
    rcases q2_cases z hz with h|h <;> simp only [q2,ha,hd,one_mul,mul_one] at h <;> omega
  have hp := mul_nonneg (show 0≤z.b-3 by omega) (show 0≤z.e by omega)
  nlinarith

private theorem normalized_adjacent_units (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (hd : z.d=1)
    (he : 0≤z.e) : FamilyOrDrop z := by
  have htri := (negative_triangle_inequalities z hz hneg).1
  have reduce_from_nonincrease
      (hn : l1 (inv1 z)≤l1 z ∨ l1 (mu2 z)≤l1 z) : FamilyOrDrop z := by
    rcases hn with hn | hn
    · have hr : Reachable z (inv1 z) := ⟨[.i1],rfl⟩
      apply DescentTransfer.family_or_drop_of_nonincrease hr hn
      exact NegativeDiagonalAdjacentUnits.signed_ab_unit_family_or_drop _
        (reachable_preserves_solution hr hz)
        (NegativeAdjacentReduction.reachable_negative hz hneg hr)
        (by simp [inv1,ha]) (by simp [inv1,hd])
    · have hr : Reachable z (mu2 z) := ⟨[.m2],rfl⟩
      apply DescentTransfer.family_or_drop_of_nonincrease hr hn
      exact NegativeDiagonalAdjacentUnits.diagonal_adjacent_units_family_or_drop _
        (reachable_preserves_solution hr hz)
        (NegativeAdjacentReduction.reachable_negative hz hneg hr)
        (Or.inl (by simp [mu2,ha])) (Or.inr (Or.inr (Or.inl (by simp [mu2,hd]))))
  by_cases hbpos : 3≤z.b
  · exact reduce_from_nonincrease (positive_b_nonincrease z hz ha hd hbpos he)
  by_cases hbneg : z.b≤-2
  · exact reduce_from_nonincrease (negative_b_nonincrease z hz ha hd hbneg he)
  have hb : z.b=-1 ∨ z.b=0 ∨ z.b=1 ∨ z.b=2 := by omega
  rcases hb with hb | hb | hb | hb
  · left
    apply first_two_unit_triangle_defect_four z hz
    · exact Or.inr (Or.inl ⟨by simp [ha],by simp [hd]⟩)
    · norm_num [cayleyDefect,ha,hd,hb]
  · norm_num [cayleyDefect,ha,hd,hb] at htri
  · norm_num [cayleyDefect,ha,hd,hb] at htri
  · left
    apply first_two_unit_triangle_defect_four z hz
    · exact Or.inr (Or.inl ⟨by simp [ha],by simp [hd]⟩)
    · norm_num [cayleyDefect,ha,hd,hb]

/-- Neighboring positive unit edges admit a genuine family reduction or
strict original-height descent, with no bounds on the other four edges. -/
theorem adjacent_units_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (hd : z.d=1) :
    FamilyOrDrop z := by
  by_cases he : 0≤z.e
  · exact normalized_adjacent_units z hz hneg ha hd he
  · have hr : Reachable z (eps4 z) := ⟨[.s4],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (l1_eps4 z)
    exact normalized_adjacent_units _ (reachable_preserves_solution hr hz)
      (NegativeAdjacentReduction.reachable_negative hz hneg hr)
      (by simpa [eps4] using ha) (by simpa [eps4] using hd) (by simp [eps4]; omega)

/-- Both neighboring unit edges may have either sign. The conclusion uses
an actual finite mutation word and its original full six-coordinate height. -/
theorem signed_adjacent_units_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : |z.a|=1) (hd : |z.d|=1) :
    FamilyOrDrop z := by
  have normalize_d (w : Six) (hw : isSolution w)
      (hwn : IntrinsicSigns.thirdMinorSum w<0) (hwa : w.a=1) (hwd : |w.d|=1) :
      FamilyOrDrop w := by
    rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hwd with hd | hd
    · exact adjacent_units_family_or_drop w hw hwn hwa hd
    · have hr : Reachable w (eps3 w) := ⟨[.s3],rfl⟩
      apply familyOrDrop_of_reachable_same_height hr (l1_eps3 w)
      exact adjacent_units_family_or_drop _ (reachable_preserves_solution hr hw)
        (NegativeAdjacentReduction.reachable_negative hw hwn hr)
        (by simpa [eps3] using hwa) (by simp [eps3,hd])
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp ha with ha | ha
  · exact normalize_d z hz hneg ha hd
  · have hr : Reachable z (eps2 z) := ⟨[.s2],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (l1_eps2 z)
    exact normalize_d _ (reachable_preserves_solution hr hz)
      (NegativeAdjacentReduction.reachable_negative hz hneg hr)
      (by simp [eps2,ha]) (by simpa [eps2] using hd)

/-- All four neighboring pairs in the adjacent-edge cycle are covered by
height-preserving actual cyclic mutation words. -/
theorem neighboring_unit_edges_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (hu : (|z.a|=1 ∧ |z.d|=1) ∨ (|z.d|=1 ∧ |z.f|=1) ∨
      (|z.f|=1 ∧ |z.c|=1) ∨ (|z.c|=1 ∧ |z.a|=1)) : FamilyOrDrop z := by
  have transfer (n : ℕ) (ha : |(CyclicMutation.cyclePower z n).a|=1)
      (hd : |(CyclicMutation.cyclePower z n).d|=1) : FamilyOrDrop z := by
    apply CyclicMutation.family_or_drop_transfer z n
    exact signed_adjacent_units_family_or_drop _
      (CyclicMutation.cyclePower_solution z hz n)
      (CyclicMutation.cyclePower_negative z hneg n) ha hd
  rcases hu with ⟨ha,hd⟩ | ⟨hd,hf⟩ | ⟨hf,hc⟩ | ⟨hc,ha⟩
  · exact signed_adjacent_units_family_or_drop z hz hneg ha hd
  · exact transfer 1 (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hd)
      (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
  · exact transfer 2 (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hf)
      (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
  · exact transfer 3 (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using hc)
      (by simpa [CyclicMutation.cyclePower,CyclicMutation.cycle] using ha)

end SerreMarkov.NegativeAdjacentUnits
