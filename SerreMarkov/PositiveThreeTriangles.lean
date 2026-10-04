import SerreMarkov.PositiveAdjacentThrees

/-! # Strong integer triangle bounds when one adjacent pairing is three

The mod-twenty-seven obstruction propagates along actual braid words. Every
edge incident to a pairing three is at least four. Well-founded Vieta descent
on either affected edge pair then makes its triangle defect at most minus
seven. No short-word no-drop hypothesis or global orbit classification is used.
-/

namespace SerreMarkov.PositiveThreeTriangles

open PositiveChamber PositiveAdjacentThrees
set_option maxHeartbeats 2000000

theorem a_three_incident_bounds (z : Six) (hz : Chamber z) (ha : z.a=3) :
    4 ≤ z.b ∧ 4 ≤ z.c ∧ 4 ≤ z.d ∧ 4 ≤ z.e := by
  have hb : 3 ≤ z.b := hz.2.2.2.1
  have hc : 3 ≤ z.c := hz.2.2.2.2.1
  have hd : 3 ≤ z.d := hz.2.2.2.2.2.1
  have he : 3 ≤ z.e := hz.2.2.2.2.2.2.1
  have hnb : z.b ≠ 3 := by
    intro hb3
    have hw := step_preserves_chamber .m1 True.intro z hz
    exact chamber_no_adjacent_threes (mu1 z) hw ha hb3
  have hnc : z.c ≠ 3 := by
    intro hc3
    have hw1 := step_preserves_chamber .i3 True.intro z hz
    have hw2 := step_preserves_chamber .m1 True.intro (inv3 z) hw1
    exact chamber_no_adjacent_threes (mu1 (inv3 z)) hw2 ha hc3
  have hnd : z.d ≠ 3 := fun hd3 => chamber_no_adjacent_threes z hz ha hd3
  have hne : z.e ≠ 3 := by
    intro he3
    have hw1 := step_preserves_chamber .i1 True.intro z hz
    have hw2 := step_preserves_chamber .i3 True.intro (inv1 z) hw1
    have hw3 := step_preserves_chamber .m1 True.intro (inv3 (inv1 z)) hw2
    exact chamber_no_adjacent_threes (mu1 (inv3 (inv1 z))) hw3 ha he3
  omega

private theorem balanced_pair_bound (u v : ℤ) (hu : 4 ≤ u) (hv : 4 ≤ v)
    (hbal1 : 2*v ≤ 3*u) (hbal2 : 2*u ≤ 3*v) : triangleDefect 3 u v ≤ -7 := by
  dsimp [triangleDefect]
  rcases le_total u v with huv | hvu
  · have hp : 0 ≤ (v-u)*(2*u-v) := mul_nonneg (by omega) (by omega)
    have hu2 : 16 ≤ u^2 := by nlinarith only [hu,sq_nonneg (u-4)]
    nlinarith only [hp,hu2]
  · have hp : 0 ≤ (u-v)*(2*v-u) := mul_nonneg (by omega) (by omega)
    have hv2 : 16 ≤ v^2 := by nlinarith only [hv,sq_nonneg (v-4)]
    nlinarith only [hp,hv2]

private theorem invariant_pair_bound (P Q : Six → ℤ)
    (hMu : ∀ z : Six, z.a=3 → P (mu1 z)=3*P z-Q z ∧ Q (mu1 z)=P z)
    (hInv : ∀ z : Six, z.a=3 → P (inv1 z)=Q z ∧ Q (inv1 z)=3*Q z-P z)
    (hLower : ∀ z : Six, Chamber z → z.a=3 → 4 ≤ P z ∧ 4 ≤ Q z)
    (z : Six) (hz : Chamber z) (ha : z.a=3) : triangleDefect 3 (P z) (Q z) ≤ -7 := by
  generalize hn : (P z+Q z).toNat=n
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      obtain ⟨hP,hQ⟩ := hLower z hz ha
      by_cases hbal1 : 2*Q z ≤ 3*P z
      · by_cases hbal2 : 2*P z ≤ 3*Q z
        · exact balanced_pair_bound _ _ hP hQ hbal1 hbal2
        · have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
          have haw : (inv1 z).a=3 := ha
          obtain ⟨hPw,hQw⟩ := hInv z ha
          obtain ⟨hPL,hQL⟩ := hLower (inv1 z) hw haw
          have hsize : (P (inv1 z)+Q (inv1 z)).toNat<n := by
            rw [hPw,hQw,←hn]
            omega
          have h := ih _ hsize (inv1 z) hw haw rfl
          have heq : triangleDefect 3 (P (inv1 z)) (Q (inv1 z)) = triangleDefect 3 (P z) (Q z) := by
            rw [hPw,hQw]
            dsimp [triangleDefect]
            ring
          rwa [heq] at h
      · have hw : Chamber (mu1 z) := step_preserves_chamber .m1 True.intro z hz
        have haw : (mu1 z).a=3 := ha
        obtain ⟨hPw,hQw⟩ := hMu z ha
        obtain ⟨hPL,hQL⟩ := hLower (mu1 z) hw haw
        have hsize : (P (mu1 z)+Q (mu1 z)).toNat<n := by
          rw [hPw,hQw,←hn]
          omega
        have h := ih _ hsize (mu1 z) hw haw rfl
        have heq : triangleDefect 3 (P (mu1 z)) (Q (mu1 z)) = triangleDefect 3 (P z) (Q z) := by
          rw [hPw,hQw]
          dsimp [triangleDefect]
          ring
        rwa [heq] at h

theorem a_three_abd_triangle_bound (z : Six) (hz : Chamber z) (ha : z.a=3) :
    triangleDefect z.a z.b z.d ≤ -7 := by
  rw [ha]
  apply invariant_pair_bound (fun w => w.b) (fun w => w.d) ?_ ?_ ?_ z hz ha
  · intro w hw
    simp only [mu1,hw,and_self]
  · intro w hw
    simp only [inv1,hw,and_self]
  · intro w hw hwa
    have h := a_three_incident_bounds w hw hwa
    exact ⟨h.1,h.2.2.1⟩

theorem a_three_ace_triangle_bound (z : Six) (hz : Chamber z) (ha : z.a=3) :
    triangleDefect z.a z.c z.e ≤ -7 := by
  rw [ha]
  apply invariant_pair_bound (fun w => w.c) (fun w => w.e) ?_ ?_ ?_ z hz ha
  · intro w hw
    simp only [mu1,hw,and_self]
  · intro w hw
    simp only [inv1,hw,and_self]
  · intro w hw hwa
    have h := a_three_incident_bounds w hw hwa
    exact ⟨h.2.1,h.2.2.2⟩

end SerreMarkov.PositiveThreeTriangles
