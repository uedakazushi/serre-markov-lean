import SerreMarkov.PositiveAdjacentThrees

/-! # Uniform negative triangle defects in the positive integral chamber

An actual three-root braid orbit has a point of minimum integral triangle
height. Its Vieta guards bound the defect by minus seven. The modular
obstruction excludes two edges equal to three, and actual braid transports
apply the same argument to all four principal triangles.
-/

namespace SerreMarkov.PositiveTriangleLower

open PositiveChamber PositiveAdjacentThrees
set_option maxHeartbeats 3000000

private theorem sorted_triangle_bound (u v w : ℤ)
    (hu : 3 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hprod : 2*w ≤ u*v) (hnot : ¬ (u=3 ∧ v=3)) : triangleDefect u v w ≤ -7 := by
  have hp : 0 ≤ (w-v)*(u*v-w-v) := mul_nonneg (by omega) (by omega)
  by_cases hu3 : u=3
  · have hv4 : 4 ≤ v := by omega
    have hv2 : 16 ≤ v^2 := by nlinarith only [hv4,sq_nonneg (v-4)]
    dsimp [triangleDefect]
    rw [hu3] at hp ⊢
    nlinarith only [hp,hv2]
  · have hu4 : 4 ≤ u := by omega
    have hu2 : 16 ≤ u^2 := by nlinarith only [hu4,sq_nonneg (u-4)]
    have hdiff : 0 ≤ v^2-u^2 := by
      have h := mul_nonneg (show 0 ≤ v-u by omega) (show 0 ≤ v+u by omega)
      nlinarith only [h]
    have hp2 : 0 ≤ (u-2)*(v^2-u^2) := mul_nonneg (by omega) hdiff
    have hp3 : 0 ≤ (u-4)*u^2 := mul_nonneg (by omega) (sq_nonneg _)
    dsimp [triangleDefect]
    nlinarith only [hp,hp2,hp3,hu2]

private theorem terminal_triangle_bound (a b d : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hd : 3 ≤ d)
    (hg1 : 2*d ≤ a*b) (hg2 : 2*b ≤ a*d) (hg3 : 2*a ≤ b*d)
    (hn1 : ¬ (a=3 ∧ b=3)) (hn2 : ¬ (a=3 ∧ d=3)) (hn3 : ¬ (b=3 ∧ d=3)) :
    triangleDefect a b d ≤ -7 := by
  rcases le_total a b with hab | hba
  · rcases le_total b d with hbd | hdb
    · exact sorted_triangle_bound a b d ha hab hbd hg1 hn1
    · rcases le_total a d with had | hda
      · have h := sorted_triangle_bound a d b ha had hdb hg2 hn2
        dsimp [triangleDefect] at h ⊢
        nlinarith only [h]
      · have h := sorted_triangle_bound d a b hd hda hab
          (by nlinarith only [hg2]) (by simpa only [and_comm] using hn2)
        dsimp [triangleDefect] at h ⊢
        nlinarith only [h]
  · rcases le_total a d with had | hda
    · have h := sorted_triangle_bound b a d hb hba had (by nlinarith only [hg1])
        (by simpa only [and_comm] using hn1)
      dsimp [triangleDefect] at h ⊢
      nlinarith only [h]
    · rcases le_total b d with hbd | hdb
      · have h := sorted_triangle_bound b d a hb hbd hda hg3 hn3
        dsimp [triangleDefect] at h ⊢
        nlinarith only [h]
      · have h := sorted_triangle_bound d b a hd hdb hba
          (by nlinarith only [hg3]) (by simpa only [and_comm] using hn3)
        dsimp [triangleDefect] at h ⊢
        nlinarith only [h]

private theorem chamber_no_abd_pair_threes (z : Six) (hz : Chamber z) :
    ¬ (z.a=3 ∧ z.b=3) ∧ ¬ (z.a=3 ∧ z.d=3) ∧ ¬ (z.b=3 ∧ z.d=3) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨ha,hb⟩
    exact chamber_no_adjacent_threes (mu1 z)
      (step_preserves_chamber .m1 True.intro z hz) ha hb
  · rintro ⟨ha,hd⟩
    exact chamber_no_adjacent_threes z hz ha hd
  · rintro ⟨hb,hd⟩
    exact chamber_no_adjacent_threes (inv2 z)
      (step_preserves_chamber .i2 True.intro z hz) hb hd

/-- The bound holds on every original triangle, with no no-drop hypothesis. -/
theorem chamber_abd_defect_bound (z : Six) (hz : Chamber z) :
    triangleDefect z.a z.b z.d ≤ -7 := by
  generalize hn : (z.a+z.b+z.d).toNat=n
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      have ha : 3 ≤ z.a := hz.2.2.1
      have hb : 3 ≤ z.b := hz.2.2.2.1
      have hd : 3 ≤ z.d := hz.2.2.2.2.2.1
      by_cases hg1 : 2*z.d ≤ z.a*z.b
      · by_cases hg2 : 2*z.b ≤ z.a*z.d
        · by_cases hg3 : 2*z.a ≤ z.b*z.d
          · obtain ⟨hn1,hn2,hn3⟩ := chamber_no_abd_pair_threes z hz
            exact terminal_triangle_bound _ _ _ ha hb hd hg1 hg2 hg3 hn1 hn2 hn3
          · have hw : Chamber (inv2 z) := step_preserves_chamber .i2 True.intro z hz
            have hwB : 3 ≤ (inv2 z).b := hw.2.2.2.1
            have hsize : ((inv2 z).a+(inv2 z).b+(inv2 z).d).toNat<n := by
              rw [←hn]
              simp only [inv2] at hwB ⊢
              omega
            have h := ih _ hsize (inv2 z) hw rfl
            have heq : triangleDefect (inv2 z).a (inv2 z).b (inv2 z).d =
                triangleDefect z.a z.b z.d := by dsimp [triangleDefect,inv2]; ring
            rwa [heq] at h
        · have hw : Chamber (inv1 z) := step_preserves_chamber .i1 True.intro z hz
          have hwD : 3 ≤ (inv1 z).d := hw.2.2.2.2.2.1
          have hsize : ((inv1 z).a+(inv1 z).b+(inv1 z).d).toNat<n := by
            rw [←hn]
            simp only [inv1] at hwD ⊢
            omega
          have h := ih _ hsize (inv1 z) hw rfl
          have heq : triangleDefect (inv1 z).a (inv1 z).b (inv1 z).d =
              triangleDefect z.a z.b z.d := by dsimp [triangleDefect,inv1]; ring
          rwa [heq] at h
      · have hw : Chamber (mu1 z) := step_preserves_chamber .m1 True.intro z hz
        have hwB : 3 ≤ (mu1 z).b := hw.2.2.2.1
        have hsize : ((mu1 z).a+(mu1 z).b+(mu1 z).d).toNat<n := by
          rw [←hn]
          simp only [mu1] at hwB ⊢
          omega
        have h := ih _ hsize (mu1 z) hw rfl
        have heq : triangleDefect (mu1 z).a (mu1 z).b (mu1 z).d =
            triangleDefect z.a z.b z.d := by dsimp [triangleDefect,mu1]; ring
        rwa [heq] at h

theorem chamber_ace_defect_bound (z : Six) (hz : Chamber z) :
    triangleDefect z.a z.c z.e ≤ -7 :=
  chamber_abd_defect_bound (inv3 z) (step_preserves_chamber .i3 True.intro z hz)

theorem chamber_bcf_defect_bound (z : Six) (hz : Chamber z) :
    triangleDefect z.b z.c z.f ≤ -7 :=
  chamber_abd_defect_bound (inv3 (inv2 z))
    (step_preserves_chamber .i3 True.intro (inv2 z)
      (step_preserves_chamber .i2 True.intro z hz))

theorem chamber_def_defect_bound (z : Six) (hz : Chamber z) :
    triangleDefect z.d z.e z.f ≤ -7 :=
  chamber_abd_defect_bound (inv3 (inv2 (inv1 z)))
    (step_preserves_chamber .i3 True.intro (inv2 (inv1 z))
      (step_preserves_chamber .i2 True.intro (inv1 z)
        (step_preserves_chamber .i1 True.intro z hz)))

theorem chamber_all_triangle_bounds (z : Six) (hz : Chamber z) :
    triangleDefect z.a z.b z.d ≤ -7 ∧ triangleDefect z.a z.c z.e ≤ -7 ∧
      triangleDefect z.b z.c z.f ≤ -7 ∧ triangleDefect z.d z.e z.f ≤ -7 :=
  ⟨chamber_abd_defect_bound z hz,chamber_ace_defect_bound z hz,
    chamber_bcf_defect_bound z hz,chamber_def_defect_bound z hz⟩

end SerreMarkov.PositiveTriangleLower
