import SerreMarkov.ZeroSingleEdgeDescent

/-! # General descent at an orthogonal adjacent pair
The other four incident edges may have any nonzero integral size; only the
opposite edge has absolute value at least three. No global descent or
classification hypothesis is used.
-/
namespace SerreMarkov.ZeroIncidentBoundary
open NegativeDescent NegativeTriangles ZeroSingleEdgeDescent
set_option linter.unusedSimpArgs false

private theorem positive_triangle_descent_or_affine (u v w : ℤ)
    (hu : 1≤u) (hv : 1≤v) (hw : 3≤w) (hmax : u≤w ∧ v≤w)
    (hc : 4≤cayleyDefect u v w) :
    |u*v-w|<w ∨ (u=2 ∧ v=w) ∨ (v=2 ∧ u=w) := by
  have sorted (u v : ℤ) (hu : 1≤u) (hv : 1≤v) (huv : u≤v)
      (hvw : v≤w) (hc : 4≤cayleyDefect u v w) :
      |u*v-w|<w ∨ (u=2 ∧ v=w) := by
    by_cases hu3 : 3≤u
    · exact Or.inl (cayley_sorted_abs_descent u v w hu3 huv hvw hc)
    · have hu12 : u=1 ∨ u=2 := by omega
      rcases hu12 with rfl | rfl
      · left
        simp only [one_mul]
        exact abs_lt.mpr ⟨by omega,by omega⟩
      · by_cases heq : v=w
        · exact Or.inr ⟨rfl,heq⟩
        · left
          exact abs_lt.mpr ⟨by omega,by omega⟩
  rcases le_total u v with huv | hvu
  · rcases sorted u v hu hv huv hmax.2 hc with hd | he
    · exact Or.inl hd
    · exact Or.inr (Or.inl he)
  · rcases sorted v u hv hu hvu hmax.1
      (by simpa [cayleyDefect,mul_comm,add_comm] using hc) with hd | he
    · exact Or.inl (by simpa [mul_comm] using hd)
    · exact Or.inr (Or.inr he)

private theorem orthogonal_no_affine_plateau (z : Six) (hz : isSolution z)
    (ha : z.a=0) (hb : 1≤z.b) (hc : 1≤z.c) (hd : 1≤z.d)
    (he : 1≤z.e) (hf : 3≤z.f) :
    ¬(z.d=2 ∧ z.e=z.f) ∧ ¬(z.e=2 ∧ z.d=z.f) ∧
    ¬(z.b=2 ∧ z.c=z.f) ∧ ¬(z.c=2 ∧ z.b=z.f) := by
  have hq := hz.1
  have hp := hz.2
  simp only [q1,q2,ha,zero_mul,mul_zero,add_zero,sub_zero,
    zero_pow (by decide : 2≠0)] at hq hp
  have hf2 : 0<z.f^2-4 := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨hd2,hef⟩
    rw [hd2,hef] at hq hp
    have hprod := mul_pos (by nlinarith : 0<z.b^2) hf2
    nlinarith only [hq,hp,hprod]
  · rintro ⟨he2,hdf⟩
    rw [he2,hdf] at hq hp
    have hprod := mul_pos (by nlinarith : 0<z.c^2) hf2
    nlinarith only [hq,hp,hprod]
  · rintro ⟨hb2,hcf⟩
    rw [hb2,hcf] at hq hp
    have hprod := mul_pos (by nlinarith : 0<z.d^2) hf2
    nlinarith only [hq,hp,hprod]
  · rintro ⟨hc2,hbf⟩
    rw [hc2,hbf] at hq hp
    have hprod := mul_pos (by nlinarith : 0<z.e^2) hf2
    nlinarith only [hq,hp,hprod]

/-- If an incident edge is above the opposite edge, determinant four rules
out reversing the order of the two positive incident pairs. -/
private theorem determinant_direction_above_three (b c d e f : ℤ)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (he : 1≤e) (hf : 3≤f)
    (hdet : -4≤c*d-b*e ∧ c*d-b*e≤4) :
    (f<c → b<c → d≤e) ∧ (f<b → c<b → e≤d) := by
  constructor
  · intro hfc hbc
    by_contra h
    have hde : e<d := by omega
    have h1 := mul_nonneg (by omega : 0≤d-e-1) (by omega : 0≤c)
    have h2 := mul_nonneg (by omega : 0≤c-b-1) (by omega : 0≤e)
    nlinarith only [hdet.2,h1,h2,hfc,hf,he]
  · intro hfb hcb
    by_contra h
    have hed : d<e := by omega
    have h1 := mul_nonneg (by omega : 0≤e-d-1) (by omega : 0≤b)
    have h2 := mul_nonneg (by omega : 0≤b-c-1) (by omega : 0≤d)
    nlinarith only [hdet.1,h1,h2,hfb,hf,hd]

/-- All positive nonzero incident edges at an adjacent zero pair admit
strict two-move descent as soon as the opposite edge is at least three. -/
theorem zero_positive_incident_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0)
    (hb : 1≤z.b) (hc : 1≤z.c) (hd : 1≤z.d) (he : 1≤z.e) (hf : 3≤z.f) :
    ∃ word : List Generator, word∈orthogonalWords ∧ l1 (applyWord z word)<l1 z := by
  obtain ⟨_,_,hbc,hde⟩ := negative_triangle_inequalities z hz hneg
  have hsq := hz.2
  simp [q2,ha] at hsq
  have hdet : -4≤z.c*z.d-z.b*z.e ∧ z.c*z.d-z.b*z.e≤4 := by
    constructor <;> nlinarith [hsq]
  obtain ⟨hnoDE,hnoED,hnoBC,hnoCB⟩ := orthogonal_no_affine_plateau z hz ha hb hc hd he hf
  have hdir := determinant_direction_above_three z.b z.c z.d z.e z.f hb hc hd he hf hdet
  by_cases hmaxde : z.d≤z.f ∧ z.e≤z.f
  · have hdrop : |z.d*z.e-z.f|<z.f := by
      rcases positive_triangle_descent_or_affine z.d z.e z.f hd he hf hmaxde hde with h | h | h
      · exact h
      · exact False.elim (hnoDE h)
      · exact False.elim (hnoED h)
    refine ⟨[.m2],by decide,?_⟩
    change l1 (mu2 z)<l1 z
    rw [mu2_drop_iff]
    simp only [ha,zero_mul,zero_sub,abs_neg]
    rw [abs_of_nonneg (by omega : 0≤z.f)]
    omega
  by_cases hmaxbc : z.b≤z.f ∧ z.c≤z.f
  · have hdrop : |z.b*z.c-z.f|<z.f := by
      rcases positive_triangle_descent_or_affine z.b z.c z.f hb hc hf hmaxbc hbc with h | h | h
      · exact h
      · exact False.elim (hnoBC h)
      · exact False.elim (hnoCB h)
    refine ⟨[.m1,.m2],by decide,?_⟩
    change l1 (mu2 (mu1 z))<l1 z
    rw [l1_lt_iff]
    simp [integerL1,mu2,mu1,ha]
    rw [abs_of_nonneg (by omega : 0≤z.f)]
    omega
  by_cases horder : z.b≤z.c
  · have hfc : z.f<z.c := by omega
    have hdropc : |z.f*z.b-z.c|<z.c := by
      rcases positive_triangle_descent_or_affine z.f z.b z.c (by omega) hb (by omega)
        ⟨by omega,horder⟩
        (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hbc)
        with h | h | h
      · exact h
      · omega
      · omega
    have hstrict : z.b<z.c := by
      by_contra h
      have heq : z.b=z.c := by omega
      have hprod := (abs_lt.mp hdropc).2
      have hmult := mul_nonneg (by omega : 0≤z.f-3) (by omega : 0≤z.b)
      nlinarith [hmult]
    have hdeord := hdir.1 hfc hstrict
    have hfe : z.f<z.e := by omega
    have hdrop : |z.f*z.d-z.e|<z.e := by
      rcases positive_triangle_descent_or_affine z.f z.d z.e (by omega) hd (by omega)
        ⟨by omega,hdeord⟩
        (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hde)
        with h | h | h
      · exact h
      · omega
      · omega
    refine ⟨[.m3],by decide,?_⟩
    change l1 (mu3 z)<l1 z
    rw [mu3_drop_iff,abs_of_nonneg (by omega : 0≤z.c),abs_of_nonneg (by omega : 0≤z.e)]
    omega
  · have hcb : z.c<z.b := by omega
    have hfb : z.f<z.b := by omega
    have hdropb : |z.f*z.c-z.b|<z.b := by
      rcases positive_triangle_descent_or_affine z.f z.c z.b (by omega) hc (by omega)
        ⟨by omega,by omega⟩
        (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hbc)
        with h | h | h
      · exact h
      · omega
      · omega
    have hedord := hdir.2 hfb hcb
    have hfd : z.f<z.d := by omega
    have hdrop : |z.f*z.e-z.d|<z.d := by
      rcases positive_triangle_descent_or_affine z.f z.e z.d (by omega) he (by omega)
        ⟨by omega,hedord⟩
        (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hde)
        with h | h | h
      · exact h
      · omega
      · omega
    refine ⟨[.i3],by decide,?_⟩
    change l1 (inv3 z)<l1 z
    rw [inv3_drop_iff,abs_of_nonneg (by omega : 0≤z.b),abs_of_nonneg (by omega : 0≤z.d)]
    omega


private theorem mixed_orthogonal_no_large_f (b c d E f : ℤ)
    (hb : 1≤b) (hc : 1≤c) (hd : 1≤d) (hE : 1≤E) (hf : 3≤|f|)
    (hdet : c*d+b*E=4)
    (hq : b^2+c^2+d^2+E^2+f^2-f*(b*c-d*E)=8) : False := by
  have hCD : 1≤c*d := by nlinarith [mul_nonneg (by omega : 0≤c-1) (by omega : 0≤d-1)]
  have hBE : 1≤b*E := by nlinarith [mul_nonneg (by omega : 0≤b-1) (by omega : 0≤E-1)]
  have hb3 : b≤3 := by
    nlinarith [mul_nonneg (by omega : 0≤b) (by omega : 0≤E-1)]
  have hc3 : c≤3 := by
    nlinarith [mul_nonneg (by omega : 0≤c) (by omega : 0≤d-1)]
  have hd3 : d≤3 := by
    nlinarith [mul_nonneg (by omega : 0≤d) (by omega : 0≤c-1)]
  have hE3 : E≤3 := by
    nlinarith [mul_nonneg (by omega : 0≤E) (by omega : 0≤b-1)]
  have hf9 : 9≤f^2 := by nlinarith [sq_abs f,sq_nonneg (|f|-3)]
  interval_cases b <;> interval_cases c <;> interval_cases d <;> interval_cases E
  all_goals norm_num at *
  all_goals nlinarith [sq_nonneg (f-2),sq_nonneg (f+2)]

private theorem zero_incident_same_sign (z : Six) (hz : isSolution z) (ha : z.a=0)
    (hb : 1≤z.b) (hc : 1≤z.c) (hd : 1≤|z.d|) (he : 1≤|z.e|) (hf : 3≤|z.f|) :
    (1≤z.d ∧ 1≤z.e) ∨ (z.d≤-1 ∧ z.e≤-1) := by
  have hdne : z.d≠0 := by intro h; simp [h] at hd
  have hene : z.e≠0 := by intro h; simp [h] at he
  have hq := hz.1
  have hp := hz.2
  simp only [q1,q2,ha,zero_mul,mul_zero,add_zero,sub_zero,
    zero_pow (by decide : 2≠0)] at hq hp
  rcases lt_or_gt_of_ne hdne with hdneg | hdpos <;>
    rcases lt_or_gt_of_ne hene with heneg | hepos
  · exact Or.inr ⟨by omega,by omega⟩
  · exfalso
    have hdet : z.c*(-z.d)+z.b*z.e=4 := by
      have hprod1 := mul_pos (by omega : 0<z.c) (by omega : 0< -z.d)
      have hprod2 := mul_pos (by omega : 0<z.b) hepos
      nlinarith only [hp,hprod1,hprod2]
    exact mixed_orthogonal_no_large_f z.b z.c (-z.d) z.e z.f hb hc (by omega)
      (by omega) hf hdet (by nlinarith only [hq])
  · exfalso
    have hdet : z.c*z.d+z.b*(-z.e)=4 := by
      have hprod1 := mul_pos (by omega : 0<z.c) hdpos
      have hprod2 := mul_pos (by omega : 0<z.b) (by omega : 0< -z.e)
      nlinarith only [hp,hprod1,hprod2]
    exact mixed_orthogonal_no_large_f z.b z.c z.d (-z.e) z.f hb hc (by omega)
      (by omega) hf hdet (by nlinarith only [hq])
  · exact Or.inl ⟨by omega,by omega⟩

private theorem zero_incident_positive_f (z : Six) (hz : isSolution z) (ha : z.a=0)
    (hb : 1≤z.b) (hc : 1≤z.c) (hd : 1≤z.d) (he : 1≤z.e) (hf : 3≤|z.f|) :
    0<z.f := by
  have hq := hz.1
  simp only [q1,ha,zero_mul,mul_zero,add_zero,sub_zero,
    zero_pow (by decide : 2≠0)] at hq
  have hf9 : 9≤z.f^2 := by nlinarith [sq_abs z.f,sq_nonneg (|z.f|-3)]
  have hB : 1≤z.b*z.c := by nlinarith [mul_nonneg (by omega : 0≤z.b-1) (by omega : 0≤z.c-1)]
  have hD : 1≤z.d*z.e := by nlinarith [mul_nonneg (by omega : 0≤z.d-1) (by omega : 0≤z.e-1)]
  by_contra h
  have hf0 : z.f≤0 := by omega
  have hprodB := mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤z.b*z.c) hf0
  have hprodD := mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤z.d*z.e) hf0
  nlinarith [sq_nonneg z.b,sq_nonneg z.c,sq_nonneg z.d,sq_nonneg z.e]

/-- Every adjacent zero solution with nonzero incident edges and an opposite
edge of absolute value at least three has strict descent in two braid moves. -/
theorem zero_nonzero_incident_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0)
    (hb : z.b≠0) (hc : z.c≠0) (hd : z.d≠0) (he : z.e≠0) (hf : 3≤|z.f|) :
    ∃ word : List Generator, word∈orthogonalWords ∧ l1 (applyWord z word)<l1 z := by
  have hb1 : 1≤|z.b| := by have h := abs_pos.mpr hb; omega
  have hc1 : 1≤|z.c| := by have h := abs_pos.mpr hc; omega
  have hd1 : 1≤|z.d| := by have h := abs_pos.mpr hd; omega
  have he1 : 1≤|z.e| := by have h := abs_pos.mpr he; omega
  obtain ⟨s,hs,hwa,hwb,hwc,hr,_⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  let w := PositiveNormalization.signedSix z s
  have hw := reachable_preserves_solution hr hz
  have hn : IntrinsicSigns.thirdMinorSum w<0 := by
    have hk := (intrinsicKind_negative_iff z hz).mpr hneg
    rw [reachable_intrinsicKind hz hr] at hk
    exact (intrinsicKind_negative_iff w hw).mp hk
  have hwa' : w.a=0 := by simpa [ha] using hwa
  have hwb' : 1≤w.b := by dsimp [w]; rw [hwb]; exact hb1
  have hwc' : 1≤w.c := by dsimp [w]; rw [hwc]; exact hc1
  obtain ⟨_,_,_,hwd,hwe,hwf⟩ := SignGaugeDescent.signedSix_abs z s hs
  have hwd' : 1≤|w.d| := by dsimp [w]; rw [hwd]; exact hd1
  have hwe' : 1≤|w.e| := by dsimp [w]; rw [hwe]; exact he1
  have hwf' : 3≤|w.f| := by dsimp [w]; rw [hwf]; exact hf
  apply SignGaugeDescent.restricted_descent_transfer z s hs (fun word => word∈orthogonalWords)
  change ∃ word,word∈orthogonalWords ∧ l1 (applyWord w word)<l1 w
  obtain ⟨hwdpos,hwepos⟩ | ⟨hwdneg,hweneg⟩ := zero_incident_same_sign w hw hwa' hwb' hwc' hwd' hwe' hwf'
  · have hfpos := zero_incident_positive_f w hw hwa' hwb' hwc' hwdpos hwepos hwf'
    rw [abs_of_pos hfpos] at hwf'
    exact zero_positive_incident_descent w hw hn hwa' hwb' hwc' hwdpos hwepos hwf'
  · have hr2 : Reachable w (eps2 w) := ⟨[.s2],rfl⟩
    have hu := reachable_preserves_solution hr2 hw
    have hun : IntrinsicSigns.thirdMinorSum (eps2 w)<0 := by
      have hk := (intrinsicKind_negative_iff w hw).mpr hn
      rw [reachable_intrinsicKind hw hr2] at hk
      exact (intrinsicKind_negative_iff (eps2 w) hu).mp hk
    have hua : (eps2 w).a=0 := by simp [eps2,hwa']
    have hub : 1≤(eps2 w).b := by simpa [eps2] using hwb'
    have huc : 1≤(eps2 w).c := by simpa [eps2] using hwc'
    have hud : 1≤(eps2 w).d := by simp [eps2]; omega
    have hue : 1≤(eps2 w).e := by simp [eps2]; omega
    have hufpos := zero_incident_positive_f (eps2 w) hu hua hub huc hud hue
      (by simpa [eps2] using hwf')
    have huf : 3≤(eps2 w).f := by
      have hab : 3≤|(eps2 w).f| := by simpa [eps2] using hwf'
      rwa [abs_of_pos hufpos] at hab
    have hdesc := zero_positive_incident_descent (eps2 w) hu hun hua hub huc hud hue huf
    let t : Fin 4 → ℤ := ![1,-1,1,1]
    have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> norm_num [t]
    have htw : PositiveNormalization.signedSix w t=eps2 w := by
      ext <;> simp [PositiveNormalization.signedSix,eps2,t]
    apply SignGaugeDescent.restricted_descent_transfer w t ht (fun word => word∈orthogonalWords)
    simpa only [htw] using hdesc

/-- General adjacent-zero boundary reduction for a large opposite edge:
a second zero reaches the family; otherwise a two-move word strictly decreases L1. -/
theorem zero_large_opposite_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=0) (hf : 3≤|z.f|) :
    (∃ x y : ℤ,Reachable z (family x y)) ∨
      (∃ word : List Generator,word∈braidWords 2 ∧ l1 (applyWord z word)<l1 z) := by
  by_cases hzero : z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0
  · left
    apply NegativeBoundary.two_zero_edges_reachable_family z hz hneg
    exact Or.inl ⟨ha,by tauto⟩
  · right
    have hb : z.b≠0 := by tauto
    have hc : z.c≠0 := by tauto
    have hd : z.d≠0 := by tauto
    have he : z.e≠0 := by tauto
    obtain ⟨word,hw,hdrop⟩ := zero_nonzero_incident_descent z hz hneg ha hb hc hd he hf
    refine ⟨word,?_,hdrop⟩
    simp [orthogonalWords] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> decide

end SerreMarkov.ZeroIncidentBoundary
