import SerreMarkov.NegativeDescent
import SerreMarkov.NegativeTriangles
import SerreMarkov.Dihedral
import SerreMarkov.SignGaugeDescent

/-! # Unconditional small-edge reductions on the negative locus

These reductions use only the integer solution equations and the proved
negative principal-minor inequalities. No local or global descent hypothesis
is assumed.
-/

namespace SerreMarkov.NegativeBoundary

open NegativeDescent NegativeTriangles

private theorem determinant_direction (b c d e : ℤ)
    (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e)
    (hdet : -4 ≤ c*d-b*e ∧ c*d-b*e ≤ 4) :
    ¬(b<c ∧ e<d) ∧ ¬(c<b ∧ d<e) := by
  constructor
  · rintro ⟨hbc,hed⟩
    have h1 := mul_nonneg (by omega : 0 ≤ c-b-1) (by omega : 0 ≤ d)
    have h2 := mul_nonneg (by omega : 0 ≤ b) (by omega : 0 ≤ d-e-1)
    nlinarith [hdet.2,h1,h2]
  · rintro ⟨hcb,hde⟩
    have h1 := mul_nonneg (by omega : 0 ≤ b-c-1) (by omega : 0 ≤ e)
    have h2 := mul_nonneg (by omega : 0 ≤ c) (by omega : 0 ≤ e-d-1)
    nlinarith [hdet.1,h1,h2]

/-- A positive orthogonal-pair presentation with all other edges at least
three has a strict braid descent of length at most two. -/
theorem zero_large_positive_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0)
    (hb : 3 ≤ z.b) (hc : 3 ≤ z.c) (hd : 3 ≤ z.d) (he : 3 ≤ z.e) (hf : 3 ≤ z.f) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word) < l1 z := by
  obtain ⟨_,_,hbc,hde⟩ := negative_triangle_inequalities z hz hneg
  have hsq := hz.2
  simp [q2,ha] at hsq
  have hdet : -4 ≤ z.c*z.d-z.b*z.e ∧ z.c*z.d-z.b*z.e ≤ 4 := by
    constructor <;> nlinarith [hsq]
  have hdir := determinant_direction z.b z.c z.d z.e hb hc hd he hdet
  by_cases hmaxde : z.d ≤ z.f ∧ z.e ≤ z.f
  · have hdrop := cayley_positive_abs_descent z.d z.e z.f hd he hf hmaxde hde
    refine ⟨[.m2],by decide,?_⟩
    change l1 (mu2 z) < l1 z
    rw [mu2_drop_iff]
    simp only [ha,zero_mul,zero_sub,abs_neg]
    rw [abs_of_nonneg (by omega : 0 ≤ z.f)]
    omega
  by_cases hmaxbc : z.b ≤ z.f ∧ z.c ≤ z.f
  · have hdrop := cayley_positive_abs_descent z.b z.c z.f hb hc hf hmaxbc hbc
    refine ⟨[.m1,.m2],by decide,?_⟩
    change l1 (mu2 (mu1 z)) < l1 z
    rw [l1_lt_iff]
    simp [integerL1,mu2,mu1,ha]
    rw [abs_of_nonneg (by omega : 0 ≤ z.f)]
    omega
  by_cases horder : z.b ≤ z.c
  · have hfc : z.f ≤ z.c := by omega
    have hdropc := cayley_positive_abs_descent z.f z.b z.c hf hb hc ⟨hfc,horder⟩
      (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hbc)
    have hstrict : z.b < z.c := by
      by_contra h
      have heq : z.b=z.c := by omega
      have hprod := (abs_lt.mp hdropc).2
      have hmult := mul_nonneg (by omega : 0 ≤ z.f-3) (by omega : 0 ≤ z.b)
      nlinarith [hmult]
    have hdeord : z.d ≤ z.e := by
      by_contra h
      exact hdir.1 ⟨hstrict,by omega⟩
    have hfe : z.f ≤ z.e := by omega
    have hdrop := cayley_positive_abs_descent z.f z.d z.e hf hd he ⟨hfe,hdeord⟩
      (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hde)
    refine ⟨[.m3],by decide,?_⟩
    change l1 (mu3 z) < l1 z
    rw [mu3_drop_iff,abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonneg (by omega : 0 ≤ z.e)]
    omega
  · have hcb : z.c ≤ z.b := by omega
    have hfb : z.f ≤ z.b := by omega
    have hdropb := cayley_positive_abs_descent z.f z.c z.b hf hc hb ⟨hfb,hcb⟩
      (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hbc)
    have hedord : z.e ≤ z.d := by
      by_contra h
      exact hdir.2 ⟨by omega,by omega⟩
    have hfd : z.f ≤ z.d := by omega
    have hdrop := cayley_positive_abs_descent z.f z.e z.d hf he hd ⟨hfd,hedord⟩
      (by simpa [cayleyDefect,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hde)
    refine ⟨[.i3],by decide,?_⟩
    change l1 (inv3 z) < l1 z
    rw [inv3_drop_iff,abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonneg (by omega : 0 ≤ z.d)]
    omega

private theorem zero_positive_f (z : Six) (hz : isSolution z) (ha : z.a=0)
    (hb : 3 ≤ z.b) (hc : 3 ≤ z.c) (hd : 3 ≤ z.d) (he : 3 ≤ z.e) : 0 < z.f := by
  by_contra hf
  have hf' : z.f ≤ 0 := by omega
  have h1 := hz.1
  simp [q1,ha] at h1
  have hb2 : 9 ≤ z.b^2 := by nlinarith [sq_nonneg (z.b-3)]
  have hc2 : 9 ≤ z.c^2 := by nlinarith [sq_nonneg (z.c-3)]
  have hd2 : 9 ≤ z.d^2 := by nlinarith [sq_nonneg (z.d-3)]
  have he2 : 9 ≤ z.e^2 := by nlinarith [sq_nonneg (z.e-3)]
  have hbc : 0 ≤ z.b*z.c := mul_nonneg (by omega) (by omega)
  have hde : 0 ≤ z.d*z.e := mul_nonneg (by omega) (by omega)
  have hbcf := mul_nonpos_of_nonneg_of_nonpos hbc hf'
  have hdef := mul_nonpos_of_nonneg_of_nonpos hde hf'
  nlinarith [sq_nonneg z.f,hbcf,hdef]

private theorem zero_large_same_sign (z : Six) (hz : isSolution z) (ha : z.a=0)
    (hb : 3 ≤ z.b) (hc : 3 ≤ z.c) (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) :
    (3 ≤ z.d ∧ 3 ≤ z.e) ∨ (z.d ≤ -3 ∧ z.e ≤ -3) := by
  have hs := hz.2
  simp [q2,ha] at hs
  have hdet : -4 ≤ z.c*z.d-z.b*z.e ∧ z.c*z.d-z.b*z.e ≤ 4 := by
    constructor <;> nlinarith [hs]
  by_cases hd0 : 0 ≤ z.d
  · rw [abs_of_nonneg hd0] at hd
    by_cases he0 : 0 ≤ z.e
    · rw [abs_of_nonneg he0] at he
      exact Or.inl ⟨hd,he⟩
    · rw [abs_of_nonpos (by omega : z.e ≤ 0)] at he
      have hcd := mul_nonneg (by omega : 0 ≤ z.c-3) (by omega : 0 ≤ z.d-3)
      have hbe := mul_nonneg (by omega : 0 ≤ z.b-3) (by omega : 0 ≤ -z.e-3)
      exact False.elim (by nlinarith [hdet.2,hcd,hbe])
  · rw [abs_of_nonpos (by omega : z.d ≤ 0)] at hd
    by_cases he0 : 0 ≤ z.e
    · rw [abs_of_nonneg he0] at he
      have hcd := mul_nonneg (by omega : 0 ≤ z.c-3) (by omega : 0 ≤ -z.d-3)
      have hbe := mul_nonneg (by omega : 0 ≤ z.b-3) (by omega : 0 ≤ z.e-3)
      exact False.elim (by nlinarith [hdet.1,hcd,hbe])
    · rw [abs_of_nonpos (by omega : z.e ≤ 0)] at he
      exact Or.inr ⟨by omega,by omega⟩

/-- All sign patterns are included: an orthogonal edge and five other edges
of absolute value at least three admit the same two-letter braid descent.
Sign gauges are used only in the proof and do not increase the output length. -/
theorem zero_large_absolute_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0)
    (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|) (hd : 3 ≤ |z.d|)
    (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word) < l1 z := by
  obtain ⟨s,hs,hwa,hwb,hwc,hr,_⟩ := SignGaugeDescent.first_row_abs_sign_gauge z
  let w := PositiveNormalization.signedSix z s
  have hw := reachable_preserves_solution hr hz
  have hn : IntrinsicSigns.thirdMinorSum w < 0 := by
    have hk := (intrinsicKind_negative_iff z hz).mpr hneg
    rw [reachable_intrinsicKind hz hr] at hk
    exact (intrinsicKind_negative_iff w hw).mp hk
  have hwa' : w.a=0 := by simpa [ha] using hwa
  have hwb' : 3 ≤ w.b := by dsimp [w]; rw [hwb]; exact hb
  have hwc' : 3 ≤ w.c := by dsimp [w]; rw [hwc]; exact hc
  obtain ⟨_,_,_,hwd,hwe,hwf⟩ := SignGaugeDescent.signedSix_abs z s hs
  have hwd' : 3 ≤ |w.d| := by dsimp [w]; rw [hwd]; exact hd
  have hwe' : 3 ≤ |w.e| := by dsimp [w]; rw [hwe]; exact he
  have hwf' : 3 ≤ |w.f| := by dsimp [w]; rw [hwf]; exact hf
  apply SignGaugeDescent.restricted_descent_transfer z s hs (fun word => word ∈ braidWords 2)
  change ∃ word, word ∈ braidWords 2 ∧ l1 (applyWord w word) < l1 w
  obtain ⟨hwdpos,hwepos⟩ | ⟨hwdneg,hweneg⟩ := zero_large_same_sign w hw hwa' hwb' hwc' hwd' hwe'
  · have hfpos := zero_positive_f w hw hwa' hwb' hwc' hwdpos hwepos
    rw [abs_of_pos hfpos] at hwf'
    exact zero_large_positive_descent w hw hn hwa' hwb' hwc' hwdpos hwepos hwf'
  · have hr2 : Reachable w (eps2 w) := ⟨[.s2],rfl⟩
    have hu := reachable_preserves_solution hr2 hw
    have hun : IntrinsicSigns.thirdMinorSum (eps2 w) < 0 := by
      have hk := (intrinsicKind_negative_iff w hw).mpr hn
      rw [reachable_intrinsicKind hw hr2] at hk
      exact (intrinsicKind_negative_iff (eps2 w) hu).mp hk
    have hua : (eps2 w).a=0 := by simp [eps2,hwa']
    have hub : 3 ≤ (eps2 w).b := by simpa [eps2] using hwb'
    have huc : 3 ≤ (eps2 w).c := by simpa [eps2] using hwc'
    have hud : 3 ≤ (eps2 w).d := by simp [eps2]; omega
    have hue : 3 ≤ (eps2 w).e := by simp [eps2]; omega
    have hufpos := zero_positive_f (eps2 w) hu hua hub huc hud hue
    have huf : 3 ≤ (eps2 w).f := by
      have hab : 3 ≤ |(eps2 w).f| := by simpa [eps2] using hwf'
      rwa [abs_of_pos hufpos] at hab
    have hdesc := zero_large_positive_descent (eps2 w) hu hun hua hub huc hud hue huf
    let t : Fin 4 → ℤ := ![1,-1,1,1]
    have ht : ∀ i,(t i)^2=1 := by intro i; fin_cases i <;> norm_num [t]
    have htw : PositiveNormalization.signedSix w t = eps2 w := by
      ext <;> simp [PositiveNormalization.signedSix,eps2,t]
    apply SignGaugeDescent.restricted_descent_transfer w t ht (fun word => word ∈ braidWords 2)
    simpa only [htw] using hdesc

private theorem square_mod_four (n : ℤ) : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
  have h0 : 0 ≤ n%4 := Int.emod_nonneg n (by decide)
  have h4 : n%4 < 4 := Int.emod_lt_of_pos n (by decide)
  have h : n^2%4 = (n%4)*(n%4)%4 := by simpa [pow_two] using Int.mul_emod n n 4
  interval_cases hn : n%4 <;> norm_num [hn] at h ⊢ <;> omega

private theorem sum_squares_not_three_mod_four (e f : ℤ) :
    (e^2+f^2)%4 ≠ 3 := by
  have he := square_mod_four e
  have hf := square_mod_four f
  rw [Int.add_emod]
  rcases he with he | he <;> rcases hf with hf | hf <;> simp [he,hf]

private theorem sum_squares_not_four_mul_sub_nine (e f t : ℤ) :
    e^2+f^2 ≠ 4*t-9 := by
  intro h
  have hm := congrArg (fun n : ℤ => n%4) h
  norm_num [Int.sub_emod,Int.mul_emod] at hm
  exact sum_squares_not_three_mod_four e f hm

private theorem zero_pair_shape (c d e f : ℤ)
    (hz : isSolution ⟨0,0,c,d,e,f⟩) (hd : 4 ≤ d^2) :
    (d = 2 ∧ e = f) ∨ (d = -2 ∧ e = -f) := by
  have h1 := hz.1
  have h2 := hz.2
  simp [q1] at h1
  simp [q2] at h2
  have hcd : c*d = 4 ∨ c*d = -4 := by
    have hfct : (c*d-4)*(c*d+4)=0 := by nlinarith [h2]
    rcases mul_eq_zero.mp hfct with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hdc : d*c = 4 ∨ d*c = -4 := by simpa [mul_comm] using hcd
  have hdivc : c ∣ (4 : ℤ) := by
    rcases hcd with h | h
    · exact ⟨d,h.symm⟩
    · exact ⟨-d,by nlinarith⟩
  have hdivd : d ∣ (4 : ℤ) := by
    rcases hdc with h | h
    · exact ⟨c,h.symm⟩
    · exact ⟨-c,by nlinarith⟩
  have hcn := Int.natAbs_le_of_dvd_ne_zero hdivc (by decide)
  have hdn := Int.natAbs_le_of_dvd_ne_zero hdivd (by decide)
  norm_num at hcn hdn
  have hca : |c| ≤ 4 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcn
  have hda : |d| ≤ 4 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hdn
  obtain ⟨hc0,hc4⟩ := abs_le.mp hca
  obtain ⟨hd0,hd4⟩ := abs_le.mp hda
  have hmod := sum_squares_not_three_mod_four e f
  interval_cases c <;> interval_cases d <;> norm_num at *
  all_goals first
    | exact False.elim (sum_squares_not_four_mul_sub_nine e f (e*f) (by nlinarith [h1]))
    | exact False.elim (sum_squares_not_four_mul_sub_nine e f (-(e*f)) (by nlinarith [h1]))
    | have hs : (e-f)^2=0 := by nlinarith [h1]
      have he := pow_eq_zero hs
      omega
    | have hs : (e+f)^2=0 := by nlinarith [h1]
      have he := pow_eq_zero hs
      omega

/-- Two zero edges incident to the first root force an equal or opposite
pair of columns, and hence an actual finite mutation path to the family. -/
theorem zero_adjacent_pair_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a = 0) (hb : z.b = 0) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have heq : z = ⟨0,0,z.c,z.d,z.e,z.f⟩ := by ext <;> simp [ha,hb]
  have htri := (negative_triangle_inequalities z hz hneg).1
  have hd : 4 ≤ z.d^2 := by simpa [cayleyDefect,ha,hb] using htri
  rw [heq] at hz
  obtain ⟨hd,hef⟩ | ⟨hd,hef⟩ := zero_pair_shape z.c z.d z.e z.f hz hd
  · apply positive_repeated_columns_reachable_family z
      (by simpa only [← heq] using hz)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd,by omega,hef⟩)))
  · apply negative_repeated_columns_reachable_family z
      (by simpa only [← heq] using hz)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd,by omega,hef⟩)))

private theorem negative_of_reachable {z w : Six} (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hr : Reachable z w) :
    IntrinsicSigns.thirdMinorSum w < 0 := by
  have hw := reachable_preserves_solution hr hz
  have hk := (intrinsicKind_negative_iff z hz).mpr hneg
  rw [reachable_intrinsicKind hz hr] at hk
  exact (intrinsicKind_negative_iff w hw).mp hk

/-- Any second zero edge incident to an adjacent orthogonal pair reduces
to the preceding two-zero normal form by at most two actual braid moves. -/
theorem zero_incident_pair_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a = 0)
    (hzero : z.b = 0 ∨ z.c = 0 ∨ z.d = 0 ∨ z.e = 0) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have transport (w : Six) (hr : Reachable z w) (hwa : w.a=0) (hwb : w.b=0) :
      ∃ x y : ℤ, Reachable z (family x y) := by
    obtain ⟨x,y,hxy⟩ := zero_adjacent_pair_reachable_family w
      (reachable_preserves_solution hr hz) (negative_of_reachable hz hneg hr) hwa hwb
    exact ⟨x,y,reachable_trans hr hxy⟩
  rcases hzero with hb | hc | hd | he
  · exact zero_adjacent_pair_reachable_family z hz hneg ha hb
  · exact transport (inv3 z) ⟨[.i3],rfl⟩ (by simp [inv3,ha]) (by simp [inv3,hc])
  · exact transport (mu1 z) ⟨[.m1],rfl⟩ (by simp [mu1,ha]) (by simp [mu1,ha,hd])
  · exact transport (inv3 (mu1 z)) ⟨[.m1,.i3],rfl⟩
      (by simp [inv3,mu1,ha]) (by simp [inv3,mu1,ha,he])

private theorem small_square_bounds (n : ℤ) (hn : n^2 ≤ 8) : -2 ≤ n ∧ n ≤ 2 := by
  constructor
  · by_contra h
    have hn' : n ≤ -3 := by omega
    nlinarith [sq_nonneg (n+3)]
  · by_contra h
    have hn' : 3 ≤ n := by omega
    nlinarith [sq_nonneg (n-3)]

/-- Orthogonal endpoint pairs have bounded remaining coefficients; the
integer equations force a second incident zero and hence the proved reduction. -/
theorem zero_endpoint_pair_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (ha : z.a=0) (hf : z.f=0) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have h1 := hz.1
  have h2 := hz.2
  simp [q1,ha,hf] at h1
  simp [q2,ha,hf] at h2
  have hb := small_square_bounds z.b (by nlinarith [sq_nonneg z.c,sq_nonneg z.d,sq_nonneg z.e])
  have hc := small_square_bounds z.c (by nlinarith [sq_nonneg z.b,sq_nonneg z.d,sq_nonneg z.e])
  have hd := small_square_bounds z.d (by nlinarith [sq_nonneg z.b,sq_nonneg z.c,sq_nonneg z.e])
  have he := small_square_bounds z.e (by nlinarith [sq_nonneg z.b,sq_nonneg z.c,sq_nonneg z.d])
  obtain ⟨hb0,hb2⟩ := hb
  obtain ⟨hc0,hc2⟩ := hc
  obtain ⟨hd0,hd2⟩ := hd
  obtain ⟨he0,he2⟩ := he
  have hzero : z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 := by
    generalize z.b = b at *
    generalize z.c = c at *
    generalize z.d = d at *
    generalize z.e = e at *
    interval_cases b <;> interval_cases c <;> interval_cases d <;> interval_cases e <;>
      norm_num at *
  exact zero_incident_pair_reachable_family z hz hneg ha hzero

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1200000 in
private theorem four_cycle_even (a c d f : ℤ)
    (h : a^2+c^2+d^2+f^2+a*c*d*f = 8) :
    ∃ A C D F : ℤ, a=2*A ∧ c=2*C ∧ d=2*D ∧ f=2*F := by
  have hm := congrArg (fun n : ℤ => n%4) h
  have ha0 : 0 ≤ a%4 := Int.emod_nonneg a (by decide)
  have hc0 : 0 ≤ c%4 := Int.emod_nonneg c (by decide)
  have hd0 : 0 ≤ d%4 := Int.emod_nonneg d (by decide)
  have hf0 : 0 ≤ f%4 := Int.emod_nonneg f (by decide)
  have ha4 : a%4 < 4 := Int.emod_lt_of_pos a (by decide)
  have hc4 : c%4 < 4 := Int.emod_lt_of_pos c (by decide)
  have hd4 : d%4 < 4 := Int.emod_lt_of_pos d (by decide)
  have hf4 : f%4 < 4 := Int.emod_lt_of_pos f (by decide)
  have heven : (a%4=0 ∨ a%4=2) ∧ (c%4=0 ∨ c%4=2) ∧
      (d%4=0 ∨ d%4=2) ∧ (f%4=0 ∨ f%4=2) := by
    interval_cases ha : a%4 <;> interval_cases hc : c%4 <;>
      interval_cases hd : d%4 <;> interval_cases hf : f%4 <;>
      norm_num [Int.add_emod,Int.mul_emod,pow_two,ha,hc,hd,hf] at hm
    all_goals simp [ha,hc,hd,hf]
  have ha : a%2=0 := by omega
  have hc : c%2=0 := by omega
  have hd : d%2=0 := by omega
  have hf : f%2=0 := by omega
  exact ⟨a/2,c/2,d/2,f/2,by omega,by omega,by omega,by omega⟩

private theorem factor_square_sum_bound (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0) :
    u^2+v^2 ≤ (u*v)^2+1 := by
  have hu' : 1 ≤ u^2 := by have h := sq_pos_of_ne_zero hu; omega
  have hv' : 1 ≤ v^2 := by have h := sq_pos_of_ne_zero hv; omega
  have hp := mul_nonneg (by omega : 0 ≤ u^2-1) (by omega : 0 ≤ v^2-1)
  nlinarith [hp]

/-- The crossing pair of zero entries cannot occur on the regular negative
locus. The mod-four equation forces even coordinates, after which elementary
factor bounds contradict the negative marker. -/
theorem crossing_zero_pair_not_negative (z : Six) (hz : isSolution z)
    (hb : z.b=0) (he : z.e=0) : ¬ IntrinsicSigns.thirdMinorSum z < 0 := by
  intro hneg
  have h1 := hz.1
  have h2 := hz.2
  simp [q1,hb,he] at h1
  simp [q2,hb,he] at h2
  have hnorm : z.a^2+z.c^2+z.d^2+z.f^2+z.a*z.c*z.d*z.f=8 := by nlinarith [h1]
  obtain ⟨A,C,D,F,ha,hc,hd,hf⟩ := four_cycle_even z.a z.c z.d z.f hnorm
  have hsum : A^2+C^2+D^2+F^2+4*A*C*D*F=2 := by
    rw [ha,hc,hd,hf] at hnorm
    nlinarith [hnorm]
  have hprod : (A*F+C*D)^2=1 := by
    rw [ha,hc,hd,hf] at h2
    nlinarith [h2]
  have hsize : 2 < A^2+C^2+D^2+F^2 := by
    simp [IntrinsicSigns.thirdMinorSum,hb,he,ha,hc,hd,hf] at hneg
    nlinarith [hneg]
  have hnonzero : A*C*D*F ≠ 0 := by
    intro h0
    nlinarith [hsize,h0]
  have hA : A ≠ 0 := by intro h; simp [h] at hnonzero
  have hC : C ≠ 0 := by intro h; simp [h] at hnonzero
  have hD : D ≠ 0 := by intro h; simp [h] at hnonzero
  have hF : F ≠ 0 := by intro h; simp [h] at hnonzero
  have hAF := factor_square_sum_bound A F hA hF
  have hCD := factor_square_sum_bound C D hC hD
  have hsquares : 2 ≤ (A*F)^2+(C*D)^2 := by
    have hu : 1 ≤ (A*F)^2 := by have h := sq_pos_of_ne_zero (mul_ne_zero hA hF); omega
    have hv : 1 ≤ (C*D)^2 := by have h := sq_pos_of_ne_zero (mul_ne_zero hC hD); omega
    omega
  have hnonneg : 0 ≤ (A*F)*(C*D) := by
    have h : -1 ≤ 2*((A*F)*(C*D)) := by nlinarith [hAF,hCD,hsum,hprod]
    omega
  nlinarith [hprod,hsquares,hnonneg]

def TwoZeroEdges (z : Six) : Prop :=
  (z.a=0 ∧ (z.b=0 ∨ z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0)) ∨
  (z.b=0 ∧ (z.c=0 ∨ z.d=0 ∨ z.e=0 ∨ z.f=0)) ∨
  (z.c=0 ∧ (z.d=0 ∨ z.e=0 ∨ z.f=0)) ∨
  (z.d=0 ∧ (z.e=0 ∨ z.f=0)) ∨ (z.e=0 ∧ z.f=0)

/-- Every negative solution with any two zero edges reaches the family.
This includes all fifteen positions of the orthogonal pairs. -/
theorem two_zero_edges_reachable_family (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzeros : TwoZeroEdges z) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have adjacent (w : Six) (hw : isSolution w) (hn : IntrinsicSigns.thirdMinorSum w < 0)
      (hwa : w.a=0) (hwzero : w.b=0 ∨ w.c=0 ∨ w.d=0 ∨ w.e=0 ∨ w.f=0) :
      ∃ x y : ℤ, Reachable w (family x y) := by
    rcases hwzero with hb | hc | hd | he | hf
    · exact zero_incident_pair_reachable_family w hw hn hwa (Or.inl hb)
    · exact zero_incident_pair_reachable_family w hw hn hwa (Or.inr (Or.inl hc))
    · exact zero_incident_pair_reachable_family w hw hn hwa (Or.inr (Or.inr (Or.inl hd)))
    · exact zero_incident_pair_reachable_family w hw hn hwa (Or.inr (Or.inr (Or.inr he)))
    · exact zero_endpoint_pair_reachable_family w hw hn hwa hf
  have transport (w : Six) (hr : Reachable z w) (hwa : w.a=0)
      (hwzero : w.b=0 ∨ w.c=0 ∨ w.d=0 ∨ w.e=0 ∨ w.f=0) :
      ∃ x y : ℤ, Reachable z (family x y) := by
    obtain ⟨x,y,hxy⟩ := adjacent w (reachable_preserves_solution hr hz)
      (negative_of_reachable hz hneg hr) hwa hwzero
    exact ⟨x,y,reachable_trans hr hxy⟩
  rcases hzeros with ⟨ha,hzero⟩ | ⟨hb,hzero⟩ | ⟨hc,hzero⟩ | ⟨hd,hzero⟩ | ⟨he,hf⟩
  · exact adjacent z hz hneg ha hzero
  · rcases hzero with hc | hd | he | hf
    · exact transport (inv2 z) ⟨[.i2],rfl⟩ (by simp [inv2,hb])
        (Or.inr (Or.inl (by simp [inv2,hc])))
    · exact transport (mu2 z) ⟨[.m2],rfl⟩ (by simp [mu2,hb,hd])
        (Or.inr (Or.inr (Or.inl (by simp [mu2,hd]))))
    · exact False.elim (crossing_zero_pair_not_negative z hz hb he hneg)
    · exact transport (inv2 z) ⟨[.i2],rfl⟩ (by simp [inv2,hb])
        (Or.inr (Or.inr (Or.inr (Or.inl (by simp [inv2,hf])))))
  · rcases hzero with hd | he | hf
    · exact transport (mu2 (mu1 z)) ⟨[.m1,.m2],rfl⟩ (by simp [mu2,mu1,hd])
        (Or.inr (Or.inr (Or.inr (Or.inr (by simp [mu2,mu1,hc])))))
    · exact transport (mu2 (inv3 z)) ⟨[.i3,.m2],rfl⟩ (by simp [mu2,inv3,hc,he])
        (Or.inr (Or.inr (Or.inl (by simp [mu2,inv3,he]))))
    · exact transport (inv2 (mu3 z)) ⟨[.m3,.i2],rfl⟩ (by simp [inv2,mu3,hc,hf])
        (Or.inr (Or.inr (Or.inr (Or.inl (by simp [inv2,mu3,hf])))))
  · rcases hzero with he | hf
    · exact transport (inv2 (inv1 z)) ⟨[.i1,.i2],rfl⟩ (by simp [inv2,inv1,hd])
        (Or.inr (Or.inl (by simp [inv2,inv1,he])))
    · exact transport (inv2 (inv1 z)) ⟨[.i1,.i2],rfl⟩ (by simp [inv2,inv1,hd])
        (Or.inr (Or.inr (Or.inr (Or.inl (by simp [inv2,inv1,hf])))))
  · exact transport (inv2 (mu3 (inv1 z))) ⟨[.i1,.m3,.i2],rfl⟩
      (by simp [inv2,mu3,inv1,he,hf])
      (Or.inr (Or.inr (Or.inr (Or.inl (by simp [inv2,mu3,inv1,hf])))))

/-- Three affine-pair roots, with arbitrary pairings to the fourth root. -/
def affineTriangle (t u v : ℤ) : Six := ⟨2,2,t,2,t-u,t-u-v⟩

private theorem affineTriangle_mu1 (t u v : ℤ) :
    mu1 (affineTriangle t u v) = affineTriangle (t+u) u (u+v) := by
  ext <;> simp [mu1,affineTriangle] <;> ring
private theorem affineTriangle_inv1 (t u v : ℤ) :
    inv1 (affineTriangle t u v) = affineTriangle (t-u) u (v-u) := by
  ext <;> simp [inv1,affineTriangle] <;> ring
private theorem affineTriangle_mu2 (t u v : ℤ) :
    mu2 (affineTriangle t u v) = affineTriangle t (u-v) v := by
  ext <;> simp [mu2,affineTriangle] <;> ring
private theorem affineTriangle_inv2 (t u v : ℤ) :
    inv2 (affineTriangle t u v) = affineTriangle t (u+v) v := by
  ext <;> simp [inv2,affineTriangle] <;> ring

/-- Euclid's four integral elementary operations lift to finite mutations
inside the affine triangle, retaining the arbitrary fourth-root pairings. -/
theorem pairReach_affineTriangle {u v u' v' : ℤ} (h : Dihedral.PairReach u v u' v') :
    ∀ t : ℤ, ∃ t' : ℤ, Reachable (affineTriangle t u v) (affineTriangle t' u' v') := by
  induction h with
  | refl u v => intro t; exact ⟨t,reachable_refl _⟩
  | addUpper u v => intro t; exact ⟨t,[.i2],affineTriangle_inv2 t u v⟩
  | subUpper u v => intro t; exact ⟨t,[.m2],affineTriangle_mu2 t u v⟩
  | addLower u v => intro t; exact ⟨t+u,[.m1],affineTriangle_mu1 t u v⟩
  | subLower u v => intro t; exact ⟨t-u,[.i1],affineTriangle_inv1 t u v⟩
  | trans h h' ih ih' =>
    intro t
    obtain ⟨s,hs⟩ := ih t
    obtain ⟨r,hr⟩ := ih' s
    exact ⟨r,reachable_trans hs hr⟩

/-- An arbitrary integral affine triangle in an actual solution reaches
equal columns by the terminating Euclidean algorithm. -/
theorem triangle_two_reachable_family (c e f : ℤ)
    (hz : isSolution ⟨2,2,c,2,e,f⟩) :
    ∃ x y : ℤ, Reachable ⟨2,2,c,2,e,f⟩ (family x y) := by
  obtain ⟨g,_,hg⟩ := Dihedral.pairReach_reduce (c-e) (e-f)
  have hrot := Dihedral.PairReach.trans hg (Dihedral.pairReach_rotate g 0)
  obtain ⟨t,ht⟩ := pairReach_affineTriangle hrot c
  have hstart : affineTriangle c (c-e) (e-f) = ⟨2,2,c,2,e,f⟩ := by
    ext <;> simp [affineTriangle] <;> ring
  rw [hstart] at ht
  have hw := reachable_preserves_solution ht hz
  have hc : PositiveRepeatedColumns (affineTriangle t 0 (-g)) :=
    Or.inl ⟨rfl,rfl,by simp [affineTriangle]⟩
  obtain ⟨x,y,hxy⟩ := positive_repeated_columns_reachable_family _ hw hc
  exact ⟨x,y,reachable_trans ht hxy⟩

/-- At an affine edge, equality of the two pairings to a third root either
already gives repeated columns or forces an affine triangle. Both alternatives
reach the family by actual finite mutations, with no sign assumption. -/
theorem edge_two_equal_reachable_family (b c e f : ℤ)
    (hz : isSolution ⟨2,b,c,b,e,f⟩) :
    ∃ x y : ℤ, Reachable ⟨2,b,c,b,e,f⟩ (family x y) := by
  by_cases hv : c = e
  · exact positive_repeated_columns_reachable_family _ hz (Or.inl ⟨rfl,rfl,hv⟩)
  have hsign : q2 ⟨2,b,c,b,e,f⟩ = 4 ∨ q2 ⟨2,b,c,b,e,f⟩ = -4 := by
    have hfct : (q2 ⟨2,b,c,b,e,f⟩-4)*(q2 ⟨2,b,c,b,e,f⟩+4)=0 := by
      nlinarith [hz.2]
    rcases mul_eq_zero.mp hfct with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have ht : ∃ t : ℤ, b*(c-e)=2*t ∧ (c-e)^2=t^2 := by
    rcases hsign with hp | hn
    · have hc := edge_two_conic_plus b c b e f hz.1 hp
      refine ⟨2-f,?_,?_⟩
      · simp [q2] at hp
        nlinarith [hp]
      · have hc' : (c-e)^2=(f-2)^2 := by simpa using hc
        nlinarith [hc']
    · have hc := edge_two_conic_minus b c b e f hz.1 hn
      refine ⟨-f-2,?_,?_⟩
      · simp [q2] at hn
        nlinarith [hn]
      · have hc' : (c-e)^2=(f+2)^2 := by simpa using hc
        nlinarith [hc']
  obtain ⟨t,hprod,hconic⟩ := ht
  have hfct : (b^2-4)*(c-e)^2=0 := by
    calc
      (b^2-4)*(c-e)^2 = (b*(c-e))^2-4*(c-e)^2 := by ring
      _ = (2*t)^2-4*(c-e)^2 := by rw [hprod]
      _ = 0 := by nlinarith [hconic]
  have hb : b^2=4 := by
    rcases mul_eq_zero.mp hfct with h | h
    · omega
    · have he := pow_eq_zero h
      exact False.elim (hv (by omega))
  have hbf : (b-2)*(b+2)=0 := by nlinarith [hb]
  rcases mul_eq_zero.mp hbf with hp | hn
  · have hb : b=2 := by omega
    subst b
    exact triangle_two_reachable_family c e f hz
  · have hb : b=-2 := by omega
    subst b
    have hr : Reachable ⟨2,-2,c,-2,e,f⟩ ⟨2,2,c,2,e,-f⟩ := by
      refine ⟨[.s3],?_⟩
      simp [applyWord,step,eps3]
    obtain ⟨x,y,hxy⟩ := triangle_two_reachable_family c e (-f)
      (reachable_preserves_solution hr hz)
    exact ⟨x,y,reachable_trans hr hxy⟩

/-- Either pair of equal neighboring coefficients at a positive affine edge
is sufficient for the complete arithmetic reduction. -/
theorem affine_edge_equal_reachable_family (z : Six) (hz : isSolution z)
    (ha : z.a = 2) (heq : z.b = z.d ∨ z.c = z.e) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  rcases heq with hb | hc
  · have ht : z = ⟨2,z.b,z.c,z.b,z.e,z.f⟩ := by ext <;> simp [ha,hb]
    rw [ht] at hz ⊢
    exact edge_two_equal_reachable_family z.b z.c z.e z.f hz
  · have hr : Reachable z (inv3 z) := ⟨[.i3],rfl⟩
    have hw := reachable_preserves_solution hr hz
    have ht : inv3 z = ⟨2,z.c,z.f*z.c-z.b,z.c,z.f*z.e-z.d,z.f⟩ := by
      ext <;> simp [inv3,ha,hc]
    rw [ht] at hw
    obtain ⟨x,y,hxy⟩ := edge_two_equal_reachable_family z.c
      (z.f*z.c-z.b) (z.f*z.e-z.d) z.f hw
    exact ⟨x,y,reachable_trans hr (by simpa only [ht] using hxy)⟩

/-- The signed affine-edge version includes opposite adjacent pairings. -/
theorem signed_affine_edge_equal_reachable_family (z : Six) (hz : isSolution z)
    (ha : (z.a=2 ∧ (z.b=z.d ∨ z.c=z.e)) ∨
      (z.a=-2 ∧ (z.b=-z.d ∨ z.c=-z.e))) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  rcases ha with ⟨ha,heq⟩ | ⟨ha,heq⟩
  · exact affine_edge_equal_reachable_family z hz ha heq
  · have hr : Reachable z (eps1 z) := ⟨[.s1],rfl⟩
    have hw := reachable_preserves_solution hr hz
    have hwa : (eps1 z).a = 2 := by simp [eps1,ha]
    have hweq : (eps1 z).b = (eps1 z).d ∨ (eps1 z).c = (eps1 z).e := by
      rcases heq with hb | hc
      · exact Or.inl (by simp [eps1,hb])
      · exact Or.inr (by simp [eps1,hc])
    obtain ⟨x,y,hxy⟩ := affine_edge_equal_reachable_family _ hw hwa hweq
    exact ⟨x,y,reachable_trans hr hxy⟩

end SerreMarkov.NegativeBoundary
