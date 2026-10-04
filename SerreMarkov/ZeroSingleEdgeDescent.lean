import SerreMarkov.NegativeBoundary

/-! # Strict short-word descent with one zero edge

Every other edge has absolute value at least three. The orthogonal triangle
reductions handle four positions directly; the two crossing positions use
an integral quadratic inequality and a nonincreasing change to an adjacent
orthogonal pair. No global descent hypothesis is assumed.
-/

namespace SerreMarkov.ZeroSingleEdgeDescent
open NegativeDescent NegativeTriangles

set_option linter.unusedSimpArgs false

def orthogonalWords : List (List Generator) := [[.m2],[.m1,.m2],[.m3],[.i3]]

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
    ∃ word : List Generator, word ∈ orthogonalWords ∧ l1 (applyWord z word) < l1 z := by
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
    ∃ word : List Generator, word ∈ orthogonalWords ∧ l1 (applyWord z word) < l1 z := by
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
  apply SignGaugeDescent.restricted_descent_transfer z s hs (fun word => word ∈ orthogonalWords)
  change ∃ word, word ∈ orthogonalWords ∧ l1 (applyWord w word) < l1 w
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
    apply SignGaugeDescent.restricted_descent_transfer w t ht (fun word => word ∈ orthogonalWords)
    simpa only [htw] using hdesc

def modelC (z : Six) : Six := ⟨0,z.a,z.b,z.e,z.f,z.d⟩

private theorem modelC_solution (z : Six) (hz : isSolution z) (hzero : z.c=0) :
    isSolution (modelC z) := by
  have hq : q1 (modelC z)=q1 z := by simp [q1,modelC,hzero]; ring
  have hp : q2 (modelC z)=-q2 z := by simp [q2,modelC,hzero]; ring
  exact ⟨hq.trans hz.1,by rw [hp,neg_sq]; exact hz.2⟩

private theorem modelC_marker (z : Six) (hzero : z.c=0) :
    IntrinsicSigns.thirdMinorSum (modelC z)=IntrinsicSigns.thirdMinorSum z := by
  simp [IntrinsicSigns.thirdMinorSum,modelC,hzero]
  ring

private theorem modelC_height (z : Six) (hzero : z.c=0) : l1 (modelC z)=l1 z := by
  simp [l1,modelC,hzero]
  omega

private theorem modelC_word_transport (z : Six) (hzero : z.c=0)
    (word : List Generator) (hw : word ∈ orthogonalWords) :
    ∃ actual : List Generator, actual ∈ braidWords 2 ∧
      l1 (applyWord z actual)=l1 (applyWord (modelC z) word) := by
  simp [orthogonalWords] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨[.i3],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelC,hzero,mul_comm]
  · refine ⟨[.m1],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelC,hzero,mul_comm]
    omega
  · refine ⟨[.m2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelC,hzero,mul_comm]
    omega
  · refine ⟨[.i2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelC,hzero,mul_comm]
    omega

theorem zero_c_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : z.c=0)
    (ha : 3 ≤ |z.a|) (hb : 3 ≤ |z.b|) (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word)<l1 z := by
  have hm := modelC_solution z hz hzero
  have hn : IntrinsicSigns.thirdMinorSum (modelC z)<0 := by rw [modelC_marker z hzero]; exact hneg
  obtain ⟨word,hw,hdrop⟩ := zero_large_absolute_descent (modelC z) hm hn rfl
    (by simpa [modelC] using ha)
    (by simpa [modelC] using hb)
    (by simpa [modelC] using he)
    (by simpa [modelC] using hf)
    (by simpa [modelC] using hd)
  obtain ⟨actual,ha,heq⟩ := modelC_word_transport z hzero word hw
  refine ⟨actual,ha,?_⟩
  rw [heq]
  rw [← modelC_height z hzero]
  exact hdrop

def modelD (z : Six) : Six := ⟨0,z.a,z.e,z.b,z.f,z.c⟩

private theorem modelD_solution (z : Six) (hz : isSolution z) (hzero : z.d=0) :
    isSolution (modelD z) := by
  have hq : q1 (modelD z)=q1 z := by simp [q1,modelD,hzero]; ring
  have hp : q2 (modelD z)=-q2 z := by simp [q2,modelD,hzero]; ring
  exact ⟨hq.trans hz.1,by rw [hp,neg_sq]; exact hz.2⟩

private theorem modelD_marker (z : Six) (hzero : z.d=0) :
    IntrinsicSigns.thirdMinorSum (modelD z)=IntrinsicSigns.thirdMinorSum z := by
  simp [IntrinsicSigns.thirdMinorSum,modelD,hzero]
  ring

private theorem modelD_height (z : Six) (hzero : z.d=0) : l1 (modelD z)=l1 z := by
  simp [l1,modelD,hzero]
  omega

private theorem modelD_word_transport (z : Six) (hzero : z.d=0)
    (word : List Generator) (hw : word ∈ orthogonalWords) :
    ∃ actual : List Generator, actual ∈ braidWords 2 ∧
      l1 (applyWord z actual)=l1 (applyWord (modelD z) word) := by
  simp [orthogonalWords] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨[.m3],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelD,hzero,mul_comm]
    omega
  · refine ⟨[.i1],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelD,hzero,mul_comm]
    omega
  · refine ⟨[.m1,.m2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelD,hzero,mul_comm]
    omega
  · refine ⟨[.i3,.i2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelD,hzero,mul_comm]
    omega

theorem zero_d_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : z.d=0)
    (ha : 3 ≤ |z.a|) (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|) (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word)<l1 z := by
  have hm := modelD_solution z hz hzero
  have hn : IntrinsicSigns.thirdMinorSum (modelD z)<0 := by rw [modelD_marker z hzero]; exact hneg
  obtain ⟨word,hw,hdrop⟩ := zero_large_absolute_descent (modelD z) hm hn rfl
    (by simpa [modelD] using ha)
    (by simpa [modelD] using he)
    (by simpa [modelD] using hb)
    (by simpa [modelD] using hf)
    (by simpa [modelD] using hc)
  obtain ⟨actual,ha,heq⟩ := modelD_word_transport z hzero word hw
  refine ⟨actual,ha,?_⟩
  rw [heq]
  rw [← modelD_height z hzero]
  exact hdrop

def modelF (z : Six) : Six := ⟨0,z.c,z.e,z.b,z.d,z.a⟩

private theorem modelF_solution (z : Six) (hz : isSolution z) (hzero : z.f=0) :
    isSolution (modelF z) := by
  have hq : q1 (modelF z)=q1 z := by simp [q1,modelF,hzero]; ring
  have hp : q2 (modelF z)=-q2 z := by simp [q2,modelF,hzero]; ring
  exact ⟨hq.trans hz.1,by rw [hp,neg_sq]; exact hz.2⟩

private theorem modelF_marker (z : Six) (hzero : z.f=0) :
    IntrinsicSigns.thirdMinorSum (modelF z)=IntrinsicSigns.thirdMinorSum z := by
  simp [IntrinsicSigns.thirdMinorSum,modelF,hzero]
  ring

private theorem modelF_height (z : Six) (hzero : z.f=0) : l1 (modelF z)=l1 z := by
  simp [l1,modelF,hzero]
  omega

private theorem modelF_word_transport (z : Six) (hzero : z.f=0)
    (word : List Generator) (hw : word ∈ orthogonalWords) :
    ∃ actual : List Generator, actual ∈ braidWords 2 ∧
      l1 (applyWord z actual)=l1 (applyWord (modelF z) word) := by
  simp [orthogonalWords] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨[.i2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelF,hzero,mul_comm]
    omega
  · refine ⟨[.i3,.i2],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelF,hzero,mul_comm]
    omega
  · refine ⟨[.m1],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelF,hzero,mul_comm]
    omega
  · refine ⟨[.i1],by decide,?_⟩
    simp [l1,applyWord,step,mu1,inv1,mu2,inv2,mu3,inv3,modelF,hzero,mul_comm]
    omega

theorem zero_f_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : z.f=0)
    (ha : 3 ≤ |z.a|) (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|) (hd : 3 ≤ |z.d|) (he : 3 ≤ |z.e|) :
    ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word)<l1 z := by
  have hm := modelF_solution z hz hzero
  have hn : IntrinsicSigns.thirdMinorSum (modelF z)<0 := by rw [modelF_marker z hzero]; exact hneg
  obtain ⟨word,hw,hdrop⟩ := zero_large_absolute_descent (modelF z) hm hn rfl
    (by simpa [modelF] using hc)
    (by simpa [modelF] using he)
    (by simpa [modelF] using hb)
    (by simpa [modelF] using hd)
    (by simpa [modelF] using ha)
  obtain ⟨actual,ha,heq⟩ := modelF_word_transport z hzero word hw
  refine ⟨actual,ha,?_⟩
  rw [heq]
  rw [← modelF_height z hzero]
  exact hdrop

private theorem quadratic_phase_pos (T U E S : ℤ) (hT : 0<T) (hU : U<0)
    (hE : 0≤E) (hquad : E^2-(T+U)*E+T*U+S=8)
    (hbound : 2*T*U+4*S≤32) : |T-E|≤|E| := by
  have hDT : T^2 < (2*E-T-U)^2 := by
    have hs := sq_pos_of_ne_zero (ne_of_lt hU)
    nlinarith [hquad,hbound,hs]
  have hDU : U^2 < (2*E-T-U)^2 := by
    have hs := sq_pos_of_ne_zero (ne_of_gt hT)
    nlinarith [hquad,hbound,hs]
  have hTE : T ≤ 2*E := by
    by_contra h
    have hsmall : 2*E<T := by omega
    have hP : 0 < (2*E-U)*(2*E-U-2*T) := by nlinarith [hDT]
    have hQ : 0 < (2*E-T)*(2*E-T-2*U) := by nlinarith [hDU]
    have hA : 0 < 2*E-U := by omega
    have hB : 0 < 2*E-U-2*T := by
      by_contra hn
      have hp := mul_nonpos_of_nonneg_of_nonpos hA.le (by omega : 2*E-U-2*T≤0)
      nlinarith [hP,hp]
    have hC : 2*E-T < 0 := by omega
    have hD : 2*E-T-2*U < 0 := by
      by_contra hn
      have hp := mul_nonpos_of_nonpos_of_nonneg hC.le (by omega : 0≤2*E-T-2*U)
      nlinarith [hQ,hp]
    omega
  rw [abs_of_nonneg hE]
  exact abs_le.mpr ⟨by omega,by omega⟩

private theorem quadratic_phase_opposite (T U E S : ℤ) (hTU : T*U<0)
    (hquad : E^2-(T+U)*E+T*U+S=8) (hbound : 2*T*U+4*S≤32) :
    |T-E|≤|E| ∨ |U-E|≤|E| := by
  have positive_negative (T U : ℤ) (hT : 0<T) (hU : U<0)
      (hq : E^2-(T+U)*E+T*U+S=8) (hb : 2*T*U+4*S≤32) :
      |T-E|≤|E| ∨ |U-E|≤|E| := by
    by_cases hE : 0≤E
    · exact Or.inl (quadratic_phase_pos T U E S hT hU hE hq hb)
    · have h := quadratic_phase_pos (-U) (-T) (-E) S (by omega) (by omega)
        (by omega) (by nlinarith [hq]) (by nlinarith [hb])
      apply Or.inr
      calc
        |U-E| = |E-U| := abs_sub_comm U E
        _ = |-U - -E| := by congr 1; ring
        _ ≤ |-E| := h
        _ = |E| := abs_neg E
  rcases mul_neg_iff.mp hTU with ⟨hT,hU⟩ | ⟨hT,hU⟩
  · exact positive_negative T U hT hU hquad hbound
  · have h := positive_negative U T hU hT (by nlinarith [hquad]) (by nlinarith [hbound])
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

private theorem abs_three_square (n : ℤ) (h : 3≤|n|) : 9≤n^2 := by
  nlinarith [sq_nonneg (|n|-3),sq_abs n]

/-- The four outer factors at a crossing orthogonal pair force one of the
two changes toward an adjacent orthogonal pair to be nonincreasing. -/
private theorem diagonal_phase (a c d f E : ℤ)
    (ha : 3≤|a|) (hc : 3≤|c|) (hd : 3≤|d|) (hf : 3≤|f|)
    (hp : (a*f+c*d)^2=16)
    (hq : E^2-(a*c+d*f)*E+a*c*d*f+(a^2+c^2+d^2+f^2)=8) :
    |a*c-E|≤|E| ∨ |d*f-E|≤|E| := by
  have ha9 := abs_three_square a ha
  have hc9 := abs_three_square c hc
  have hd9 := abs_three_square d hd
  have hf9 := abs_three_square f hf
  have hAF : 9≤|a*f| := by
    rw [abs_mul]
    nlinarith [mul_nonneg (by omega : 0≤|a|-3) (by omega : 0≤|f|-3)]
  have hCD : 9≤|c*d| := by
    rw [abs_mul]
    nlinarith [mul_nonneg (by omega : 0≤|c|-3) (by omega : 0≤|d|-3)]
  have hAFsq : 81≤(a*f)^2 := by nlinarith [sq_nonneg (|a*f|-9),sq_abs (a*f)]
  have hCDsq : 81≤(c*d)^2 := by nlinarith [sq_nonneg (|c*d|-9),sq_abs (c*d)]
  have hneg : (a*c)*(d*f)<0 := by
    by_contra h
    have h0 : 0≤(a*c)*(d*f) := by omega
    nlinarith only [hp,hAFsq,hCDsq,h0]
  have hprod : 81≤|(a*c)*(d*f)| := by
    have heq : (a*c)*(d*f)=(a*f)*(c*d) := by ring
    rw [heq,abs_mul]
    nlinarith [mul_nonneg (by omega : 0≤|a*f|-9) (by omega : 0≤|c*d|-9)]
  rw [abs_of_neg hneg] at hprod
  have hfactorAF := mul_nonneg (by omega : 0≤a^2-9) (by omega : 0≤f^2-9)
  have hfactorCD := mul_nonneg (by omega : 0≤c^2-9) (by omega : 0≤d^2-9)
  have hbound : 2*((a*c)*(d*f))+4*(a^2+c^2+d^2+f^2)≤32 := by
    nlinarith only [hp,hfactorAF,hfactorCD,hprod]
  exact quadratic_phase_opposite (a*c) (d*f) E (a^2+c^2+d^2+f^2) hneg
    (by nlinarith only [hq]) (by nlinarith only [hbound])


private theorem negative_after_step (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (g : Generator) :
    IntrinsicSigns.thirdMinorSum (step g z) < 0 := by
  have hr : Reachable z (step g z) := ⟨[g],rfl⟩
  have hw := reachable_preserves_solution hr hz
  apply (intrinsicKind_negative_iff _ hw).mp
  rw [← reachable_intrinsicKind hz hr]
  exact (intrinsicKind_negative_iff _ hz).mpr hneg

private theorem integer_height_le (z w : Six) (h : integerL1 w ≤ integerL1 z) :
    l1 w ≤ l1 z := by
  rw [integerL1_cast, integerL1_cast] at h
  exact_mod_cast h

private theorem integer_height_eq (z w : Six) (h : l1 w = l1 z) :
    integerL1 w = integerL1 z := by
  rw [integerL1_cast, integerL1_cast, h]

private theorem phase_then_descent (z : Six) (g : Generator) (hg : g ∈ braidMoves)
    (hle : l1 (step g z) ≤ l1 z)
    (hnext : l1 (step g z) = l1 z →
      ∃ word : List Generator, word ∈ braidWords 2 ∧
        l1 (applyWord (step g z) word) < l1 (step g z)) :
    ∃ word : List Generator, word ∈ braidWords 3 ∧ l1 (applyWord z word) < l1 z := by
  by_cases hdrop : l1 (step g z) < l1 z
  · refine ⟨[g],(mem_braidWords_iff 3 [g]).mpr ?_,hdrop⟩
    simp [hg]
  · have heq : l1 (step g z) = l1 z := by omega
    obtain ⟨word,hw,hd⟩ := hnext heq
    obtain ⟨hlen,hletters⟩ := (mem_braidWords_iff 2 word).mp hw
    refine ⟨g::word,(mem_braidWords_iff 3 (g::word)).mpr ?_,?_⟩
    · constructor
      · simp only [List.length_cons]; omega
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hg
        · exact hletters k hk
    · change l1 (applyWord (step g z) word) < l1 z
      omega

/-- A crossing zero in position `b` reaches strict descent within three braid moves. -/
theorem zero_b_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : z.b=0)
    (ha : 3 ≤ |z.a|) (hc : 3 ≤ |z.c|) (hd : 3 ≤ |z.d|)
    (he : 3 ≤ |z.e|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word ∈ braidWords 3 ∧ l1 (applyWord z word)<l1 z := by
  have hq1 := hz.1
  have hq2 := hz.2
  simp only [q1,q2,hzero,zero_mul,mul_zero,add_zero,sub_zero,zero_pow (by decide : 2≠0)] at hq1 hq2
  have hphase := diagonal_phase z.a z.c z.d z.f z.e ha hc hd hf hq2
    (by nlinarith only [hq1])
  rcases hphase with hphase | hphase
  · apply phase_then_descent z .m1 (by decide)
    · apply integer_height_le
      simp [integerL1,step,mu1,hzero]
      omega
    · intro heq
      have hi := integer_height_eq z (step .m1 z) heq
      have he : |z.a*z.c-z.e|=|z.e| := by
        simp [integerL1,step,mu1,hzero] at hi
        omega
      apply zero_d_large_descent (step .m1 z)
        (reachable_preserves_solution ⟨[.m1],rfl⟩ hz)
        (negative_after_step z hz hneg .m1)
      · simp [step,mu1,hzero]
      · simpa [step,mu1] using ha
      · simpa [step,mu1,hzero] using hd
      · simpa [step,mu1,he] using ‹3≤|z.e|›
      · simpa [step,mu1] using hc
      · simpa [step,mu1] using hf
  · apply phase_then_descent z .i2 (by decide)
    · apply integer_height_le
      simp [integerL1,step,inv2,hzero]
      omega
    · intro heq
      have hi := integer_height_eq z (step .i2 z) heq
      have hnew : |z.d*z.f-z.e|=|z.e| := by
        simp [integerL1,step,inv2,hzero] at hi
        omega
      exact NegativeBoundary.zero_large_absolute_descent (step .i2 z)
        (reachable_preserves_solution ⟨[.i2],rfl⟩ hz)
        (negative_after_step z hz hneg .i2)
        (by simp [step,inv2,hzero])
        (by simpa [step,inv2,hzero] using ha)
        (by simpa [step,inv2] using hc)
        (by simpa [step,inv2] using hd)
        (by simpa [step,inv2] using hf)
        (by simpa [step,inv2,hnew] using he)

/-- The other crossing zero, in position `e`, has the same three-move bound. -/
theorem zero_e_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : z.e=0)
    (ha : 3 ≤ |z.a|) (hb : 3 ≤ |z.b|) (hc : 3 ≤ |z.c|)
    (hd : 3 ≤ |z.d|) (hf : 3 ≤ |z.f|) :
    ∃ word : List Generator, word ∈ braidWords 3 ∧ l1 (applyWord z word)<l1 z := by
  have hq1 := hz.1
  have hq2 := hz.2
  simp only [q1,q2,hzero,zero_mul,mul_zero,add_zero,sub_zero,zero_pow (by decide : 2≠0)] at hq1 hq2
  have hphase := diagonal_phase z.a z.d z.c z.f z.b ha hd hc hf
    (by nlinarith only [hq2]) (by nlinarith only [hq1])
  rcases hphase with hphase | hphase
  · apply phase_then_descent z .m2 (by decide)
    · apply integer_height_le
      simp [integerL1,step,mu2,hzero]
      omega
    · intro heq
      have hi := integer_height_eq z (step .m2 z) heq
      have hnew : |z.a*z.d-z.b|=|z.b| := by
        simp [integerL1,step,mu2,hzero] at hi
        omega
      exact zero_f_large_descent (step .m2 z)
        (reachable_preserves_solution ⟨[.m2],rfl⟩ hz)
        (negative_after_step z hz hneg .m2)
        (by simp [step,mu2,hzero])
        (by simpa [step,mu2,hnew] using hb)
        (by simpa [step,mu2] using ha)
        (by simpa [step,mu2] using hc)
        (by simpa [step,mu2] using hd)
        (by simpa [step,mu2,hzero] using hf)
  · apply phase_then_descent z .i3 (by decide)
    · apply integer_height_le
      simp [integerL1,step,inv3,hzero,mul_comm]
      omega
    · intro heq
      have hi := integer_height_eq z (step .i3 z) heq
      have hnew : |z.f*z.c-z.b|=|z.b| := by
        simp [integerL1,step,inv3,hzero] at hi
        omega
      exact zero_d_large_descent (step .i3 z)
        (reachable_preserves_solution ⟨[.i3],rfl⟩ hz)
        (negative_after_step z hz hneg .i3)
        (by simp [step,inv3,hzero])
        (by simpa [step,inv3] using ha)
        (by simpa [step,inv3] using hc)
        (by simpa [step,inv3,hnew] using hb)
        (by simpa [step,inv3,hzero] using hd)
        (by simpa [step,inv3] using hf)


/-- Exactly one edge is zero and the other five have absolute value at least three. -/
def SingleZeroLarge (z : Six) : Prop :=
  (z.a=0 ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (z.b=0 ∧ 3≤|z.a| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (z.c=0 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.d| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (z.d=0 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.e| ∧ 3≤|z.f|) ∨
  (z.e=0 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.f|) ∨
  (z.f=0 ∧ 3≤|z.a| ∧ 3≤|z.b| ∧ 3≤|z.c| ∧ 3≤|z.d| ∧ 3≤|z.e|)

private theorem extend_two (z : Six)
    (h : ∃ word : List Generator, word ∈ braidWords 2 ∧ l1 (applyWord z word)<l1 z) :
    ∃ word : List Generator, word ∈ braidWords 3 ∧ l1 (applyWord z word)<l1 z := by
  obtain ⟨word,hw,hd⟩ := h
  obtain ⟨hlen,hletters⟩ := (mem_braidWords_iff 2 word).mp hw
  exact ⟨word,(mem_braidWords_iff 3 word).mpr ⟨by omega,hletters⟩,hd⟩

/-- Unconditional strict L1 descent for a zero edge in any position.
The resulting word contains at most three forward or inverse braid generators. -/
theorem zero_single_edge_large_descent (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) (hzero : SingleZeroLarge z) :
    ∃ word : List Generator, word ∈ braidWords 3 ∧ l1 (applyWord z word)<l1 z := by
  rcases hzero with ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩ |
    ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩ |
    ⟨h0,h1,h2,h3,h4,h5⟩ | ⟨h0,h1,h2,h3,h4,h5⟩
  · exact extend_two z (NegativeBoundary.zero_large_absolute_descent z hz hneg h0 h1 h2 h3 h4 h5)
  · exact zero_b_large_descent z hz hneg h0 h1 h2 h3 h4 h5
  · exact extend_two z (zero_c_large_descent z hz hneg h0 h1 h2 h3 h4 h5)
  · exact extend_two z (zero_d_large_descent z hz hneg h0 h1 h2 h3 h4 h5)
  · exact zero_e_large_descent z hz hneg h0 h1 h2 h3 h4 h5
  · exact extend_two z (zero_f_large_descent z hz hneg h0 h1 h2 h3 h4 h5)

end SerreMarkov.ZeroSingleEdgeDescent
