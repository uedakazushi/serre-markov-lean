import SerreMarkov.NegativeBoundary
import SerreMarkov.NegativeTwoEdge

/-!
# Small unit triangles reduce to actual families

These statements use the integer solution equations and explicit authorized
mutation words. No negative classification or unproved boundary branch is used.
-/

namespace SerreMarkov.NegativeUnitSmall

open NegativeBoundary NegativeTriangles

/-- The solution equations force the two remaining columns to agree at the
unit-unit-affine triangle. -/
theorem unit_unit_affine_columns (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=2) : z.e=z.f := by
  have h1 := hz.1
  have h2 := hz.2
  simp only [q1,q2,ha,hb,hd,one_mul,one_pow] at h1 h2
  nlinarith [sq_nonneg (z.e-z.f)]

theorem unit_unit_affine_reachable_family (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hef := unit_unit_affine_columns z hz ha hb hd
  apply positive_repeated_columns_reachable_family z hz
  unfold PositiveRepeatedColumns
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd,ha.trans hb.symm,hef⟩)))

private theorem abs_eq_one_cases (x : ℤ) (hx : |x|=1) : x=1 ∨ x=-1 := by
  have h := (abs_eq (by norm_num : (0:ℤ)≤1)).mp hx
  exact h

/-- Every signed unit-unit-affine triangle of positive product reduces to
an actual family, with all other coefficients arbitrary. -/
theorem signed_unit_unit_affine_reachable_family (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hb : |z.b|=1) (hp : z.a*z.b*z.d=2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  rcases abs_eq_one_cases z.a ha with ha | ha
  all_goals rcases abs_eq_one_cases z.b hb with hb | hb
  all_goals simp only [ha,hb,one_mul,neg_one_mul] at hp
  · exact unit_unit_affine_reachable_family z hz ha hb (by nlinarith [hp])
  · have hr : Reachable z (eps3 z) := ⟨[.s3],rfl⟩
    obtain ⟨x,y,hxy⟩ := unit_unit_affine_reachable_family (eps3 z)
      (reachable_preserves_solution hr hz)
      (by simp [eps3,ha]) (by simp [eps3,hb]) (by simp [eps3]; nlinarith [hp])
    exact ⟨x,y,reachable_trans hr hxy⟩
  · have hr : Reachable z (eps2 z) := ⟨[.s2],rfl⟩
    obtain ⟨x,y,hxy⟩ := unit_unit_affine_reachable_family (eps2 z)
      (reachable_preserves_solution hr hz)
      (by simp [eps2,ha]) (by simp [eps2,hb]) (by simp [eps2]; nlinarith [hp])
    exact ⟨x,y,reachable_trans hr hxy⟩
  · have hr : Reachable z (eps1 z) := ⟨[.s1],rfl⟩
    obtain ⟨x,y,hxy⟩ := unit_unit_affine_reachable_family (eps1 z)
      (reachable_preserves_solution hr hz)
      (by simp [eps1,ha]) (by simp [eps1,hb]) (by simpa only [eps1] using (show z.d=2 by nlinarith [hp]))
    exact ⟨x,y,reachable_trans hr hxy⟩

/-- The other affine-A₂ small triangle reaches the preceding affine pair by
one elementary braid. -/
theorem signed_three_unit_reachable_family (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hb : |z.b|=1) (hp : z.a*z.b*z.d=-1) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hr : Reachable z (mu1 z) := ⟨[.m1],rfl⟩
  have hwa : |(mu1 z).a|=1 := ha
  have hwd : |(mu1 z).d|=1 := hb
  have hwb : |(mu1 z).b|=2 := by
    rcases abs_eq_one_cases z.a ha with ha | ha
    all_goals rcases abs_eq_one_cases z.b hb with hb | hb
    all_goals simp only [ha,hb,one_mul,neg_one_mul] at hp
    all_goals have hd : z.d = -z.a*z.b := by simp only [ha,hb]; nlinarith [hp]
    all_goals simp [mu1,hd,ha,hb]
  let w := inv2 (mu1 z)
  have hrw : Reachable z w := ⟨[.m1,.i2],rfl⟩
  have hwa' : (w.a=2 ∧ w.b=w.d) ∨ (w.a=-2 ∧ w.b=-w.d) := by
    rcases abs_eq_one_cases z.a ha with ha | ha
    all_goals rcases abs_eq_one_cases z.b hb with hb | hb
    all_goals simp only [ha,hb,one_mul,neg_one_mul] at hp
    all_goals have hd : z.d = -z.a*z.b := by simp only [ha,hb]; nlinarith [hp]
    all_goals simp [w,inv2,mu1,hd,ha,hb]
  obtain ⟨x,y,hxy⟩ := signed_affine_edge_equal_reachable_family w
    (reachable_preserves_solution hrw hz)
    (hwa'.imp (fun h => ⟨h.1,Or.inl h.2⟩) (fun h => ⟨h.1,Or.inl h.2⟩))
  exact ⟨x,y,reachable_trans hrw hxy⟩

/-- A first triangle whose defect is exactly four and whose first two edges
are units has a complete family reduction. -/
theorem first_unit_triangle_defect_four (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hb : |z.b|=1)
    (hdef : cayleyDefect z.a z.b z.d=4) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have hasq : z.a^2=1 := by nlinarith [sq_abs z.a]
  have hbsq : z.b^2=1 := by nlinarith [sq_abs z.b]
  have hp : z.a*z.b*z.d=2 ∨ z.a*z.b*z.d=-1 := by
    unfold cayleyDefect at hdef
    have hs : (z.a*z.b*z.d)^2 = z.d^2 := by
      calc (z.a*z.b*z.d)^2 = z.a^2*z.b^2*z.d^2 := by ring
           _ = z.d^2 := by rw [hasq,hbsq]; ring
    have he : (z.a*z.b*z.d-2)*(z.a*z.b*z.d+1)=0 := by
      nlinarith [hdef,hasq,hbsq,hs]
    rcases mul_eq_zero.mp he with h | h
    · left
      nlinarith [h]
    · right
      nlinarith [h]
  rcases hp with hp | hp
  · exact signed_unit_unit_affine_reachable_family z hz ha hb hp
  · exact signed_three_unit_reachable_family z hz ha hb hp

/-- At an affine first edge, two unit neighbors give the signed equal-pair condition. -/
theorem first_affine_between_units_reachable_family (z : Six) (hz : isSolution z)
    (hb : |z.b|=1) (hd : |z.d|=1) (hp : z.a*z.b*z.d=2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  apply signed_affine_edge_equal_reachable_family z hz
  rcases abs_eq_one_cases z.b hb with hb | hb
  all_goals rcases abs_eq_one_cases z.d hd with hd | hd
  all_goals simp only [hb,hd,mul_one,mul_neg_one] at hp
  all_goals simp [hb,hd]
  all_goals omega

/-- An affine diagonal between two unit edges is moved to the first adjacent edge. -/
theorem unit_affine_unit_reachable_family (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hd : |z.d|=1) (hp : z.a*z.b*z.d=2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  let w := inv2 z
  have hr : Reachable z w := ⟨[.i2],rfl⟩
  apply Exists.elim (signed_affine_edge_equal_reachable_family w
    (reachable_preserves_solution hr hz) ?_)
  · rintro x ⟨y,hy⟩
    exact ⟨x,y,reachable_trans hr hy⟩
  · rcases abs_eq_one_cases z.a ha with ha | ha
    all_goals rcases abs_eq_one_cases z.d hd with hd | hd
    all_goals simp only [ha,hd,one_mul,neg_one_mul,mul_one,mul_neg_one] at hp
    all_goals simp only [w,inv2,ha,hd]
    all_goals omega

/-- Two of the three triangle pairings are units. -/
def HasTwoUnits (u v w : ℤ) : Prop :=
  (|u|=1 ∧ |v|=1) ∨ (|u|=1 ∧ |w|=1) ∨ (|v|=1 ∧ |w|=1)

private theorem unit_triangle_product (u v w : ℤ) (hu : |u|=1) (hv : |v|=1)
    (hdef : cayleyDefect u v w=4) : u*v*w=2 ∨ u*v*w=-1 := by
  have husq : u^2=1 := by nlinarith [sq_abs u]
  have hvsq : v^2=1 := by nlinarith [sq_abs v]
  have hs : (u*v*w)^2 = w^2 := by
    calc (u*v*w)^2 = u^2*v^2*w^2 := by ring
         _ = w^2 := by rw [husq,hvsq]; ring
  unfold cayleyDefect at hdef
  have he : (u*v*w-2)*(u*v*w+1)=0 := by nlinarith [hdef,husq,hvsq,hs]
  rcases mul_eq_zero.mp he with h | h
  · left
    nlinarith [h]
  · right
    nlinarith [h]

/-- Every orientation of a degenerate unit triangle gives a genuine family reduction. -/
theorem first_two_unit_triangle_defect_four (z : Six) (hz : isSolution z)
    (hu : HasTwoUnits z.a z.b z.d) (hdef : cayleyDefect z.a z.b z.d=4) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  rcases hu with ⟨ha,hb⟩ | ⟨ha,hd⟩ | ⟨hb,hd⟩
  · exact first_unit_triangle_defect_four z hz ha hb hdef
  · have hdef' : cayleyDefect z.a z.d z.b=4 := by
      unfold cayleyDefect at *
      nlinarith [hdef]
    have hp := unit_triangle_product z.a z.d z.b ha hd hdef'
    have hp' : z.a*z.b*z.d=2 ∨ z.a*z.b*z.d=-1 := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hp
    rcases hp' with hp' | hp'
    · exact unit_affine_unit_reachable_family z hz ha hd hp'
    · have hb : |z.b|=1 := by
        rcases abs_eq_one_cases z.a ha with ha | ha
        all_goals rcases abs_eq_one_cases z.d hd with hd | hd
        all_goals simp only [ha,hd,one_mul,neg_one_mul,mul_one,mul_neg_one] at hp'
        all_goals have hb : z.b=1 ∨ z.b=-1 := by omega
        all_goals rcases hb with hb | hb <;> simp [hb]
      exact signed_three_unit_reachable_family z hz ha hb hp'
  · have hdef' : cayleyDefect z.b z.d z.a=4 := by
      unfold cayleyDefect at *
      nlinarith [hdef]
    have hp := unit_triangle_product z.b z.d z.a hb hd hdef'
    have hp' : z.a*z.b*z.d=2 ∨ z.a*z.b*z.d=-1 := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hp
    rcases hp' with hp' | hp'
    · exact first_affine_between_units_reachable_family z hz hb hd hp'
    · have ha : |z.a|=1 := by
        rcases abs_eq_one_cases z.b hb with hb | hb
        all_goals rcases abs_eq_one_cases z.d hd with hd | hd
        all_goals simp only [hb,hd,mul_one,mul_neg_one] at hp'
        all_goals have ha : z.a=1 ∨ z.a=-1 := by omega
        all_goals rcases ha with ha | ha <;> simp [ha]
      exact signed_three_unit_reachable_family z hz ha hb hp'

/-- The four genuine triangles of the Euler pairing. -/
def UnitBoundaryTriangle (z : Six) : Prop :=
  (HasTwoUnits z.a z.b z.d ∧ cayleyDefect z.a z.b z.d=4) ∨
  (HasTwoUnits z.a z.c z.e ∧ cayleyDefect z.a z.c z.e=4) ∨
  (HasTwoUnits z.b z.c z.f ∧ cayleyDefect z.b z.c z.f=4) ∨
  (HasTwoUnits z.d z.e z.f ∧ cayleyDefect z.d z.e z.f=4)

/-- Any signed degenerate unit triangle, in any of the four positions, reduces
by actual authorized mutations to the family. -/
theorem unit_boundary_triangle_reachable_family (z : Six) (hz : isSolution z)
    (hu : UnitBoundaryTriangle z) : ∃ x y : ℤ, Reachable z (family x y) := by
  have transport (word : List Generator)
      (hw : HasTwoUnits (applyWord z word).a (applyWord z word).b (applyWord z word).d)
      (hdef : cayleyDefect (applyWord z word).a (applyWord z word).b
        (applyWord z word).d=4) : ∃ x y : ℤ, Reachable z (family x y) := by
    have hr : Reachable z (applyWord z word) := ⟨word,rfl⟩
    obtain ⟨x,y,hxy⟩ := first_two_unit_triangle_defect_four (applyWord z word)
      (reachable_preserves_solution hr hz) hw hdef
    exact ⟨x,y,reachable_trans hr hxy⟩
  rcases hu with ⟨hw,hdef⟩ | ⟨hw,hdef⟩ | ⟨hw,hdef⟩ | ⟨hw,hdef⟩
  · exact first_two_unit_triangle_defect_four z hz hw hdef
  · exact transport [.i3] hw hdef
  · exact transport [.i2,.i3] hw hdef
  · exact transport [.i1,.i2,.i3] hw hdef

open NegativeDescent NegativeTwoEdge

private theorem no_square_twenty (n : ℤ) : n^2 ≠ 20 := by
  intro hn
  have hb : -5 ≤ n ∧ n ≤ 5 := by
    constructor <;> nlinarith [sq_nonneg (n-5),sq_nonneg (n+5)]
  rcases hb with ⟨hlo,hhi⟩
  interval_cases n <;> norm_num at hn

/-- Exact quadratic and Pfaffian equations at the nondegenerate small triangle. -/
theorem bad_unit_triangle_equations (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=-2) :
    z.f^2-(3*z.c-2*z.e)*z.f+z.c^2-z.c*z.e+z.e^2=0 ∧
      (z.f-z.e-2*z.c=4 ∨ z.f-z.e-2*z.c=-4) := by
  constructor
  · have h := hz.1
    simp only [q1,ha,hb,hd,one_mul,one_pow] at h
    nlinarith [h]
  · have h : (z.f-z.e-2*z.c)^2=(4:ℤ)^2 := by
      have h := hz.2
      simp only [q2,ha,hb,hd,one_mul] at h
      nlinarith [h]
    exact eq_or_eq_neg_of_sq_eq_sq _ _ h

private theorem small_bad_unit_box (c e f : ℤ)
    (hc : 0 ≤ c ∧ c ≤ 2) (he : -4 ≤ e ∧ e ≤ 0) (hf : 0 ≤ f ∧ f ≤ 7)
    (hz : isSolution ⟨1,1,c,-2,e,f⟩) :
    ∃ word : List Generator, l1 (applyWord ⟨1,1,c,-2,e,f⟩ word) < l1 ⟨1,1,c,-2,e,f⟩ := by
  rcases hc with ⟨hc0,hc2⟩
  rcases he with ⟨he4,he0⟩
  rcases hf with ⟨hf0,hf7⟩
  interval_cases c <;> interval_cases e <;> interval_cases f <;>
    norm_num [isSolution,q1,q2] at hz
  all_goals first
    | exact ⟨[.m1,.i3],by decide⟩
    | exact ⟨[.i1,.m2],by decide⟩

private theorem small_positive_bad_unit_box (c e f : ℤ)
    (hc1 : 1≤c) (hc2 : c≤2) (he1 : 1≤e) (he2 : e≤2)
    (hf0 : -1≤f) (hf10 : f≤10) (hz : isSolution ⟨1,1,c,-2,e,f⟩) :
    FamilyOrDrop ⟨1,1,c,-2,e,f⟩ := by
  interval_cases c <;> interval_cases e <;> interval_cases f <;>
    norm_num [isSolution,q1,q2] at hz
  left
  exact unit_boundary_triangle_reachable_family _ (by norm_num [isSolution,q1,q2])
    (by norm_num [UnitBoundaryTriangle,HasTwoUnits,cayleyDefect])

private theorem bad_unit_c_zero (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=-2) (hc : z.c=0) : FamilyOrDrop z := by
  obtain ⟨hq,hk⟩ := bad_unit_triangle_equations z hz ha hb hd
  have hef : z.f=-z.e := by
    rw [hc] at hq
    nlinarith [sq_nonneg (z.f+z.e)]
  have he : z.e=2 ∨ z.e=-2 := by
    rw [hc,hef] at hk
    omega
  right
  refine ⟨[.m1,.i3],?_⟩
  rcases he with he | he
  all_goals have hz' : z=⟨1,1,0,-2,z.e,-z.e⟩ := by ext <;> simp [ha,hb,hc,hd,hef]
  all_goals rw [hz']
  all_goals simp only [he]
  all_goals decide

private theorem bad_unit_nonnegative_tail (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=-2) (hc : 0 ≤ z.c) (he : 0 ≤ z.e) :
    FamilyOrDrop z := by
  obtain ⟨hq,hk⟩ := bad_unit_triangle_equations z hz ha hb hd
  by_cases hc0 : z.c=0
  · exact bad_unit_c_zero z hz ha hb hd hc0
  by_cases he0 : z.e=0
  · have hfalse : False := by
      rcases hk with hk | hk
      · have hf : z.f=2*z.c+4 := by omega
        rw [hf,he0] at hq
        exact no_square_twenty (z.c-2) (by nlinarith [hq])
      · have hf : z.f=2*z.c-4 := by omega
        rw [hf,he0] at hq
        exact no_square_twenty (z.c+2) (by nlinarith [hq])
    exact hfalse.elim
  have hc1 : 1 ≤ z.c := by omega
  have he1 : 1 ≤ z.e := by omega
  by_cases hsum : z.c+z.e≤3
  · have hc2 : z.c≤2 := by omega
    have he2 : z.e≤2 := by omega
    have hz' : z=⟨1,1,z.c,-2,z.e,z.f⟩ := by ext <;> simp [ha,hb,hd]
    have hf0 : -1≤z.f := by rcases hk with hk | hk <;> omega
    have hf10 : z.f≤10 := by rcases hk with hk | hk <;> omega
    rw [hz'] at hz ⊢
    exact small_positive_bad_unit_box _ _ _ hc1 hc2 he1 he2 hf0 hf10 hz
  · have hf0 : 0 ≤ z.f := by rcases hk with hk | hk <;> omega
    have hcf : z.c-z.f≤0 := by rcases hk with hk | hk <;> omega
    have habs : |z.c-z.e|<z.c+z.e := abs_lt.mpr ⟨by omega,by omega⟩
    right
    refine ⟨[.m1,.m2],?_⟩
    rw [l1_lt_iff]
    change integerL1 (mu2 (mu1 z)) < integerL1 z
    simp [integerL1,mu2,mu1,ha,hb,hd,abs_of_nonneg hc,abs_of_nonneg he,
      abs_of_nonneg hf0,abs_of_nonpos hcf]
    omega

private theorem bad_unit_opposed_tail (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=-2) (hc : 0 ≤ z.c) (he : z.e<0) :
    FamilyOrDrop z := by
  obtain ⟨hq,hk⟩ := bad_unit_triangle_equations z hz ha hb hd
  let E : ℤ := -z.e
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hq' : z.f^2-(3*z.c+2*E)*z.f+z.c^2+z.c*E+E^2=0 := by
    dsimp [E]
    nlinarith [hq]
  have hk' : z.f+E-2*z.c=4 ∨ z.f+E-2*z.c=-4 := by
    simpa only [E,sub_neg_eq_add] using hk
  have hf : 0 < z.f := by
    by_contra h
    have hf0 : z.f≤0 := by omega
    have hprod : (3*z.c+2*E)*z.f≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) hf0
    nlinarith [hq',sq_nonneg z.f,sq_nonneg z.c,mul_nonneg hc (by omega : 0≤E)]
  by_cases hE1 : E=1
  · have hc2 : z.c≤2 := by
      rcases hk' with hk' | hk'
      · have hf' : z.f=2*z.c+3 := by omega
        rw [hE1,hf'] at hq'
        nlinarith [hq',sq_nonneg (z.c-2)]
      · have hf' : z.f=2*z.c-5 := by omega
        rw [hE1,hf'] at hq'
        have hc3 : z.c≤3 := by nlinarith [hq',sq_nonneg (z.c-3)]
        interval_cases z.c <;> norm_num at hq'
    have hf7 : z.f≤7 := by rcases hk' with hk' | hk' <;> omega
    have hz' : z=⟨1,1,z.c,-2,z.e,z.f⟩ := by ext <;> simp [ha,hb,hd]
    right
    rw [hz'] at hz ⊢
    exact small_bad_unit_box _ _ _ ⟨hc,hc2⟩ (by dsimp [E] at hE1; omega)
      ⟨by omega,hf7⟩ hz
  have hE2 : 2≤E := by omega
  by_cases hfE : E<z.f
  · have hfE2 : E+2≤z.f := by rcases hk' with hk' | hk' <;> omega
    have habs : |2*E-z.f|<z.f-2 := abs_lt.mpr ⟨by omega,by omega⟩
    right
    refine ⟨[.m2],?_⟩
    change l1 (mu2 z)<l1 z
    apply (mu2_drop_iff z).mpr
    rw [ha,hb,hd,abs_of_pos hf]
    have hm : -2*z.e-z.f=2*E-z.f := by dsimp [E]; ring
    rw [hm]
    change |(1:ℤ)*(-2)-1|+|2*E-z.f|< |1|+z.f
    norm_num
    omega
  have hfE' : z.f≤E := by omega
  by_cases hfc : z.f<2*z.c
  · have h1 : |z.f-z.c|<z.c := abs_lt.mpr ⟨by omega,by omega⟩
    have h2 : |E-2*z.f|≤E := abs_le.mpr ⟨by omega,by omega⟩
    right
    refine ⟨[.m3],?_⟩
    change l1 (mu3 z)<l1 z
    apply (mu3_drop_iff z).mpr
    rw [hb,hd,abs_of_nonneg hc,abs_of_neg he]
    have hm : z.f*(-2)-z.e=E-2*z.f := by dsimp [E]; ring
    rw [mul_one,hm]
    change |z.f-z.c|+|E-2*z.f|<z.c+E
    omega
  · have hE4 : E≤4 := by rcases hk' with hk' | hk' <;> omega
    have hc2 : z.c≤2 := by omega
    have hf7 : z.f≤7 := by omega
    have hz' : z=⟨1,1,z.c,-2,z.e,z.f⟩ := by ext <;> simp [ha,hb,hd]
    right
    rw [hz'] at hz ⊢
    exact small_bad_unit_box _ _ _ ⟨hc,hc2⟩ (by dsimp [E] at hE hE4; omega)
      ⟨by omega,hf7⟩ hz

/-- The signed `(1,1,-2)` triangle admits a complete, unconditional finite-word
family-or-strict-height reduction, with the other three coordinates arbitrary. -/
theorem bad_unit_triangle_family_or_drop (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : z.d=-2) : FamilyOrDrop z := by
  have normalized (w : Six) (hw : isSolution w) (hwa : w.a=1) (hwb : w.b=1)
      (hwd : w.d=-2) (hwc : 0≤w.c) : FamilyOrDrop w := by
    by_cases he : 0≤w.e
    · exact bad_unit_nonnegative_tail w hw hwa hwb hwd hwc he
    · exact bad_unit_opposed_tail w hw hwa hwb hwd hwc (by omega)
  by_cases hc : 0≤z.c
  · exact normalized z hz ha hb hd hc
  · have hr : Reachable z (eps4 z) := ⟨[.s4],rfl⟩
    have h := normalized (eps4 z) (reachable_preserves_solution hr hz)
      (by simpa [eps4] using ha) (by simpa [eps4] using hb)
      (by simpa [eps4] using hd) (by simp [eps4]; omega)
    rcases h with ⟨x,y,hxy⟩ | ⟨word,hword⟩
    · exact Or.inl ⟨x,y,reachable_trans hr hxy⟩
    · right
      exact ⟨.s4::word,by simpa only [applyWord,step,l1_eps4] using hword⟩

/-- Finite family-or-height reductions transport along an actual path preserving height. -/
theorem familyOrDrop_of_reachable_same_height {z w : Six} (hr : Reachable z w)
    (hheight : l1 w=l1 z) (h : FamilyOrDrop w) : FamilyOrDrop z := by
  rcases h with ⟨x,y,hxy⟩ | ⟨word,hword⟩
  · exact Or.inl ⟨x,y,reachable_trans hr hxy⟩
  · right
    obtain ⟨initialWord,hprefix⟩ := hr
    refine ⟨initialWord++word,?_⟩
    rw [applyWord_append,hprefix,←hheight]
    exact hword

private theorem normalized_two_units_small_third (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hb : z.b=1) (hd : |z.d|≤2)
    (htri : 4≤cayleyDefect z.a z.b z.d) : FamilyOrDrop z := by
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hd
  have hdcase : z.d=-2 ∨ z.d=-1 ∨ z.d=0 ∨ z.d=1 ∨ z.d=2 := by omega
  rcases hdcase with hdz | hdz | hdz | hdz | hdz
  · exact bad_unit_triangle_family_or_drop z hz ha hb hdz
  · left
    apply signed_three_unit_reachable_family z hz
    · simp [ha]
    · simp [hb]
    · simp [ha,hb,hdz]
  · norm_num [cayleyDefect,ha,hb,hdz] at htri
  · norm_num [cayleyDefect,ha,hb,hdz] at htri
  · exact Or.inl (unit_unit_affine_reachable_family z hz ha hb hdz)

/-- Two unit edges at the first triangle, with its third edge of absolute value
at most two, admit a complete genuine family-or-height reduction on the negative side. -/
theorem two_units_small_third_family_or_drop (z : Six) (hz : isSolution z)
    (ha : |z.a|=1) (hb : |z.b|=1) (hd : |z.d|≤2)
    (htri : 4≤cayleyDefect z.a z.b z.d) : FamilyOrDrop z := by
  rcases abs_eq_one_cases z.a ha with ha | ha
  all_goals rcases abs_eq_one_cases z.b hb with hb | hb
  · exact normalized_two_units_small_third z hz ha hb hd htri
  · have hr : Reachable z (eps3 z) := ⟨[.s3],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (l1_eps3 z)
    apply normalized_two_units_small_third (eps3 z) (reachable_preserves_solution hr hz)
    · simp [eps3,ha]
    · simp [eps3,hb]
    · simpa [eps3] using hd
    · simpa [eps3,cayleyDefect,ha,hb] using htri
  · have hr : Reachable z (eps2 z) := ⟨[.s2],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (l1_eps2 z)
    apply normalized_two_units_small_third (eps2 z) (reachable_preserves_solution hr hz)
    · simp [eps2,ha]
    · simp [eps2,hb]
    · simpa [eps2] using hd
    · simpa [eps2,cayleyDefect,ha,hb] using htri
  · have hr : Reachable z (eps1 z) := ⟨[.s1],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (by simp [l1,eps1])
    apply normalized_two_units_small_third (eps1 z) (reachable_preserves_solution hr hz)
    · simp [eps1,ha]
    · simp [eps1,hb]
    · simpa [eps1] using hd
    · simpa [eps1,cayleyDefect,ha,hb] using htri

theorem negative_two_units_small_third_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0)
    (ha : |z.a|=1) (hb : |z.b|=1) (hd : |z.d|≤2) : FamilyOrDrop z :=
  two_units_small_third_family_or_drop z hz ha hb hd
    (negative_triangle_inequalities z hz hneg).1

end SerreMarkov.NegativeUnitSmall
