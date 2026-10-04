import SerreMarkov.NegativeUnitSmall

/-! # Complete small reduction at the opposite adjacent unit edges

A universal positive sum of squares bounds all other coefficients. The entire
resulting finite box is verified in the kernel; its alternatives are genuine
family reductions or actual single-braid height drops.
-/

namespace SerreMarkov.NegativeEndpointUnits

open NegativeDescent NegativeTwoEdge NegativeUnitSmall

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The endpoint-unit specialization of the first solution equation is positive definite. -/
theorem endpoint_unit_sum_squares (b c d e : ℤ) :
    4*(q1 ⟨1,b,c,d,e,1⟩-2)=
      2*(b-e)^2+(c-d)^2+2*(b+e-c-d)^2+(c+d)^2 := by
  dsimp [q1]
  ring

private theorem square_bounds_three (x : ℤ) (hx : x^2≤12) : -3≤x ∧ x≤3 := by
  constructor <;> nlinarith [sq_nonneg (x-3),sq_nonneg (x+3)]

private theorem square_bounds_four (x : ℤ) (hx : x^2≤24) : -4≤x ∧ x≤4 := by
  constructor <;> nlinarith [sq_nonneg (x-4),sq_nonneg (x+4)]

/-- No bound on the input coordinates is assumed: the equation itself proves the box. -/
theorem endpoint_unit_coordinate_bounds (z : Six) (hz : isSolution z)
    (ha : z.a=1) (hf : z.f=1) :
    (-5≤z.b ∧ z.b≤5) ∧ (-4≤z.c ∧ z.c≤4) ∧
      (-4≤z.d ∧ z.d≤4) ∧ (-5≤z.e ∧ z.e≤5) := by
  have hz' : z=⟨1,z.b,z.c,z.d,z.e,1⟩ := by ext <;> simp [ha,hf]
  have hq := hz.1
  rw [hz'] at hq
  have hs := endpoint_unit_sum_squares z.b z.c z.d z.e
  rw [hq] at hs
  have hB := square_bounds_three (z.b-z.e) (by
    nlinarith [sq_nonneg (z.c-z.d),sq_nonneg (z.b+z.e-z.c-z.d),sq_nonneg (z.c+z.d)])
  have hC := square_bounds_four (z.c-z.d) (by
    nlinarith [sq_nonneg (z.b-z.e),sq_nonneg (z.b+z.e-z.c-z.d),sq_nonneg (z.c+z.d)])
  have hW := square_bounds_three (z.b+z.e-z.c-z.d) (by
    nlinarith [sq_nonneg (z.b-z.e),sq_nonneg (z.c-z.d),sq_nonneg (z.c+z.d)])
  have hV := square_bounds_four (z.c+z.d) (by
    nlinarith [sq_nonneg (z.b-z.e),sq_nonneg (z.c-z.d),sq_nonneg (z.b+z.e-z.c-z.d)])
  omega

private def boxTuple (i : Fin 11) (j k : Fin 9) (l : Fin 11) : Six :=
  ⟨1,(i.val:ℤ)-5,(j.val:ℤ)-4,(k.val:ℤ)-4,(l.val:ℤ)-5,1⟩

local instance solutionDecidable (z : Six) : Decidable (isSolution z) := by
  unfold isSolution
  infer_instance
local instance triangleDecidable (z : Six) : Decidable (UnitBoundaryTriangle z) := by
  unfold UnitBoundaryTriangle HasTwoUnits
  infer_instance
local instance dropDecidable (z : Six) : Decidable (OneStepDrop z) := by
  unfold OneStepDrop
  infer_instance

/-- This checks every tuple in the proved box, not only preselected examples. -/
private theorem every_box_checked (i : Fin 11) : ∀ (j k : Fin 9) (l : Fin 11),
    isSolution (boxTuple i j k l) → IntrinsicSigns.thirdMinorSum (boxTuple i j k l)<0 →
      UnitBoundaryTriangle (boxTuple i j k l) ∨ OneStepDrop (boxTuple i j k l) := by
  fin_cases i <;> decide +kernel

private theorem endpoint_unit_alternatives (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (hf : z.f=1) :
    UnitBoundaryTriangle z ∨ OneStepDrop z := by
  obtain ⟨⟨hb0,hb5⟩,⟨hc0,hc4⟩,⟨hd0,hd4⟩,⟨he0,he5⟩⟩ :=
    endpoint_unit_coordinate_bounds z hz ha hf
  let i : Fin 11 := ⟨(z.b+5).toNat,by omega⟩
  let j : Fin 9 := ⟨(z.c+4).toNat,by omega⟩
  let k : Fin 9 := ⟨(z.d+4).toNat,by omega⟩
  let l : Fin 11 := ⟨(z.e+5).toNat,by omega⟩
  have heq : boxTuple i j k l=z := by
    ext <;> simp only [boxTuple,i,j,k,l]
    · exact ha.symm
    · omega
    · omega
    · omega
    · omega
    · exact hf.symm
  have h := every_box_checked i j k l
  rw [heq] at h
  exact h hz hneg

private theorem familyOrDrop_of_oneStepDrop (z : Six) (h : OneStepDrop z) : FamilyOrDrop z := by
  right
  rcases h with h | h | h | h | h | h
  · exact ⟨[.m1],h⟩
  · exact ⟨[.i1],h⟩
  · exact ⟨[.m2],h⟩
  · exact ⟨[.i2],h⟩
  · exact ⟨[.m3],h⟩
  · exact ⟨[.i3],h⟩

/-- The positive endpoint-unit branch is completely reduced without any classification premise. -/
theorem endpoint_units_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : z.a=1) (hf : z.f=1) :
    FamilyOrDrop z := by
  rcases endpoint_unit_alternatives z hz hneg ha hf with ht | hd
  · exact Or.inl (unit_boundary_triangle_reachable_family z hz ht)
  · exact familyOrDrop_of_oneStepDrop z hd

private theorem negative_eps2 (z : Six) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    IntrinsicSigns.thirdMinorSum (eps2 z)<0 := by
  change negativeMarker (eps2 z)<0
  rw [marker_eps2]
  exact hneg
private theorem negative_eps3 (z : Six) (hneg : IntrinsicSigns.thirdMinorSum z<0) :
    IntrinsicSigns.thirdMinorSum (eps3 z)<0 := by
  change negativeMarker (eps3 z)<0
  rw [marker_eps3]
  exact hneg

/-- Both opposite adjacent edges may have either unit sign. -/
theorem signed_endpoint_units_family_or_drop (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z<0) (ha : |z.a|=1) (hf : |z.f|=1) :
    FamilyOrDrop z := by
  have normalized_a (w : Six) (hw : isSolution w) (hwn : IntrinsicSigns.thirdMinorSum w<0)
      (hwa : w.a=1) (hwf : |w.f|=1) : FamilyOrDrop w := by
    have hfcase : w.f=1 ∨ w.f=-1 := (abs_eq (by norm_num : (0:ℤ)≤1)).mp hwf
    rcases hfcase with hwf | hwf
    · exact endpoint_units_family_or_drop w hw hwn hwa hwf
    · have hr : Reachable w (eps3 w) := ⟨[.s3],rfl⟩
      apply familyOrDrop_of_reachable_same_height hr (l1_eps3 w)
      exact endpoint_units_family_or_drop (eps3 w) (reachable_preserves_solution hr hw)
        (negative_eps3 w hwn) (by simpa [eps3] using hwa) (by simp [eps3,hwf])
  have hacase : z.a=1 ∨ z.a=-1 := (abs_eq (by norm_num : (0:ℤ)≤1)).mp ha
  rcases hacase with ha | ha
  · exact normalized_a z hz hneg ha hf
  · have hr : Reachable z (eps2 z) := ⟨[.s2],rfl⟩
    apply familyOrDrop_of_reachable_same_height hr (l1_eps2 z)
    exact normalized_a (eps2 z) (reachable_preserves_solution hr hz)
      (negative_eps2 z hneg) (by simp [eps2,ha]) (by simpa [eps2] using hf)

end SerreMarkov.NegativeEndpointUnits
