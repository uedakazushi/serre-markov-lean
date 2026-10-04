import SerreMarkov.AffineTriangles

/-! # Orthogonal pairs with opposite affine edge

If the first coefficient is zero and the opposite edge has absolute value
two, the solution equations force an affine triangle. No intrinsic sign
assumption or bound on the remaining coefficients is needed.
-/

namespace SerreMarkov.NegativeZeroAffineBoundary
open AffineTriangles

private theorem sum_squares_four_has_zero (u v : ℤ) (h : u^2+v^2=4) :
    u=0 ∨ v=0 := by
  have hu : -2≤u ∧ u≤2 := by
    constructor
    · by_contra hn
      have hh : u≤-3 := by omega
      nlinarith [sq_nonneg (u+3),sq_nonneg v]
    · by_contra hn
      have hh : 3≤u := by omega
      nlinarith [sq_nonneg (u-3),sq_nonneg v]
  have hv : -2≤v ∧ v≤2 := by
    constructor
    · by_contra hn
      have hh : v≤-3 := by omega
      nlinarith [sq_nonneg (v+3),sq_nonneg u]
    · by_contra hn
      have hh : 3≤v := by omega
      nlinarith [sq_nonneg (v-3),sq_nonneg u]
  obtain ⟨hulo,huhi⟩ := hu
  obtain ⟨hvlo,hvhi⟩ := hv
  interval_cases u <;> interval_cases v <;> first | omega | norm_num at h

private theorem abs_two_of_square (u : ℤ) (h : u^2=4) : |u|=2 := by
  have hp : (u-2)*(u+2)=0 := by nlinarith [h]
  rcases mul_eq_zero.mp hp with hp | hp
  · have hu : u=2 := by omega
    simp [hu]
  · have hu : u=-2 := by omega
    simp [hu]

theorem zero_positive_affine_triangle (b c d e : ℤ)
    (hz : isSolution ⟨0,b,c,d,e,2⟩) : HasAffineTriangle ⟨0,b,c,d,e,2⟩ := by
  have hq1 := hz.1
  have hq2 := hz.2
  simp only [q1,q2,zero_mul,zero_sub] at hq1 hq2
  have hs : (b-c)^2+(d-e)^2=4 := by nlinarith [hq1]
  rcases sum_squares_four_has_zero (b-c) (d-e) hs with hbc | hde
  · have hc : c=b := by omega
    subst c
    have hd : (d-e)^2=4 := by nlinarith [hs]
    have hp : b^2*(d-e)^2=16 := by nlinarith [hq2]
    have hb : b^2=4 := by nlinarith [hp,hd]
    exact Or.inr (Or.inr (Or.inl ⟨abs_two_of_square b hb,abs_two_of_square b hb,
      by norm_num,by nlinarith [hb]⟩))
  · have he : e=d := by omega
    subst e
    have hb : (b-c)^2=4 := by nlinarith [hs]
    have hp : d^2*(b-c)^2=16 := by nlinarith [hq2]
    have hd : d^2=4 := by nlinarith [hp,hb]
    exact Or.inr (Or.inr (Or.inr ⟨abs_two_of_square d hd,abs_two_of_square d hd,
      by norm_num,by nlinarith [hd]⟩))

theorem zero_opposite_affine_reachable_family (z : Six) (hz : isSolution z)
    (ha : z.a=0) (hf : |z.f|=2) : ∃ x y : ℤ, Reachable z (family x y) := by
  rcases (abs_eq (by norm_num : (0:ℤ)≤2)).mp hf with hf | hf
  · have ht : z=⟨0,z.b,z.c,z.d,z.e,2⟩ := by ext <;> simp [ha,hf]
    rw [ht] at hz ⊢
    exact affine_triangle_reachable_family _ hz (zero_positive_affine_triangle _ _ _ _ hz)
  · have hr : Reachable z (eps4 z) := ⟨[.s4],rfl⟩
    have ht : eps4 z=⟨0,z.b,-z.c,z.d,-z.e,2⟩ := by ext <;> simp [eps4,ha,hf]
    have hw : isSolution ⟨0,z.b,-z.c,z.d,-z.e,2⟩ := ht ▸ reachable_preserves_solution hr hz
    obtain ⟨x,y,hxy⟩ := affine_triangle_reachable_family _ hw
      (zero_positive_affine_triangle _ _ _ _ hw)
    exact ⟨x,y,reachable_trans hr (by simpa only [ht] using hxy)⟩

end SerreMarkov.NegativeZeroAffineBoundary
