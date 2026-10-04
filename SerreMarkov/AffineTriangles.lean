import SerreMarkov.NegativeBoundary

/-! # Signed affine triangles in all four positions

An actual pairing triangle with three edges of absolute value two and
positive product always reduces to the family by authorized finite words.
The other three coefficients are arbitrary integers.
-/

namespace SerreMarkov.AffineTriangles
open NegativeBoundary

def AffineTriangle (u v w : ℤ) : Prop :=
  |u|=2 ∧ |v|=2 ∧ |w|=2 ∧ u*v*w=8

def HasAffineTriangle (z : Six) : Prop :=
  AffineTriangle z.a z.b z.d ∨ AffineTriangle z.a z.c z.e ∨
  AffineTriangle z.b z.c z.f ∨ AffineTriangle z.d z.e z.f

theorem first_affine_triangle_reachable_family (z : Six) (hz : isSolution z)
    (haff : AffineTriangle z.a z.b z.d) : ∃ x y : ℤ, Reachable z (family x y) := by
  obtain ⟨ha,hb,_,hp⟩ := haff
  have transport (word : List Generator)
      (hwa : (applyWord z word).a=2) (hwb : (applyWord z word).b=2)
      (hwd : (applyWord z word).d=2) : ∃ x y : ℤ, Reachable z (family x y) := by
    have hr : Reachable z (applyWord z word) := ⟨word,rfl⟩
    have ht : applyWord z word=⟨2,2,(applyWord z word).c,2,
        (applyWord z word).e,(applyWord z word).f⟩ := by
      apply Six.ext
      · exact hwa
      · exact hwb
      · rfl
      · exact hwd
      · rfl
      · rfl
    obtain ⟨x,y,hxy⟩ := triangle_two_reachable_family _ _ _
      (ht ▸ reachable_preserves_solution hr hz)
    exact ⟨x,y,reachable_trans hr (ht.symm ▸ hxy)⟩
  rcases (abs_eq (by norm_num : (0:ℤ)≤2)).mp ha with ha | ha
  all_goals rcases (abs_eq (by norm_num : (0:ℤ)≤2)).mp hb with hb | hb
  · have hd : z.d=2 := by rw [ha,hb] at hp; nlinarith [hp]
    exact transport [] (by simpa using ha) (by simpa using hb) (by simpa using hd)
  · have hd : z.d=-2 := by rw [ha,hb] at hp; nlinarith [hp]
    exact transport [.s3] (by simp [applyWord,step,eps3,ha])
      (by simp [applyWord,step,eps3,hb]) (by simp [applyWord,step,eps3,hd])
  · have hd : z.d=-2 := by rw [ha,hb] at hp; nlinarith [hp]
    exact transport [.s2] (by simp [applyWord,step,eps2,ha])
      (by simp [applyWord,step,eps2,hb]) (by simp [applyWord,step,eps2,hd])
  · have hd : z.d=2 := by rw [ha,hb] at hp; nlinarith [hp]
    exact transport [.s1] (by simp [applyWord,step,eps1,ha])
      (by simp [applyWord,step,eps1,hb]) (by simp [applyWord,step,eps1,hd])

theorem affine_triangle_reachable_family (z : Six) (hz : isSolution z)
    (haff : HasAffineTriangle z) : ∃ x y : ℤ, Reachable z (family x y) := by
  have transport (word : List Generator)
      (hw : AffineTriangle (applyWord z word).a (applyWord z word).b
        (applyWord z word).d) : ∃ x y : ℤ, Reachable z (family x y) := by
    have hr : Reachable z (applyWord z word) := ⟨word,rfl⟩
    obtain ⟨x,y,hxy⟩ := first_affine_triangle_reachable_family _
      (reachable_preserves_solution hr hz) hw
    exact ⟨x,y,reachable_trans hr hxy⟩
  rcases haff with h | h | h | h
  · exact first_affine_triangle_reachable_family z hz h
  · exact transport [.i3] (by simpa [applyWord,step,inv3] using h)
  · exact transport [.i2,.i3] (by simpa [applyWord,step,inv2,inv3] using h)
  · exact transport [.i1,.i2,.i3] (by simpa [applyWord,step,inv1,inv2,inv3] using h)

end SerreMarkov.AffineTriangles
