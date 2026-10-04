import SerreMarkov.Mutations

/-! # Complete reduction of the two-Kronecker slice

The positive Pfaffian component reduces by two integral translations to the
eight residues of Appendix B. The words at those residues are kernel checked.
This proves a global statement about the slice, not a bounded search.
-/

namespace SerreMarkov

theorem kroneckerPlus_down_u (u v B : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus (u-4) v (B-v)) := by
  have h := kroneckerPlus_translation_u_reachable (u-4) v (B-v)
  have heq : kroneckerPlus (u-4+4) v (B-v+v)=kroneckerPlus u v B := by
    congr 1 <;> ring
  rw [heq] at h
  exact reachable_symm h

theorem kroneckerPlus_down_v (u v B : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus u (v-4) (B-u)) := by
  have h := kroneckerPlus_translation_v_reachable u (v-4) (B-u)
  have heq : kroneckerPlus u (v-4+4) (B-u+u)=kroneckerPlus u v B := by
    congr 1 <;> ring
  rw [heq] at h
  exact reachable_symm h

theorem kroneckerPlus_shift_u (u v B n : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus (u+4*n) v (B+n*v)) := by
  induction n using Int.induction_on with
  | zero => simpa using reachable_refl (kroneckerPlus u v B)
  | succ n ih =>
    have h := reachable_trans ih
      (kroneckerPlus_translation_u_reachable (u+4*(n:ℤ)) v (B+(n:ℤ)*v))
    have heq : kroneckerPlus (u+4*(n:ℤ)+4) v (B+(n:ℤ)*v+v)=
        kroneckerPlus (u+4*((n:ℤ)+1)) v (B+((n:ℤ)+1)*v) := by
      congr 1 <;> ring
    rw [heq] at h
    exact h
  | pred n ih =>
    have h := reachable_trans ih
      (kroneckerPlus_down_u (u+4*(-(n:ℤ))) v (B+(-(n:ℤ))*v))
    have heq : kroneckerPlus (u+4*(-(n:ℤ))-4) v (B+(-(n:ℤ))*v-v)=
        kroneckerPlus (u+4*(-(n:ℤ)-1)) v (B+(-(n:ℤ)-1)*v) := by
      congr 1 <;> ring
    rw [heq] at h
    exact h

theorem kroneckerPlus_shift_v (u v B n : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus u (v+4*n) (B+n*u)) := by
  induction n using Int.induction_on with
  | zero => simpa using reachable_refl (kroneckerPlus u v B)
  | succ n ih =>
    have h := reachable_trans ih
      (kroneckerPlus_translation_v_reachable u (v+4*(n:ℤ)) (B+(n:ℤ)*u))
    have heq : kroneckerPlus u (v+4*(n:ℤ)+4) (B+(n:ℤ)*u+u)=
        kroneckerPlus u (v+4*((n:ℤ)+1)) (B+((n:ℤ)+1)*u) := by
      congr 1 <;> ring
    rw [heq] at h
    exact h
  | pred n ih =>
    have h := reachable_trans ih
      (kroneckerPlus_down_v u (v+4*(-(n:ℤ))) (B+(-(n:ℤ))*u))
    have heq : kroneckerPlus u (v+4*(-(n:ℤ))-4) (B+(-(n:ℤ))*u-u)=
        kroneckerPlus u (v+4*(-(n:ℤ)-1)) (B+(-(n:ℤ)-1)*u) := by
      congr 1 <;> ring
    rw [heq] at h
    exact h

theorem kroneckerPlus_reduce_mod (u v B : ℤ) (hB : 4*B=u*v+8) :
    ∃ B' : ℤ, 4*B'=(u%4)*(v%4)+8 ∧
      Reachable (kroneckerPlus u v B) (kroneckerPlus (u%4) (v%4) B') := by
  let B1 := B+(-(u/4))*v
  let B2 := B1+(-(v/4))*(u%4)
  have hu : u+4*(-(u/4))=u%4 := by
    have hd := Int.emod_add_mul_ediv u 4
    omega
  have hv : v+4*(-(v/4))=v%4 := by
    have hd := Int.emod_add_mul_ediv v 4
    omega
  have h1 := kroneckerPlus_shift_u u v B (-(u/4))
  rw [hu] at h1
  have h2 := kroneckerPlus_shift_v (u%4) v B1 (-(v/4))
  rw [hv] at h2
  have hB1 : 4*B1=(u%4)*v+8 := by
    dsimp [B1]
    rw [← hu]
    nlinarith [hB]
  refine ⟨B2, ?_, reachable_trans h1 h2⟩
  dsimp [B2]
  rw [← hv]
  nlinarith [hB1]

theorem kroneckerPlus_residue_family (u v B : ℤ)
    (hu0 : 0≤u) (hu4 : u<4) (hv0 : 0≤v) (hv4 : v<4)
    (hB : 4*B=u*v+8) :
    ∃ x y : ℤ, Reachable (kroneckerPlus u v B) (family x y) := by
  interval_cases u <;> interval_cases v <;> norm_num at hB <;> try omega
  all_goals have hBval : B=2 ∨ B=3 := by omega
  all_goals rcases hBval with hBval | hBval <;> subst B <;> norm_num at hB
  · exact ⟨2,2,[.m1,.s4],kronecker_plus_certificate_00⟩
  · exact ⟨1,-2,[.m1,.m2,.m2,.m2,.i3,.s2,.s3,.s4],kronecker_plus_certificate_01⟩
  · exact ⟨0,2,[.m1,.m2,.i3,.s4],kronecker_plus_certificate_02⟩
  · exact ⟨1,-2,[.m1,.m2,.i3,.i3,.i3,.s2,.s3,.s4],kronecker_plus_certificate_03⟩
  · exact ⟨2,-1,[.i2,.m1,.m1,.m1,.s2],kronecker_plus_certificate_10⟩
  · exact ⟨2,0,[.i2,.m1,.s2],kronecker_plus_certificate_20⟩
  · exact ⟨1,-3,[.m2,.i1,.i3,.s3],kronecker_plus_certificate_22⟩
  · exact ⟨2,-1,[.i2,.i2,.i2,.m1,.s2],kronecker_plus_certificate_30⟩

theorem kroneckerPlus_reachable_family (u v B : ℤ) (hB : 4*B=u*v+8) :
    ∃ x y : ℤ, Reachable (kroneckerPlus u v B) (family x y) := by
  obtain ⟨B', hB', h⟩ := kroneckerPlus_reduce_mod u v B hB
  obtain ⟨x,y,h'⟩ := kroneckerPlus_residue_family (u%4) (v%4) B'
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega))
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega)) hB'
  exact ⟨x,y,reachable_trans h h'⟩

theorem kronecker_plus_sum4_reachable_family (b c d e : ℤ)
    (h2 : q2 ⟨-2,b,c,d,e,2⟩=4) (hsum : b-c+d-e=4) :
    ∃ x y : ℤ, Reachable ⟨-2,b,c,d,e,2⟩ (family x y) := by
  have he : e=b-c+d-4 := by omega
  have hB : 4*b=(b-c)*(b+d)+8 := by
    rw [kronecker_q2, he] at h2
    nlinarith [h2]
  have hq : (⟨-2,b,c,d,e,2⟩:Six)=kroneckerPlus (b-c) (b+d) b := by
    ext <;> simp [kroneckerPlus, he]
    ring
  rw [hq]
  exact kroneckerPlus_reachable_family (b-c) (b+d) b hB

/-- Both Pfaffian-positive components of the Kronecker slice reach the family. -/
theorem kronecker_plus_reachable_family (b c d e : ℤ)
    (h1 : q1 ⟨-2,b,c,d,e,2⟩=8) (h2 : q2 ⟨-2,b,c,d,e,2⟩=4) :
    ∃ x y : ℤ, Reachable ⟨-2,b,c,d,e,2⟩ (family x y) := by
  obtain ⟨_, hsum | hsum⟩ := kronecker_plus_components b c d e h1 h2
  · exact kronecker_plus_sum4_reachable_family b c d e h2 hsum
  · have hsign : applyWord ⟨-2,b,c,d,e,2⟩ [.s1,.s2]=⟨-2,-b,-c,-d,-e,2⟩ := by
      ext <;> simp [applyWord, step, eps1, eps2]
    have h2' : q2 ⟨-2,-b,-c,-d,-e,2⟩=4 := by
      simpa [q2] using h2
    have hsum' : -b-(-c)+(-d)-(-e)=4 := by omega
    obtain ⟨x,y,h⟩ := kronecker_plus_sum4_reachable_family (-b) (-c) (-d) (-e) h2' hsum'
    exact ⟨x,y,reachable_trans ⟨[.s1,.s2],hsign⟩ h⟩

/-- The full two-Kronecker slice reduces, with no coefficient bound. -/
theorem kronecker_slice_reachable_family (b c d e : ℤ)
    (h1 : q1 ⟨-2,b,c,d,e,2⟩=8) (h2 : q2 ⟨-2,b,c,d,e,2⟩^2=16) :
    ∃ x y : ℤ, Reachable ⟨-2,b,c,d,e,2⟩ (family x y) := by
  have hf : (q2 ⟨-2,b,c,d,e,2⟩-4)*(q2 ⟨-2,b,c,d,e,2⟩+4)=0 := by nlinarith
  rcases mul_eq_zero.mp hf with hp | hn
  · exact kronecker_plus_reachable_family b c d e h1 (by omega)
  · exact kronecker_minus_reachable_family b c d e h1 (by omega)

end SerreMarkov
