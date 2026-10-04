import SerreMarkov.IntrinsicUnique
import SerreMarkov.IntrinsicSigns

/-! # Explicit intrinsic parameters of the regular family

The vectors printed in Section 5 form an actual primitive Serre frame.
Consequently every primitive frame of the positive-total family has `A=-1`
and `κ=m`, rather than merely matching these values in one selected basis.
-/

namespace SerreMarkov.FamilyIntrinsic

open Matrix IntrinsicFrame IntrinsicUnique
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply
set_option maxHeartbeats 3000000

def p : IntVec4 := ![0,-1,1,0]
def l : IntVec4 := ![1,0,0,1]
def u (y : ℤ) : IntVec4 := ![-y,1,0,0]
def v : IntVec4 := ![-1,0,0,0]

theorem rank_formula (m y : ℤ) (x : IntVec4) :
    chiVec (family (m-y) y) x p = x 1+x 2 := by
  simp [chiVec,gram,family,p,Matrix.mulVec,dotProduct,Fin.sum_univ_four]

theorem degree_formula (m y : ℤ) (x : IntVec4) :
    chiVec (family (m-y) y) x l = -x 0-y*(x 1+x 2)+x 3 := by
  simp [chiVec,gram,family,l,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  ring

theorem square_action (m y : ℤ) (x : IntVec4) :
    (shiftedSerre (family (m-y) y)^2) *ᵥ x =
      ![2*m*(x 1+x 2),
        2*m*(-x 0-y*(x 1+x 2)+x 3)-m^2*(x 1+x 2),
        -2*m*(-x 0-y*(x 1+x 2)+x 3)+m^2*(x 1+x 2),
        2*m*(x 1+x 2)] := by
  rw [family_shiftedSerre]
  ext i
  fin_cases i <;> simp [pow_two,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_four] <;> ring

private theorem first_kernel (m y : ℤ) (hm : 0 < m) (x : IntVec4)
    (hx : shiftedSerre (family (m-y) y) *ᵥ x = 0) :
    x 0 = 0 ∧ x 3 = 0 ∧ x 1+x 2 = 0 := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h3 := congrFun hx 3
  rw [family_shiftedSerre] at h0 h1 h3
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four] at h0 h1 h3
  have hrprod : m*(x 1+x 2) = 0 := by nlinarith [h0,h3]
  have hr : x 1+x 2 = 0 := (mul_eq_zero.mp hrprod).resolve_left hm.ne'
  have h3n : -2*x 0-y*(x 1+x 2)+2*x 3 = 0 := by nlinarith only [h3]
  rw [hr] at h3n
  have heq : x 3 = x 0 := by nlinarith only [h3n]
  have h1n : (m+y)*x 0+(y^2-2)*(x 1+x 2)-y*x 3 = 0 := by nlinarith only [h1]
  rw [hr,heq] at h1n
  have hxprod : m*x 0 = 0 := by nlinarith only [h1n]
  have hx0 : x 0 = 0 := (mul_eq_zero.mp hxprod).resolve_left hm.ne'
  exact ⟨hx0,by omega,hr⟩

private theorem second_kernel (m y : ℤ) (hm : 0 < m) (x : IntVec4)
    (hx : (shiftedSerre (family (m-y) y)^2) *ᵥ x = 0) :
    x 1+x 2 = 0 ∧ x 3 = x 0 := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  rw [square_action] at h0 h1
  simp at h0 h1
  have hr : x 1+x 2 = 0 := h0.resolve_left hm.ne'
  rw [hr] at h1
  have hdprod : m*(x 3-x 0) = 0 := by nlinarith [h1]
  have hd : x 3-x 0 = 0 := (mul_eq_zero.mp hdprod).resolve_left hm.ne'
  exact ⟨hr,by omega⟩

/-- The explicit primitive flag of the positive-total family. -/
def familyFlag (m y : ℤ) (hm : 0 < m) : PrimitiveSerreFlag (family (m-y) y) where
  p := p
  l := l
  k := m
  k_pos := hm
  first_step := by
    rw [family_shiftedSerre]
    ext i
    fin_cases i <;> simp [p,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  second_step := by
    rw [family_shiftedSerre]
    ext i
    fin_cases i <;> simp [p,l,Matrix.mulVec,dotProduct,Fin.sum_univ_four] <;> ring
  first_generator x hx := by
    obtain ⟨h0,h3,hr⟩ := first_kernel m y hm x hx
    refine ⟨-x 1,?_⟩
    ext i
    fin_cases i <;> simp [p,h0,h3] <;> omega
  second_span x := by
    constructor
    · intro hx
      obtain ⟨hr,hd⟩ := second_kernel m y hm x hx
      refine ⟨-x 1,x 0,?_⟩
      ext i
      fin_cases i <;> simp [p,l,hd] <;> omega
    · rintro ⟨n,t,rfl⟩
      rw [square_action]
      ext i
      fin_cases i <;> simp [p,l] <;> ring
  coordinates_surjective q := by
    refine ⟨![(-q.2-y*q.1),q.1,0,0],?_⟩
    dsimp only
    rw [rank_formula,degree_formula]
    simp
  isotropic_pp := by rw [rank_formula]; simp [p]
  isotropic_pl := by rw [degree_formula]; simp [p]
  isotropic_lp := by rw [rank_formula]; simp [l]
  isotropic_ll := by rw [degree_formula]; simp [l]

/-- The manuscript's concrete four-vector frame. -/
def familyFrame (m y : ℤ) (hm : 0 < m) : Frame (family (m-y) y) where
  flag := familyFlag m y hm
  u := u y
  v := v
  u_rank := by change chiVec _ (u y) p = 1; rw [rank_formula]; simp [u]
  u_degree := by change chiVec _ (u y) l = 0; rw [degree_formula]; simp [u]
  v_rank := by change chiVec _ v p = 0; rw [rank_formula]; simp [v]
  v_degree := by change chiVec _ v l = 1; rw [degree_formula]; simp [v]

theorem familyFrame_A (m y : ℤ) (hm : 0 < m) : A (familyFrame m y hm) = -1 := by
  simp [A,familyFrame,v,chiVec,gram,family,Matrix.mulVec,dotProduct,Fin.sum_univ_four]

/-- The regular family's intrinsic pair is `(-1,m)` in every frame. -/
theorem family_frame_invariants (m y : ℤ) (hm : 0 < m)
    (R : Frame (family (m-y) y)) : A R = -1 ∧ R.flag.k = m := by
  have hA := frame_A_unique R (familyFrame m y hm)
  have hk := frame_k_unique R (familyFrame m y hm)
  exact ⟨hA.trans (familyFrame_A m y hm),hk⟩

theorem family_flag_k (m y : ℤ) (hm : 0 < m)
    (F : PrimitiveSerreFlag (family (m-y) y)) : F.k = m :=
  flag_k_unique F (familyFlag m y hm)

theorem familyFrame_columns (m y : ℤ) (hm : 0 < m) :
    columns (familyFrame m y hm) = adaptedBasis y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columns,familyFrame,familyFlag,u,v,p,l,adaptedBasis]

theorem family_regular (m y : ℤ) (hm : 0 < m) :
    shiftedSerre (family (m-y) y)^3 ≠ 0 := by
  intro h
  have he := (family_cube_eq_zero_iff (m-y) y).mp h
  omega

/-- The polynomial sign test is negative for every regular family member. -/
theorem family_thirdMinorSum (m y : ℤ) :
    IntrinsicSigns.thirdMinorSum (family (m-y) y) = -4*m^2 := by
  simp [IntrinsicSigns.thirdMinorSum,family]
  ring

theorem family_negative (m y : ℤ) (hm : 0 < m) :
    IntrinsicSigns.thirdMinorSum (family (m-y) y) < 0 := by
  rw [family_thirdMinorSum]
  nlinarith [sq_pos_of_pos hm]

end SerreMarkov.FamilyIntrinsic
