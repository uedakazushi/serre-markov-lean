import SerreMarkov.PositiveRepresentatives
import SerreMarkov.IntrinsicUnique

/-! # Actual primitive frames of the five positive representatives

The integral vectors below generate the saturated first and second Serre
kernels and give surjective rank/degree coordinates. Thus the table of `A`
and `κ` holds in every primitive frame, without inference from cube-content.
-/
namespace SerreMarkov.PositiveRepresentativeInvariants
open Matrix IntrinsicFrame IntrinsicUnique PositiveExamples
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail Matrix.one_apply
set_option maxHeartbeats 3000000
set_option Elab.async false

def aValue (i : Fin 5) : ℤ := ![2,3,5,11,1] i
def kValue (i : Fin 5) : ℤ := ![4,3,2,1,6] i

def point (i : Fin 5) : IntVec4 :=
  ![![-1,3,-3,1], ![-1,4,-7,2], ![-1,3,-9,2],
    ![-1,4,-10,3], ![-1,-1,1,-1]] i

def line (i : Fin 5) : IntVec4 :=
  ![![-1,2,-1,0], ![-1,3,-4,1], ![-1,2,-5,1],
    ![-1,3,-7,2], ![-5,-3,2,0]] i

def rankUnit (i : Fin 5) : IntVec4 :=
  ![![0,0,0,1], ![0,0,1,0], ![0,0,1,0],
    ![1,0,0,0], ![0,0,0,-1]] i

def degreeUnit (i : Fin 5) : IntVec4 :=
  ![![0,0,-1,1], ![0,-1,1,0], ![-1,0,1,0],
    ![-3,1,0,0], ![-1,0,0,-1]] i

private def firstMatrix (i : Fin 5) : Mat4 :=
  ![!![-34,-20,-10,-4;84,46,20,6;-70,-36,-14,-4;20,10,4,2],
    !![-29,-14,-5,-4;95,41,11,4;-146,-59,-14,-4;40,16,4,2],
    !![-22,-25,-7,-5;45,43,10,3;-118,-105,-23,-5;25,22,5,2],
    !![-13,-18,-8,-7;29,25,8,3;-64,-48,-14,-4;18,13,4,2],
    !![-38,162,151,27;-18,70,63,11;11,-39,-34,-6;-3,7,6,2]] i

private def secondMatrix (i : Fin 5) : Mat4 :=
  ![!![96,80,64,48;-272,-224,-176,-128;256,208,160,112;-80,-64,-48,-32],
    !![81,63,45,72;-306,-234,-162,-252;513,387,261,396;-144,-108,-72,-108],
    !![60,100,40,60;-160,-260,-100,-140;460,740,280,380;-100,-160,-60,-80],
    !![33,77,44,55;-110,-242,-132,-154;264,572,308,352;-77,-165,-88,-99],
    !![108,-516,-504,-96;84,-396,-384,-72;-72,336,324,60;48,-216,-204,-36]] i

private theorem firstMatrix_correct (i : Fin 5) :
    shiftedSerre (representative i) = firstMatrix i := by
  fin_cases i <;> decide +kernel

private theorem secondMatrix_correct (i : Fin 5) :
    shiftedSerre (representative i)^2 = secondMatrix i := by
  fin_cases i <;> decide +kernel

private theorem point_kernel (i : Fin 5) :
    shiftedSerre (representative i) *ᵥ point i = 0 := by
  rw [firstMatrix_correct]
  fin_cases i <;> decide +kernel

private theorem line_step (i : Fin 5) :
    shiftedSerre (representative i) *ᵥ line i = -(kValue i • point i) := by
  rw [firstMatrix_correct]
  fin_cases i <;> decide +kernel

private theorem vector_eta (x : IntVec4) : x = ![x 0,x 1,x 2,x 3] := by
  ext j
  fin_cases j <;> rfl

private theorem first_kernel_generator (i : Fin 5) (x : IntVec4)
    (hx : shiftedSerre (representative i) *ᵥ x = 0) :
    ∃ n : ℤ, x = n • point i := by
  rw [firstMatrix_correct] at hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  refine ⟨-x 0,?_⟩
  rw [vector_eta x]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstMatrix,point,Matrix.mulVec,dotProduct,Fin.sum_univ_four,Pi.smul_apply] at h0 h1 h2 h3 ⊢ <;> linarith

private def firstCoefficient (i : Fin 5) (x : IntVec4) : ℤ :=
  ![2*x 0+x 1,3*x 0+x 1,2*x 0+x 1,3*x 0+x 1,2*x 1+3*x 2] i

private def secondCoefficient (i : Fin 5) (x : IntVec4) : ℤ :=
  ![-3*x 0-x 1,-4*x 0-x 1,-3*x 0-x 1,-4*x 0-x 1,-x 1-x 2] i

private theorem second_kernel_span (i : Fin 5) (x : IntVec4) :
    (shiftedSerre (representative i)^2) *ᵥ x = 0 ↔
      ∃ n t : ℤ, x = n • point i + t • line i := by
  constructor
  · intro hx
    rw [secondMatrix_correct] at hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    have h3 := congrFun hx 3
    refine ⟨firstCoefficient i x,secondCoefficient i x,?_⟩
    rw [vector_eta x]
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [secondMatrix,point,line,firstCoefficient,secondCoefficient,
        Matrix.mulVec,dotProduct,Fin.sum_univ_four,Pi.smul_apply] at h0 h1 h2 h3 ⊢ <;> linarith
  · rintro ⟨n,t,rfl⟩
    rw [pow_two,←Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_neg,point_kernel,line_step,Matrix.mulVec_zero,smul_zero,neg_zero,add_zero]

private theorem unit_coordinates (i : Fin 5) :
    chiVec (representative i) (rankUnit i) (point i) = 1 ∧
    chiVec (representative i) (rankUnit i) (line i) = 0 ∧
    chiVec (representative i) (degreeUnit i) (point i) = 0 ∧
    chiVec (representative i) (degreeUnit i) (line i) = 1 := by
  fin_cases i <;> norm_num [chiVec,representative,gram,rankUnit,degreeUnit,
    point,line,Matrix.mulVec,dotProduct,Fin.sum_univ_four]

private theorem flag_isotropic (i : Fin 5) :
    chiVec (representative i) (point i) (point i) = 0 ∧
    chiVec (representative i) (point i) (line i) = 0 ∧
    chiVec (representative i) (line i) (point i) = 0 ∧
    chiVec (representative i) (line i) (line i) = 0 := by
  fin_cases i <;> norm_num [chiVec,representative,gram,point,line,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four]

/-- Actual primitive flags, including their saturated second-kernel span. -/
def explicitFlag (i : Fin 5) : PrimitiveSerreFlag (representative i) where
  p := point i
  l := line i
  k := kValue i
  k_pos := by fin_cases i <;> decide +kernel
  first_step := point_kernel i
  second_step := line_step i
  first_generator := first_kernel_generator i
  second_span := second_kernel_span i
  coordinates_surjective q := by
    obtain ⟨hur,hud,hvr,hvd⟩ := unit_coordinates i
    refine ⟨q.1 • rankUnit i + q.2 • degreeUnit i,?_⟩
    simp only [chiVec_add_left,chiVec_smul_left,hur,hud,hvr,hvd,mul_one,mul_zero,zero_add,add_zero,Prod.mk.eta]
  isotropic_pp := (flag_isotropic i).1
  isotropic_pl := (flag_isotropic i).2.1
  isotropic_lp := (flag_isotropic i).2.2.1
  isotropic_ll := (flag_isotropic i).2.2.2

/-- A concrete integral frame for each actual Gram tuple. -/
def explicitFrame (i : Fin 5) : Frame (representative i) where
  flag := explicitFlag i
  u := rankUnit i
  v := degreeUnit i
  u_rank := (unit_coordinates i).1
  u_degree := (unit_coordinates i).2.1
  v_rank := (unit_coordinates i).2.2.1
  v_degree := (unit_coordinates i).2.2.2

theorem explicitFrame_A (i : Fin 5) : A (explicitFrame i) = aValue i := by
  fin_cases i <;> norm_num [A,explicitFrame,degreeUnit,chiVec,representative,gram,
    aValue,Matrix.mulVec,dotProduct,Fin.sum_univ_four]

theorem explicitFrame_k (i : Fin 5) : (explicitFrame i).flag.k = kValue i := rfl

/-- Every primitive frame has the same parameters as the displayed one. -/
theorem representative_frame_invariants (i : Fin 5) (R : Frame (representative i)) :
    A R = aValue i ∧ R.flag.k = kValue i := by
  exact ⟨(frame_A_unique R (explicitFrame i)).trans (explicitFrame_A i),
    (frame_k_unique R (explicitFrame i)).trans (explicitFrame_k i)⟩

theorem representative_flag_k (i : Fin 5) (F : PrimitiveSerreFlag (representative i)) :
    F.k = kValue i :=
  (flag_k_unique F (explicitFlag i)).trans rfl

end SerreMarkov.PositiveRepresentativeInvariants
