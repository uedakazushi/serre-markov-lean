import SerreMarkov.Basis

/-!
# Reflection tuples and actual basis mutations

Each integral basis mutation realizes the Hurwitz operation on the four
reflections. Sign changes leave the old-coordinate reflections unchanged.
The identities hold for every integral Gram matrix, without a solution
assumption or a reflection-group classification.
-/

namespace SerreMarkov

open Matrix
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

def hurwitzTupleStep (g : Generator) (R : Fin 4 → Mat4) : Fin 4 → Mat4 :=
  match g with
  | .m1 => fun j => if j = 0 then R 0 * R 1 * R 0 else if j = 1 then R 0 else R j
  | .m2 => fun j => if j = 1 then R 1 * R 2 * R 1 else if j = 2 then R 1 else R j
  | .m3 => fun j => if j = 2 then R 2 * R 3 * R 2 else if j = 3 then R 2 else R j
  | .i1 => fun j => if j = 0 then R 1 else if j = 1 then R 1 * R 0 * R 1 else R j
  | .i2 => fun j => if j = 1 then R 2 else if j = 2 then R 2 * R 1 * R 2 else R j
  | .i3 => fun j => if j = 2 then R 3 else if j = 3 then R 3 * R 2 * R 3 else R j
  | .s1 | .s2 | .s3 | .s4 => R

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_m1 (z : Six) (j : Fin 4) :
    basisStep .m1 z * basisReflection (step .m1 z) j =
      hurwitzTupleStep .m1 (basisReflection z) j * basisStep .m1 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisMu1, mu1,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_m2 (z : Six) (j : Fin 4) :
    basisStep .m2 z * basisReflection (step .m2 z) j =
      hurwitzTupleStep .m2 (basisReflection z) j * basisStep .m2 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisMu2, mu2,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_m3 (z : Six) (j : Fin 4) :
    basisStep .m3 z * basisReflection (step .m3 z) j =
      hurwitzTupleStep .m3 (basisReflection z) j * basisStep .m3 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisMu3, mu3,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_i1 (z : Six) (j : Fin 4) :
    basisStep .i1 z * basisReflection (step .i1 z) j =
      hurwitzTupleStep .i1 (basisReflection z) j * basisStep .i1 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisInv1, inv1,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_i2 (z : Six) (j : Fin 4) :
    basisStep .i2 z * basisReflection (step .i2 z) j =
      hurwitzTupleStep .i2 (basisReflection z) j * basisStep .i2 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisInv2, inv2,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_i3 (z : Six) (j : Fin 4) :
    basisStep .i3 z * basisReflection (step .i3 z) j =
      hurwitzTupleStep .i3 (basisReflection z) j * basisStep .i3 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisInv3, inv3,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_s1 (z : Six) (j : Fin 4) :
    basisStep .s1 z * basisReflection (step .s1 z) j =
      hurwitzTupleStep .s1 (basisReflection z) j * basisStep .s1 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisEps1, eps1,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_s2 (z : Six) (j : Fin 4) :
    basisStep .s2 z * basisReflection (step .s2 z) j =
      hurwitzTupleStep .s2 (basisReflection z) j * basisStep .s2 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisEps2, eps2,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_s3 (z : Six) (j : Fin 4) :
    basisStep .s3 z * basisReflection (step .s3 z) j =
      hurwitzTupleStep .s3 (basisReflection z) j * basisStep .s3 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisEps3, eps3,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 0 in
private theorem basisReflection_hurwitz_s4 (z : Six) (j : Fin 4) :
    basisStep .s4 z * basisReflection (step .s4 z) j =
      hurwitzTupleStep .s4 (basisReflection z) j * basisStep .s4 z := by
  fin_cases j <;> apply Matrix.ext <;> intro i k
  all_goals
    fin_cases i <;> fin_cases k <;>
      simp [hurwitzTupleStep, basisStep, step, basisEps4, eps4,
        basisReflection, symmetricForm, gram, Matrix.mul_apply, Fin.sum_univ_four]

theorem basisStep_reflection_hurwitz (g : Generator) (z : Six) (j : Fin 4) :
    basisStep g z * basisReflection (step g z) j =
      hurwitzTupleStep g (basisReflection z) j * basisStep g z := by
  cases g
  · exact basisReflection_hurwitz_m1 z j
  · exact basisReflection_hurwitz_m2 z j
  · exact basisReflection_hurwitz_m3 z j
  · exact basisReflection_hurwitz_i1 z j
  · exact basisReflection_hurwitz_i2 z j
  · exact basisReflection_hurwitz_i3 z j
  · exact basisReflection_hurwitz_s1 z j
  · exact basisReflection_hurwitz_s2 z j
  · exact basisReflection_hurwitz_s3 z j
  · exact basisReflection_hurwitz_s4 z j

private theorem reflection_intertwine_mul (B P P' Q Q' : Mat4)
    (hP : B * P' = P * B) (hQ : B * Q' = Q * B) : B * (P' * Q') = (P * Q) * B := by
  calc
    B * (P' * Q') = (B * P') * Q' := by noncomm_ring
    _ = (P * B) * Q' := by rw [hP]
    _ = P * (B * Q') := by noncomm_ring
    _ = P * (Q * B) := by rw [hQ]
    _ = (P * Q) * B := by noncomm_ring

theorem hurwitzTupleStep_intertwine (g : Generator) (B : Mat4)
    (R R' : Fin 4 → Mat4) (h : ∀ j, B * R' j = R j * B) (j : Fin 4) :
    B * hurwitzTupleStep g R' j = hurwitzTupleStep g R j * B := by
  cases g <;> fin_cases j <;> simp only [hurwitzTupleStep]
  all_goals
    first
    | exact h _
    | exact reflection_intertwine_mul _ _ _ _ _
        (reflection_intertwine_mul _ _ _ _ _ (h _) (h _)) (h _)

def hurwitzTupleWord (R : Fin 4 → Mat4) : List Generator → Fin 4 → Mat4
  | [] => R
  | g :: gs => hurwitzTupleWord (hurwitzTupleStep g R) gs

theorem hurwitzTupleWord_intertwine (word : List Generator) (B : Mat4)
    (R R' : Fin 4 → Mat4) (h : ∀ j, B * R' j = R j * B) (j : Fin 4) :
    B * hurwitzTupleWord R' word j = hurwitzTupleWord R word j * B := by
  induction word generalizing R R' with
  | nil => exact h j
  | cons g gs ih =>
      exact ih (hurwitzTupleStep g R) (hurwitzTupleStep g R')
        (hurwitzTupleStep_intertwine g B R R' h)

theorem basisWord_reflection_hurwitz (z : Six) (word : List Generator) (j : Fin 4) :
    basisWord z word * basisReflection (applyWord z word) j =
      hurwitzTupleWord (basisReflection z) word j * basisWord z word := by
  induction word generalizing z with
  | nil => simp [basisWord, applyWord, hurwitzTupleWord]
  | cons g gs ih =>
      have hs := hurwitzTupleWord_intertwine gs (basisStep g z)
        (hurwitzTupleStep g (basisReflection z)) (basisReflection (step g z))
        (basisStep_reflection_hurwitz g z) j
      simp only [basisWord, applyWord, hurwitzTupleWord]
      calc
        (basisStep g z * basisWord (step g z) gs) *
            basisReflection (applyWord (step g z) gs) j =
          basisStep g z * (basisWord (step g z) gs *
            basisReflection (applyWord (step g z) gs) j) := by noncomm_ring
        _ = basisStep g z *
            (hurwitzTupleWord (basisReflection (step g z)) gs j *
              basisWord (step g z) gs) := by rw [ih]
        _ = (basisStep g z * hurwitzTupleWord (basisReflection (step g z)) gs j) *
              basisWord (step g z) gs := by noncomm_ring
        _ = (hurwitzTupleWord (hurwitzTupleStep g (basisReflection z)) gs j *
              basisStep g z) * basisWord (step g z) gs := by rw [hs]
        _ = hurwitzTupleWord (hurwitzTupleStep g (basisReflection z)) gs j *
              (basisStep g z * basisWord (step g z) gs) := by noncomm_ring

end SerreMarkov
