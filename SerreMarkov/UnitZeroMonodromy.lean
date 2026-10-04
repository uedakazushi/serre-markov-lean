import SerreMarkov.NegativeDescent

/-! # Exact braid monodromy on the unit-zero conic

The first-three full twist realizes the symmetric conic's Vieta move followed
by exchange of its two coordinates. Every identity holds for arbitrary integer
parameters, before imposing the solution equation.
-/

namespace SerreMarkov.UnitZeroMonodromy

open NegativeDescent

/-- The unit-zero slice with second solution invariant equal to four. -/
def unitZeroSlice (d c e : ℤ) : Six := ⟨1,0,c,d,e,4-d*c⟩

/-- The remaining solution equation on this slice. -/
def unitZeroConic (d c e : ℤ) : ℤ :=
  c^2+e^2+(d^2-1)*c*e-4*d*(c+e)+d^2+9

def fullTwistWord : List Generator := [.m1,.m2,.m1,.m2,.m1,.m2]
def inverseFullTwistWord : List Generator := [.i2,.i1,.i2,.i1,.i2,.i1]

/-- This is a polynomial identity on the entire slice, with no conic assumption. -/
theorem applyWord_fullTwist (d c e : ℤ) :
    applyWord (unitZeroSlice d c e) fullTwistWord=
      unitZeroSlice d e (4*d-c-(d^2-1)*e) := by
  ext <;> simp [unitZeroSlice,fullTwistWord,applyWord,step,mu1,mu2] <;> ring

/-- The inverse full twist is the other Vieta move followed by exchange. -/
theorem applyWord_inverseFullTwist (d c e : ℤ) :
    applyWord (unitZeroSlice d c e) inverseFullTwistWord=
      unitZeroSlice d (4*d-e-(d^2-1)*c) c := by
  ext <;> simp [unitZeroSlice,inverseFullTwistWord,applyWord,step,inv1,inv2] <;> ring

theorem reachable_fullTwist (d c e : ℤ) :
    Reachable (unitZeroSlice d c e) (unitZeroSlice d e (4*d-c-(d^2-1)*e)) :=
  ⟨fullTwistWord,applyWord_fullTwist d c e⟩

theorem reachable_inverseFullTwist (d c e : ℤ) :
    Reachable (unitZeroSlice d c e) (unitZeroSlice d (4*d-e-(d^2-1)*c) c) :=
  ⟨inverseFullTwistWord,applyWord_inverseFullTwist d c e⟩

theorem conic_forward (d c e : ℤ) :
    unitZeroConic d e (4*d-c-(d^2-1)*e)=unitZeroConic d c e := by
  dsimp [unitZeroConic]
  ring

theorem conic_inverse (d c e : ℤ) :
    unitZeroConic d (4*d-e-(d^2-1)*c) c=unitZeroConic d c e := by
  dsimp [unitZeroConic]
  ring

@[simp] theorem slice_q2 (d c e : ℤ) : q2 (unitZeroSlice d c e)=4 := by
  dsimp [q2,unitZeroSlice]
  ring

theorem slice_q1 (d c e : ℤ) : q1 (unitZeroSlice d c e)=unitZeroConic d c e+8 := by
  dsimp [q1,unitZeroSlice,unitZeroConic]
  ring

/-- The slice's two original integer equations are exactly this single conic. -/
theorem solution_slice_iff_conic (d c e : ℤ) :
    isSolution (unitZeroSlice d c e) ↔ unitZeroConic d c e=0 := by
  unfold isSolution
  rw [slice_q1,slice_q2]
  norm_num

/-- The slice representation of an arbitrary solution with the stated coordinates. -/
theorem eq_slice_of_coordinates (z : Six) (ha : z.a=1) (hb : z.b=0)
    (hk : q2 z=4) : z=unitZeroSlice z.d z.c z.e := by
  ext <;> simp [unitZeroSlice,ha,hb]
  dsimp [q2] at hk
  rw [ha,hb] at hk
  nlinarith [hk]

theorem slice_integerL1 (d c e : ℤ) :
    integerL1 (unitZeroSlice d c e)=1+|c|+|d|+|e|+|4-d*c| := by
  simp [integerL1,unitZeroSlice]

end SerreMarkov.UnitZeroMonodromy
