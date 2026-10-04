import SerreMarkov.PositiveConic

/-! Explicit bounds for the last three coordinates with a fixed first triangle.
These bounds depend on that triangle; no global terminal bound is assumed.
-/
namespace SerreMarkov.PositiveConicBound
open PositiveConic PositiveChamber PositiveShortWord
set_option maxHeartbeats 4000000

def quadraticX (z : Six) : ℤ := z.d^2+triangleSize z
def quadraticY (z : Six) : ℤ := z.a^2+triangleSize z
def mixed (z : Six) : ℤ := adjacentDifference z*triangleSize z+2*z.a*z.d
def linearX (z : Six) : ℤ :=
  2*quadraticX z*firstOffset z+mixed z*secondOffset z
def linearY (z : Six) : ℤ :=
  mixed z*firstOffset z+2*quadraticY z*secondOffset z
def constantTerm (z : Six) : ℤ :=
  quadraticX z*(firstOffset z)^2+
  mixed z*firstOffset z*secondOffset z+
  quadraticY z*(secondOffset z)^2-
  z.b^2*(adjacentDifference z)^2*(triangleSize z+4)^2
def slackBound (z : Six) : ℤ :=
  (linearX z)^2+(linearY z)^2+2*|constantTerm z|+1

theorem expanded_conic (z : Six) :
    conic z=quadraticX z*(firstSlack z)^2+
      mixed z*firstSlack z*secondSlack z+
      quadraticY z*(secondSlack z)^2-
      linearX z*firstSlack z-linearY z*secondSlack z+constantTerm z := by
  dsimp [conic,quadraticX,quadraticY,mixed,linearX,linearY,constantTerm]
  ring

theorem quadrant_bound (P L Q kx ky C x y : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hP : 0<P) (hQ : 0<Q) (hL : 0≤L)
    (heq : P*x^2+L*x*y+Q*y^2-kx*x-ky*y+C=0) :
    x≤kx^2+ky^2+2*|C|+1 ∧ y≤kx^2+ky^2+2*|C|+1 := by
  have hxx := mul_nonneg (show 0≤P-1 by omega) (sq_nonneg x)
  have hyy := mul_nonneg (show 0≤Q-1 by omega) (sq_nonneg y)
  have hxy := mul_nonneg hL (mul_nonneg hx hy)
  have hC := le_abs_self C
  have hmC := neg_le_abs C
  have hquad : x^2+y^2≤kx^2+ky^2+2*|C| := by
    nlinarith only [hxx,hyy,hxy,heq,sq_nonneg (x-kx),sq_nonneg (y-ky),hmC]
  have hnon : 0≤kx^2+ky^2+2*|C| := by positivity
  constructor
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg x]

theorem terminal_slack_bounds (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 2) :
    0≤firstSlack z ∧ firstSlack z≤slackBound z ∧
    0≤secondSlack z ∧ secondSlack z≤slackBound z := by
  have h := chamber_coefficient_bounds z hz
  have hn := terminal_slacks_nonnegative z hz ht
  have heq := solution_conic z hz.1
  rw [expanded_conic] at heq
  have hb := quadrant_bound (quadraticX z) (mixed z) (quadraticY z)
    (linearX z) (linearY z) (constantTerm z) (firstSlack z) (secondSlack z)
    hn.1 hn.2 h.2.2.1 h.2.2.2.2 h.2.2.2.1.le heq
  exact ⟨hn.1,hb.1,hn.2,hb.2⟩

def recoveryScale (z : Six) : ℤ :=
  z.b*adjacentDifference z*triangleSize z
def tailBoundC (z : Six) : ℤ :=
  quadraticX z*(slackBound z+|firstOffset z|)+
  z.a*z.d*(slackBound z+|secondOffset z|)+
  4*z.d*(quadraticX z+z.a^2)
def tailBoundF (z : Six) : ℤ :=
  z.a*z.d*(slackBound z+|firstOffset z|)+
  quadraticY z*(slackBound z+|secondOffset z|)+
  4*z.a*(quadraticY z+z.d^2)
def tailBoundE (z : Six) : ℤ := z.a*tailBoundF z+z.d*tailBoundC z+4

theorem recover_c (z : Six) :
    recoveryScale z*z.c=
      quadraticX z*(firstSlack z-firstOffset z)+
      z.a*z.d*(secondSlack z-secondOffset z)-
      z.d*(quadraticX z+z.a^2)*q2 z := by
  rw [firstSlack_formula,secondSlack_formula]
  dsimp [recoveryScale,quadraticX,triangleSize,adjacentDifference,
    firstOffset,secondOffset,q2]
  ring

theorem recover_f (z : Six) :
    recoveryScale z*z.f=
      z.a*z.d*(firstSlack z-firstOffset z)+
      quadraticY z*(secondSlack z-secondOffset z)-
      z.a*(quadraticY z+z.d^2)*q2 z := by
  rw [firstSlack_formula,secondSlack_formula]
  dsimp [recoveryScale,quadraticY,triangleSize,adjacentDifference,
    firstOffset,secondOffset,q2]
  ring

theorem recovery_bound (δ U V W x y X Y q c S : ℤ)
    (hδ : 1≤δ) (hU : 0≤U) (hV : 0≤V) (hW : 0≤W) (hc : 0≤c)
    (hx : x≤S) (hy : y≤S) (hq : -4≤q)
    (hr : δ*c=U*(x-X)+V*(y-Y)-W*q) :
    c≤U*(S+|X|)+V*(S+|Y|)+4*W := by
  have hhx : x-X≤S+|X| := by have h:=neg_le_abs X; omega
  have hhy : y-Y≤S+|Y| := by have h:=neg_le_abs Y; omega
  have ht1 := mul_le_mul_of_nonneg_left hhx hU
  have ht2 := mul_le_mul_of_nonneg_left hhy hV
  have ht3 := mul_nonneg hW (show 0≤q+4 by omega)
  have ht4 := mul_nonneg (show 0≤δ-1 by omega) hc
  nlinarith only [hr,ht1,ht2,ht3,ht4]

/-- With the first triangle fixed, two-step terminality bounds all remaining
coordinates by explicit expressions in that triangle. -/
theorem terminal_tail_bounds (z : Six) (hz : Chamber z)
    (ht : ShortTerminal z 2) :
    z.c≤tailBoundC z ∧ z.f≤tailBoundF z ∧ z.e≤tailBoundE z := by
  have hh := chamber_coefficient_bounds z hz
  have hs := terminal_slack_bounds z hz ht
  have ha : 0≤z.a := by have h:=hz.2.2.1; omega
  have hb : 1≤z.b := by have h:=hz.2.2.2.1; omega
  have hc : 0≤z.c := by have h:=hz.2.2.2.2.1; omega
  have hd : 0≤z.d := by have h:=hz.2.2.2.2.2.1; omega
  have he : 0≤z.e := by have h:=hz.2.2.2.2.2.2.1; omega
  have hf : 0≤z.f := by have h:=hz.2.2.2.2.2.2.2; omega
  have hδ : 1≤recoveryScale z := by
    have hpos : 0<z.b*adjacentDifference z*triangleSize z :=
      mul_pos (mul_pos (by omega) (by omega)) (by omega)
    dsimp [recoveryScale]
    omega
  have hq : -4≤q2 z := by nlinarith only [hz.1.2,sq_nonneg (q2 z+4)]
  have hC := recovery_bound (recoveryScale z) (quadraticX z) (z.a*z.d)
    (z.d*(quadraticX z+z.a^2)) (firstSlack z) (secondSlack z)
    (firstOffset z) (secondOffset z) (q2 z) z.c (slackBound z)
    hδ hh.2.2.1.le (mul_nonneg ha hd)
    (mul_nonneg hd (add_nonneg hh.2.2.1.le (sq_nonneg z.a))) hc
    hs.2.1 hs.2.2.2 hq (recover_c z)
  have hF := recovery_bound (recoveryScale z) (z.a*z.d) (quadraticY z)
    (z.a*(quadraticY z+z.d^2)) (firstSlack z) (secondSlack z)
    (firstOffset z) (secondOffset z) (q2 z) z.f (slackBound z)
    hδ (mul_nonneg ha hd) hh.2.2.2.2.le
    (mul_nonneg ha (add_nonneg hh.2.2.2.2.le (sq_nonneg z.d))) hf
    hs.2.1 hs.2.2.2 hq (recover_f z)
  have hCb : z.c≤tailBoundC z := by simpa [tailBoundC,mul_assoc] using hC
  have hFb : z.f≤tailBoundF z := by simpa [tailBoundF,mul_assoc] using hF
  have hE : z.e≤tailBoundE z := by
    have hcf := mul_le_mul_of_nonneg_left hCb hd
    have hff := mul_le_mul_of_nonneg_left hFb ha
    have hbe := mul_nonneg (show 0≤z.b-1 by omega) he
    dsimp [tailBoundE,q2] at hq ⊢
    nlinarith only [hcf,hff,hbe,hq]
  exact ⟨hCb,hFb,hE⟩

theorem tail_bounds_depend_on_first_triangle (z w : Six)
    (ha : z.a=w.a) (hb : z.b=w.b) (hd : z.d=w.d) :
    tailBoundC z=tailBoundC w ∧ tailBoundF z=tailBoundF w ∧
    tailBoundE z=tailBoundE w := by
  simp only [tailBoundC,tailBoundF,tailBoundE,slackBound,linearX,linearY,
    constantTerm,quadraticX,quadraticY,mixed,firstOffset,secondOffset,
    adjacentDifference,triangleSize,ha,hb,hd,and_self]

end SerreMarkov.PositiveConicBound
