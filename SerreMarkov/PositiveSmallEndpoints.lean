import SerreMarkov.PositiveShortWord

/-! # Universal bounds at equal endpoints four and five

Four actual one-letter no-drop comparisons control the differences of the
opposite coordinates. Exact quadratic identities from the two solution
equations then bound their total. No search bound is assumed. -/

namespace SerreMarkov.PositiveSmallEndpoints

open PositiveChamber PositiveShortWord NegativeDescent

private theorem endpoint_guards (z : Six) (hz : Chamber z)
    (hterm : ShortTerminal z 1) :
    2*(z.d+z.e) ≤ z.a*(z.b+z.c) ∧
    2*(z.b+z.c) ≤ z.a*(z.d+z.e) ∧
    2*(z.c+z.e) ≤ z.f*(z.b+z.d) ∧
    2*(z.b+z.d) ≤ z.f*(z.c+z.e) := by
  have hp := (shortTerminal_iff_polynomial z hz 1).mp hterm
  have H (g : Generator) (hg : g ∈ braidMoves) : 0 ≤ heightPolynomial z [g] :=
    hp [g] ((mem_braidWords_iff 1 [g]).mpr ⟨by simp,by simpa using hg⟩)
  have h1 := H .m1 (by simp [braidMoves])
  have h2 := H .i1 (by simp [braidMoves])
  have h3 := H .m3 (by simp [braidMoves])
  have h4 := H .i3 (by simp [braidMoves])
  dsimp [heightPolynomial,coordinateSum,applyWord,step,mu1,inv1,mu3,inv3] at h1 h2 h3 h4
  exact ⟨by nlinarith only [h1],by nlinarith only [h2],
    by nlinarith only [h3],by nlinarith only [h4]⟩

theorem equal_endpoint_difference_bound (z : Six) (p : ℤ) (hz : Chamber z)
    (hterm : ShortTerminal z 1) (ha : z.a=p) (hf : z.f=p) :
    (p+2)*(|z.b-z.e|+|z.c-z.d|) ≤ (p-2)*(z.b+z.c+z.d+z.e) := by
  obtain ⟨h1,h2,h3,h4⟩ := endpoint_guards z hz hterm
  rw [ha] at h1 h2
  rw [hf] at h3 h4
  rcases le_total 0 (z.b-z.e) with hu | hu
  · rcases le_total 0 (z.c-z.d) with hv | hv
    · rw [abs_of_nonneg hu,abs_of_nonneg hv]
      nlinarith only [h2]
    · rw [abs_of_nonneg hu,abs_of_nonpos hv]
      nlinarith only [h4]
  · rcases le_total 0 (z.c-z.d) with hv | hv
    · rw [abs_of_nonpos hu,abs_of_nonneg hv]
      nlinarith only [h3]
    · rw [abs_of_nonpos hu,abs_of_nonpos hv]
      nlinarith only [h1]

/-- The first quadratic identity is exactly four times the `q1=8` equation. -/
theorem equal_endpoint_first_identity (z : Six) (p : ℤ)
    (hz : isSolution z) (ha : z.a=p) (hf : z.f=p) :
    (2*(z.b+z.e)-p*(z.c+z.d))^2 =
      (p^2-4)*(z.c-z.d)^2+32-8*q2 z := by
  have h := hz.1
  dsimp [q1] at h
  dsimp [q2]
  rw [ha,hf] at h ⊢
  linear_combination 4*h

/-- The complementary quadratic identity has the same exact source. -/
theorem equal_endpoint_second_identity (z : Six) (p : ℤ)
    (hz : isSolution z) (ha : z.a=p) (hf : z.f=p) :
    (p*(z.b+z.e)-2*(z.c+z.d))^2 =
      (p^2-4)*(z.b-z.e)^2+4*p^4-16*p^2+32-4*(p^2-2)*q2 z := by
  have h := hz.1
  dsimp [q1] at h
  dsimp [q2]
  rw [ha,hf] at h ⊢
  linear_combination 4*h

theorem equal_endpoint_square_bounds (z : Six) (p : ℤ)
    (hz : isSolution z) (hp : 3 ≤ p) (ha : z.a=p) (hf : z.f=p) :
    (2*(z.b+z.e)-p*(z.c+z.d))^2 ≤ (p^2-4)*(z.c-z.d)^2+64 ∧
    (p*(z.b+z.e)-2*(z.c+z.d))^2 ≤ (p^2-4)*(z.b-z.e)^2+4*p^4 := by
  have h1 := equal_endpoint_first_identity z p hz ha hf
  have h2 := equal_endpoint_second_identity z p hz ha hf
  have hq : q2 z=4 ∨ q2 z=-4 := by
    have hzero : (q2 z-4)*(q2 z+4)=0 := by nlinarith only [hz.2]
    rcases mul_eq_zero.mp hzero with h | h <;> [left;right] <;> linarith
  have hp2 : 9 ≤ p^2 := by nlinarith only [hp,sq_nonneg (p-3)]
  rcases hq with hq | hq
  · rw [hq] at h1 h2
    constructor
    · nlinarith only [h1]
    · nlinarith only [h2,hp2]
  · rw [hq] at h1 h2
    constructor <;> nlinarith only [h1,h2]

private theorem absolute_difference_squares (u v : ℤ) :
    u^2+v^2 ≤ (|u|+|v|)^2 := by
  have hu := sq_abs u
  have hv := sq_abs v
  have hp := mul_nonneg (abs_nonneg u) (abs_nonneg v)
  nlinarith only [hu,hv,hp]

theorem endpoint_four_sum_bound (z : Six) (hz : Chamber z)
    (hterm : ShortTerminal z 1) (ha : z.a=4) (hf : z.f=4) :
    z.b+z.c+z.d+z.e ≤ 40 := by
  let T := z.b+z.c+z.d+z.e
  let S := |z.b-z.e|+|z.c-z.d|
  let X := 2*(z.b+z.e)-4*(z.c+z.d)
  let Y := 4*(z.b+z.e)-2*(z.c+z.d)
  have hguard : 3*S ≤ T := by
    have h := equal_endpoint_difference_bound z 4 hz hterm ha hf
    dsimp [S,T]
    nlinarith only [h]
  have hT : 0 ≤ T := by dsimp [T]; linarith [hz.2.2.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2.1]
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hGS := mul_nonneg (show 0 ≤ T-3*S by omega) (show 0 ≤ T+3*S by omega)
  have hdiff := absolute_difference_squares (z.b-z.e) (z.c-z.d)
  have hsquare : 9*((z.b-z.e)^2+(z.c-z.d)^2) ≤ T^2 := by
    change (z.b-z.e)^2+(z.c-z.d)^2 ≤ S^2 at hdiff
    nlinarith only [hGS,hdiff]
  obtain ⟨hX,hY⟩ := equal_endpoint_square_bounds z 4 hz.1 (by decide) ha hf
  change X^2 ≤ (4^2-4)*(z.c-z.d)^2+64 at hX
  change Y^2 ≤ (4^2-4)*(z.b-z.e)^2+4*4^4 at hY
  have heq : Y-X=2*T := by dsimp [X,Y,T]; ring
  have hxy := sq_nonneg (X+Y)
  have hT2 : T^2 ≤ 1632 := by nlinarith only [heq,hxy,hX,hY,hsquare]
  change T ≤ 40
  by_contra hb
  have hge : 41 ≤ T := by omega
  nlinarith only [hge,hT2,sq_nonneg (T-41)]

theorem endpoint_five_sum_bound (z : Six) (hz : Chamber z)
    (hterm : ShortTerminal z 1) (ha : z.a=5) (hf : z.f=5) :
    z.b+z.c+z.d+z.e ≤ 63 := by
  let T := z.b+z.c+z.d+z.e
  let S := |z.b-z.e|+|z.c-z.d|
  let X := 2*(z.b+z.e)-5*(z.c+z.d)
  let Y := 5*(z.b+z.e)-2*(z.c+z.d)
  have hguard : 7*S ≤ 3*T := by
    have h := equal_endpoint_difference_bound z 5 hz hterm ha hf
    dsimp [S,T]
    nlinarith only [h]
  have hT : 0 ≤ T := by dsimp [T]; linarith [hz.2.2.2.1,hz.2.2.2.2.1,hz.2.2.2.2.2.1,hz.2.2.2.2.2.2.1]
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hGS := mul_nonneg (show 0 ≤ 3*T-7*S by omega) (show 0 ≤ 3*T+7*S by omega)
  have hdiff := absolute_difference_squares (z.b-z.e) (z.c-z.d)
  have hsquare : 49*((z.b-z.e)^2+(z.c-z.d)^2) ≤ 9*T^2 := by
    change (z.b-z.e)^2+(z.c-z.d)^2 ≤ S^2 at hdiff
    nlinarith only [hGS,hdiff]
  obtain ⟨hX,hY⟩ := equal_endpoint_square_bounds z 5 hz.1 (by decide) ha hf
  change X^2 ≤ (5^2-4)*(z.c-z.d)^2+64 at hX
  change Y^2 ≤ (5^2-4)*(z.b-z.e)^2+4*5^4 at hY
  have heq : Y-X=3*T := by dsimp [X,Y,T]; ring
  have hxy := sq_nonneg (X+Y)
  have hT2 : 63*T^2 ≤ 251272 := by nlinarith only [heq,hxy,hX,hY,hsquare]
  change T ≤ 63
  by_contra hb
  have hge : 64 ≤ T := by omega
  nlinarith only [hge,hT2,sq_nonneg (T-64)]

end SerreMarkov.PositiveSmallEndpoints
