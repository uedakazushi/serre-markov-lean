import SerreMarkov.NegativeUnitEdge
import SerreMarkov.NegativeTwoEdge
import SerreMarkov.AffineTriangles

/-! # Unit-edge descent with two negative neighboring pairings

All outer absolute bounds are two. Degenerate equalities are handled by an
actual affine triangle, and all other cases have strict original-height descent.
-/

namespace SerreMarkov.NegativeUnitPairTwo

set_option maxHeartbeats 1000000

open NegativeDescent NegativePairDescent NegativeTriangles NegativeTwoEdge
open AffineTriangles

private def unitCentralPolynomial (a b d e k : ℤ) : ℤ :=
  a^2-a*b*d^3+a*b*d-a*d^2*k+2*a*k+b^2*d^2+b*d*k+d^4-7*d^2+k^2+
    (-a*b*d+b^2+d^2)*e^2+
    (-a^2*d-a*b*d^2+2*a*b-a*d*k+b^2*d+2*b*k+d^3)*e

set_option maxHeartbeats 1000000 in
private theorem unitCentralPolynomial_shift_le (B D T E k : ℤ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hk : k = 4 ∨ k = -4) :
    unitCentralPolynomial (B+2+D+T) (B+2) (B+2+D) (E+2) k ≤ -(B+D+T) ∧
    unitCentralPolynomial (B+2+D+T) (B+2+D) (B+2) (E+2) k ≤ -(B+D+T) := by
  rcases hk with rfl | rfl
  all_goals
    constructor <;> apply sub_nonneg.mp <;> dsimp [unitCentralPolynomial] <;>
      ring_nf <;> positivity

theorem unit_central_max_two (a b c d e : ℤ)
    (hb : 2 ≤ b) (hd : 2 ≤ d) (he : 2 ≤ e) (hab : b ≤ a) (had : d ≤ a)
    (hsol : isSolution ⟨a,b,c,d,e,-1⟩) : a=2 ∧ b=2 ∧ d=2 := by
  have hk : -a-b*e+c*d = 4 ∨ -a-b*e+c*d = -4 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    norm_num
    simpa [q2] using hsol.2
  have hpoly : unitCentralPolynomial a b d e (-a-b*e+c*d) ≤ -(a-2) := by
    by_cases hbd : b ≤ d
    · have hh := (unitCentralPolynomial_shift_le (b-2) (d-b) (a-d) (e-2)
        (-a-b*e+c*d) (by omega) (by omega) (by omega) (by omega) hk).1
      convert hh using 1 <;> dsimp [unitCentralPolynomial] <;> ring
    · have hh := (unitCentralPolynomial_shift_le (d-2) (b-d) (a-b) (e-2)
        (-a-b*e+c*d) (by omega) (by omega) (by omega) (by omega) hk).2
      convert hh using 1 <;> dsimp [unitCentralPolynomial] <;> ring
  have hcert : d^2*(q1 ⟨a,b,c,d,e,-1⟩-8) =
      unitCentralPolynomial a b d e (-a-b*e+c*d) := by
    dsimp [unitCentralPolynomial,q1]
    ring
  rw [hsol.1] at hcert
  simp only [sub_self,mul_zero] at hcert
  rw [← hcert] at hpoly
  omega

private theorem triangle_strict_two (u v w : ℤ) (hu : 3 ≤ u) (hv : 2 ≤ v)
    (_hw : 2 ≤ w) (hum : u < w) (hvm : v ≤ w)
    (htri : 4 ≤ cayleyDefect u v w) : |u*v-w| < w := by
  by_cases hv2 : v=2
  · subst v
    exact abs_lt.mpr ⟨by omega,by omega⟩
  exact cayley_positive_abs_descent u v w hu (by omega) (by omega) ⟨hum.le,hvm⟩ htri

/-- The strict pair alternative holds when the central positive edge exceeds two. -/
theorem unit_tail_pair_strict (a b c d e : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hsol : isSolution ⟨a,b,c,d,e,-1⟩)
    (htri1 : 4 ≤ cayleyDefect a b d) (htri2 : 4 ≤ cayleyDefect a c e) :
    (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  have hn1 : ¬ (b ≤ a ∧ d ≤ a) := by
    rintro ⟨hba,hda⟩
    have hh := unit_central_max_two a b c d e hb hd he hba hda hsol
    omega
  have hsol2 : isSolution ⟨a,e,d,c,b,-1⟩ := by
    constructor
    · convert hsol.1 using 1 <;> dsimp [q1] <;> ring
    · convert hsol.2 using 1 <;> dsimp [q2] <;> ring
  have hn2 : ¬ (c ≤ a ∧ e ≤ a) := by
    rintro ⟨hca,hea⟩
    have hh := unit_central_max_two a e d c b he hc hb hea hca hsol2
    omega
  by_cases hbd : b ≤ d
  · have had : a < d := by omega
    have hdropd := triangle_strict_two a b d ha hb hd had hbd htri1
    by_cases hce : c ≤ e
    · have hae : a < e := by omega
      exact Or.inl ⟨hdropd,triangle_strict_two a c e ha hc he hae hce htri2⟩
    · have hac : a < c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      have hdropc := triangle_strict_two a e c ha he hc hac (by omega) htri2'
      have hdomd : a*b ≤ 2*d := by have hh := (abs_lt.mp hdropd).2; omega
      have hdomc : a*e ≤ 2*c := by have hh := (abs_lt.mp hdropc).2; omega
      exact False.elim (opposed_dominance_two_impossible a b c d e (-1) ha hb he
        (by norm_num) hdomd hdomc (solution_gramDiscriminant _ hsol))
  · have hab : a < b := by omega
    have htri1' : 4 ≤ cayleyDefect a d b := by
      convert htri1 using 1 <;> dsimp [cayleyDefect] <;> ring
    have hdropb := triangle_strict_two a d b ha hd hb hab (by omega) htri1'
    by_cases hce : c ≤ e
    · have hae : a < e := by omega
      have hdrope := triangle_strict_two a c e ha hc he hae hce htri2
      have hdomb : a*d ≤ 2*b := by have hh := (abs_lt.mp hdropb).2; omega
      have hdome : a*c ≤ 2*e := by have hh := (abs_lt.mp hdrope).2; omega
      have hdisc3 : gramDiscriminant a d e b c (-1) = 0 := by
        convert solution_gramDiscriminant _ hsol using 1 <;>
          dsimp [gramDiscriminant,q1,q2] <;> ring
      exact False.elim (opposed_dominance_two_impossible a d e b c (-1) ha hd hc
        (by norm_num) hdomb hdome hdisc3)
    · have hac : a < c := by omega
      have htri2' : 4 ≤ cayleyDefect a e c := by
        convert htri2 using 1 <;> dsimp [cayleyDefect] <;> ring
      exact Or.inr ⟨hdropb,triangle_strict_two a e c ha he hc hac (by omega) htri2'⟩

private theorem center_two_sign (b c d e : ℤ) (hz : isSolution ⟨2,b,c,d,e,-1⟩) :
    -2-b*e+c*d=4 ∨ -2-b*e+c*d=-4 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  norm_num
  simpa [q2] using hz.2

private theorem center_two_equal (b c e : ℤ) (hb : 2 ≤ b)
    (hz : isSolution ⟨2,b,c,b,e,-1⟩) : b=2 := by
  rcases center_two_sign b c b e hz with h | h
  · have hcon := edge_two_conic_plus b c b e (-1) hz.1 (by simpa [q2] using h)
    have hc : (c-e)^2=3^2 := by nlinarith only [hcon]
    have hprod : b*(c-e)=6 := by nlinarith only [h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hc | hc <;> nlinarith
  · have hcon := edge_two_conic_minus b c b e (-1) hz.1 (by simpa [q2] using h)
    have hc : (c-e)^2=1^2 := by nlinarith only [hcon]
    have hprod : b*(c-e)=-2 := by nlinarith only [h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hc | hc <;> nlinarith

private theorem center_two_opposed_impossible (b c d e : ℤ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hbd : b<d) (hec : e<c) (hz : isSolution ⟨2,b,c,d,e,-1⟩) : False := by
  have hq : -2-b*e+c*d=4 := by
    rcases center_two_sign b c d e hz with h | h
    · exact h
    · have h1 := mul_pos (show 0<c-e by omega) (show 0<d by omega)
      have h2 := mul_pos (show 0<d-b by omega) (show 0<e by omega)
      nlinarith
  let s := d-b
  let t := c-e
  have hs : 1 ≤ s := by dsimp [s]; omega
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hprod : b*t+e*s+s*t=6 := by dsimp [s,t]; nlinarith only [hq]
  have h1 := mul_nonneg (by omega : 0 ≤ b-2) (by omega : 0 ≤ t)
  have h2 := mul_nonneg (by omega : 0 ≤ e-2) (by omega : 0 ≤ s)
  have h3 := mul_nonneg (by omega : 0 ≤ s-1) (by omega : 0 ≤ t-1)
  have hsum : s+t ≤ 2 := by nlinarith only [hprod,h1,h2,h3]
  have hs1 : s=1 := by omega
  have ht1 : t=1 := by omega
  have hcon := edge_two_conic_plus b c d e (-1) hz.1 (by simpa [q2] using hq)
  have hds : b-d=-1 := by dsimp [s] at hs1; omega
  have het : c-e=1 := by dsimp [t] at ht1; omega
  rw [hds,het] at hcon
  norm_num at hcon

private theorem center_two_reverse_opposed_impossible (b c d e : ℤ)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hdb : d<b) (hce : c<e) (hz : isSolution ⟨2,b,c,d,e,-1⟩) : False := by
  let s := b-d
  let t := e-c
  have hs : 1 ≤ s := by dsimp [s]; omega
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hgap : 5 ≤ b*e-c*d := by
    have h1 := mul_nonneg (by omega : 0 ≤ d-2) (by omega : 0 ≤ t)
    have h2 := mul_nonneg (by omega : 0 ≤ c-2) (by omega : 0 ≤ s)
    have h3 := mul_nonneg (by omega : 0 ≤ s-1) (by omega : 0 ≤ t-1)
    dsimp [s,t] at hs ht h1 h2 h3
    nlinarith
  rcases center_two_sign b c d e hz with h | h <;> omega

/-- At central edge two, equality gives an affine triangle; every remaining
solution gives simultaneous strict reduction of both neighboring pairs. -/
theorem unit_tail_pair_two (a b c d e : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (he : 2 ≤ e)
    (hsol : isSolution ⟨a,b,c,d,e,-1⟩)
    (htri1 : 4 ≤ cayleyDefect a b d) (htri2 : 4 ≤ cayleyDefect a c e) :
    (a=2 ∧ b=2 ∧ d=2) ∨ (a=2 ∧ c=2 ∧ e=2) ∨
      (|a*b-d| < d ∧ |a*c-e| < e) ∨ (|a*d-b| < b ∧ |a*e-c| < c) := by
  by_cases ha2 : a=2
  · subst a
    by_cases hbd : b=d
    · have hb2 := center_two_equal b c e hb (by simpa [← hbd] using hsol)
      exact Or.inl ⟨rfl,hb2,by omega⟩
    by_cases hce : c=e
    · have hsol2 : isSolution ⟨2,e,d,e,b,-1⟩ := by
        constructor
        · convert hsol.1 using 1 <;> dsimp [q1] <;> rw [hce] <;> ring
        · convert hsol.2 using 1 <;> dsimp [q2] <;> rw [hce] <;> ring
      have he2 := center_two_equal e d b he hsol2
      exact Or.inr (Or.inl ⟨rfl,by omega,he2⟩)
    by_cases hbdlt : b<d
    · by_cases hcelt : c<e
      · exact Or.inr (Or.inr (Or.inl ⟨abs_lt.mpr ⟨by omega,by omega⟩,
          abs_lt.mpr ⟨by omega,by omega⟩⟩))
      · exact False.elim (center_two_opposed_impossible b c d e hb hc hd he hbdlt (by omega) hsol)
    · by_cases heclt : e<c
      · exact Or.inr (Or.inr (Or.inr ⟨abs_lt.mpr ⟨by omega,by omega⟩,
          abs_lt.mpr ⟨by omega,by omega⟩⟩))
      · exact False.elim (center_two_reverse_opposed_impossible b c d e hb hc hd he (by omega) (by omega) hsol)
  · rcases unit_tail_pair_strict a b c d e (by omega) hb hc hd he hsol htri1 htri2 with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- The complete `(--+)` unit-edge chamber reduces by actual mutations or
an actual affine triangle, with absolute outer bounds only two. -/
theorem unit_two_negative_right_reduction (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0)
    (ha : z.a=1) (hb : 2 ≤ z.b) (hc : 2 ≤ z.c)
    (hd : z.d ≤ -2) (he : z.e ≤ -2) (hf : 2 ≤ z.f) : FamilyOrDrop z := by
  obtain ⟨htri1,htri2,htri3,htri4⟩ := negative_triangle_inequalities z hz hneg
  have hsol : isSolution ⟨z.f,z.b,-z.d,z.c,-z.e,-1⟩ := by
    constructor
    · convert hz.1 using 1 <;> dsimp [q1] <;> rw [ha] <;> ring
    · convert hz.2 using 1 <;> dsimp [q2] <;> rw [ha] <;> ring
  have htri1' : 4 ≤ cayleyDefect z.f z.b z.c := by
    convert htri3 using 1 <;> dsimp [cayleyDefect] <;> ring
  have htri2' : 4 ≤ cayleyDefect z.f (-z.d) (-z.e) := by
    convert htri4 using 1 <;> dsimp [cayleyDefect] <;> ring
  rcases unit_tail_pair_two z.f z.b (-z.d) z.c (-z.e)
    hf hb (by omega) hc (by omega) hsol htri1' htri2' with h | h | h | h
  · left
    apply affine_triangle_reachable_family z hz
    right; right; left
    obtain ⟨hfa,hba,hca⟩ := h
    simp [AffineTriangle,hfa,hba,hca]
  · left
    apply affine_triangle_reachable_family z hz
    right; right; right
    obtain ⟨hfa,hda,hea⟩ := h
    have hdz : z.d=-2 := by omega
    have hez : z.e=-2 := by omega
    simp [AffineTriangle,hfa,hdz,hez]
  · right
    refine ⟨[.m3],?_⟩
    change l1 (mu3 z) < l1 z
    rw [mu3_drop_iff]
    obtain ⟨h1,h2⟩ := h
    have hh : z.f*(-z.d)-(-z.e)=-(z.f*z.d-z.e) := by ring
    rw [hh,abs_neg] at h2
    simp only [abs_of_nonneg (by omega : 0 ≤ z.c),abs_of_nonpos (by omega : z.e ≤ 0)]
    linarith
  · right
    refine ⟨[.i3],?_⟩
    change l1 (inv3 z) < l1 z
    rw [inv3_drop_iff]
    obtain ⟨h1,h2⟩ := h
    have hh : z.f*(-z.e)-(-z.d)=-(z.f*z.e-z.d) := by ring
    rw [hh,abs_neg] at h2
    simp only [abs_of_nonneg (by omega : 0 ≤ z.b),abs_of_nonpos (by omega : z.d ≤ 0)]
    linarith

end SerreMarkov.NegativeUnitPairTwo
