import Mathlib.Tactic

/-!
# Polynomial algebra of Serre–Markov mutations

This module formalizes the six scalar coordinates of a unipotent upper triangular
Gram matrix and its braid and sign operations. Every theorem in this module is
proved by the Lean kernel; no classification result is assumed.
-/

namespace SerreMarkov

@[ext] structure Six where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  deriving DecidableEq, Repr

def q1 (z : Six) : ℤ :=
  z.a * z.c * z.d * z.f - z.a * z.b * z.d - z.a * z.c * z.e -
    z.b * z.c * z.f - z.d * z.e * z.f + z.a ^ 2 + z.b ^ 2 +
    z.c ^ 2 + z.d ^ 2 + z.e ^ 2 + z.f ^ 2

def q2 (z : Six) : ℤ := z.a * z.f - z.b * z.e + z.c * z.d

def isSolution (z : Six) : Prop := q1 z = 8 ∧ q2 z ^ 2 = 16

def mu1 (z : Six) : Six :=
  ⟨z.a, z.a * z.b - z.d, z.a * z.c - z.e, z.b, z.c, z.f⟩
def inv1 (z : Six) : Six :=
  ⟨z.a, z.d, z.e, z.a * z.d - z.b, z.a * z.e - z.c, z.f⟩
def mu2 (z : Six) : Six :=
  ⟨z.a * z.d - z.b, z.a, z.c, z.d, z.d * z.e - z.f, z.e⟩
def inv2 (z : Six) : Six :=
  ⟨z.b, z.b * z.d - z.a, z.c, z.d, z.f, z.d * z.f - z.e⟩
def mu3 (z : Six) : Six :=
  ⟨z.a, z.f * z.b - z.c, z.b, z.f * z.d - z.e, z.d, z.f⟩
def inv3 (z : Six) : Six :=
  ⟨z.a, z.c, z.f * z.c - z.b, z.e, z.f * z.e - z.d, z.f⟩

def eps1 (z : Six) : Six := ⟨-z.a, -z.b, -z.c, z.d, z.e, z.f⟩
def eps2 (z : Six) : Six := ⟨-z.a, z.b, z.c, -z.d, -z.e, z.f⟩
def eps3 (z : Six) : Six := ⟨z.a, -z.b, z.c, -z.d, z.e, -z.f⟩
def eps4 (z : Six) : Six := ⟨z.a, z.b, -z.c, z.d, -z.e, -z.f⟩

theorem inv1_mu1 (z : Six) : inv1 (mu1 z) = z := by
  ext <;> simp [inv1, mu1]
theorem mu1_inv1 (z : Six) : mu1 (inv1 z) = z := by
  ext <;> simp [inv1, mu1]
theorem inv2_mu2 (z : Six) : inv2 (mu2 z) = z := by
  ext <;> simp [inv2, mu2]
theorem mu2_inv2 (z : Six) : mu2 (inv2 z) = z := by
  ext <;> simp [inv2, mu2]
theorem inv3_mu3 (z : Six) : inv3 (mu3 z) = z := by
  ext <;> simp [inv3, mu3]
theorem mu3_inv3 (z : Six) : mu3 (inv3 z) = z := by
  ext <;> simp [inv3, mu3]

theorem braid12 (z : Six) : mu1 (mu2 (mu1 z)) = mu2 (mu1 (mu2 z)) := by
  ext <;> simp [mu1, mu2] <;> ring
theorem braid23 (z : Six) : mu2 (mu3 (mu2 z)) = mu3 (mu2 (mu3 z)) := by
  ext <;> dsimp [mu2, mu3] <;> ring
theorem braid13 (z : Six) : mu1 (mu3 z) = mu3 (mu1 z) := by
  ext <;> dsimp [mu1, mu3] <;> ring

theorem q1_mu1 (z : Six) : q1 (mu1 z) = q1 z := by unfold q1 mu1; ring
theorem q1_inv1 (z : Six) : q1 (inv1 z) = q1 z := by unfold q1 inv1; ring
theorem q1_mu2 (z : Six) : q1 (mu2 z) = q1 z := by unfold q1 mu2; ring
theorem q1_inv2 (z : Six) : q1 (inv2 z) = q1 z := by unfold q1 inv2; ring
theorem q1_mu3 (z : Six) : q1 (mu3 z) = q1 z := by unfold q1 mu3; ring
theorem q1_inv3 (z : Six) : q1 (inv3 z) = q1 z := by unfold q1 inv3; ring
theorem q2_mu1 (z : Six) : q2 (mu1 z) = q2 z := by unfold q2 mu1; ring
theorem q2_inv1 (z : Six) : q2 (inv1 z) = q2 z := by unfold q2 inv1; ring
theorem q2_mu2 (z : Six) : q2 (mu2 z) = q2 z := by unfold q2 mu2; ring
theorem q2_inv2 (z : Six) : q2 (inv2 z) = q2 z := by unfold q2 inv2; ring
theorem q2_mu3 (z : Six) : q2 (mu3 z) = q2 z := by unfold q2 mu3; ring
theorem q2_inv3 (z : Six) : q2 (inv3 z) = q2 z := by unfold q2 inv3; ring

theorem q1_eps1 (z : Six) : q1 (eps1 z) = q1 z := by unfold q1 eps1; ring
theorem q1_eps2 (z : Six) : q1 (eps2 z) = q1 z := by unfold q1 eps2; ring
theorem q1_eps3 (z : Six) : q1 (eps3 z) = q1 z := by unfold q1 eps3; ring
theorem q1_eps4 (z : Six) : q1 (eps4 z) = q1 z := by unfold q1 eps4; ring
theorem q2_eps1 (z : Six) : q2 (eps1 z) = -q2 z := by unfold q2 eps1; ring
theorem q2_eps2 (z : Six) : q2 (eps2 z) = -q2 z := by unfold q2 eps2; ring
theorem q2_eps3 (z : Six) : q2 (eps3 z) = -q2 z := by unfold q2 eps3; ring
theorem q2_eps4 (z : Six) : q2 (eps4 z) = -q2 z := by unfold q2 eps4; ring

theorem eps1_involution (z : Six) : eps1 (eps1 z) = z := by ext <;> simp [eps1]
theorem eps2_involution (z : Six) : eps2 (eps2 z) = z := by ext <;> simp [eps2]
theorem eps3_involution (z : Six) : eps3 (eps3 z) = z := by ext <;> simp [eps3]
theorem eps4_involution (z : Six) : eps4 (eps4 z) = z := by ext <;> simp [eps4]

theorem eps12_commute (z : Six) : eps1 (eps2 z) = eps2 (eps1 z) := by
  ext <;> simp [eps1, eps2]
theorem eps13_commute (z : Six) : eps1 (eps3 z) = eps3 (eps1 z) := by
  ext <;> simp [eps1, eps3]
theorem eps14_commute (z : Six) : eps1 (eps4 z) = eps4 (eps1 z) := by
  ext <;> simp [eps1, eps4]
theorem eps23_commute (z : Six) : eps2 (eps3 z) = eps3 (eps2 z) := by
  ext <;> simp [eps2, eps3]
theorem eps24_commute (z : Six) : eps2 (eps4 z) = eps4 (eps2 z) := by
  ext <;> simp [eps2, eps4]
theorem eps34_commute (z : Six) : eps3 (eps4 z) = eps4 (eps3 z) := by
  ext <;> simp [eps3, eps4]
theorem all_signs_trivial (z : Six) : eps4 (eps3 (eps2 (eps1 z))) = z := by
  ext <;> simp [eps1, eps2, eps3, eps4]

theorem mu1_eps1 (z : Six) : mu1 (eps1 z) = eps2 (mu1 z) := by
  ext <;> simp [mu1, eps1, eps2]
theorem mu1_eps2 (z : Six) : mu1 (eps2 z) = eps1 (mu1 z) := by
  ext <;> simp [mu1, eps1, eps2] <;> ring
theorem mu1_eps3 (z : Six) : mu1 (eps3 z) = eps3 (mu1 z) := by
  ext <;> dsimp [mu1, eps3] <;> ring
theorem mu1_eps4 (z : Six) : mu1 (eps4 z) = eps4 (mu1 z) := by
  ext <;> dsimp [mu1, eps4] <;> ring
theorem mu2_eps1 (z : Six) : mu2 (eps1 z) = eps1 (mu2 z) := by
  ext <;> dsimp [mu2, eps1] <;> ring
theorem mu2_eps2 (z : Six) : mu2 (eps2 z) = eps3 (mu2 z) := by
  ext <;> simp [mu2, eps2, eps3]
theorem mu2_eps3 (z : Six) : mu2 (eps3 z) = eps2 (mu2 z) := by
  ext <;> simp [mu2, eps2, eps3] <;> ring
theorem mu2_eps4 (z : Six) : mu2 (eps4 z) = eps4 (mu2 z) := by
  ext <;> dsimp [mu2, eps4] <;> ring
theorem mu3_eps1 (z : Six) : mu3 (eps1 z) = eps1 (mu3 z) := by
  ext <;> dsimp [mu3, eps1] <;> ring
theorem mu3_eps2 (z : Six) : mu3 (eps2 z) = eps2 (mu3 z) := by
  ext <;> dsimp [mu3, eps2] <;> ring
theorem mu3_eps3 (z : Six) : mu3 (eps3 z) = eps4 (mu3 z) := by
  ext <;> simp [mu3, eps3, eps4]
theorem mu3_eps4 (z : Six) : mu3 (eps4 z) = eps3 (mu3 z) := by
  ext <;> simp [mu3, eps3, eps4] <;> ring

inductive Generator where
  | m1 | m2 | m3 | i1 | i2 | i3 | s1 | s2 | s3 | s4
  deriving DecidableEq, Repr

def step : Generator → Six → Six
  | .m1 => mu1
  | .m2 => mu2
  | .m3 => mu3
  | .i1 => inv1
  | .i2 => inv2
  | .i3 => inv3
  | .s1 => eps1
  | .s2 => eps2
  | .s3 => eps3
  | .s4 => eps4

def inverseGenerator : Generator → Generator
  | .m1 => .i1
  | .m2 => .i2
  | .m3 => .i3
  | .i1 => .m1
  | .i2 => .m2
  | .i3 => .m3
  | .s1 => .s1
  | .s2 => .s2
  | .s3 => .s3
  | .s4 => .s4

theorem step_inverse (g : Generator) (z : Six) : step (inverseGenerator g) (step g z) = z := by
  cases g <;> simp [inverseGenerator, step, inv1_mu1, mu1_inv1, inv2_mu2,
    mu2_inv2, inv3_mu3, mu3_inv3, eps1_involution, eps2_involution,
    eps3_involution, eps4_involution]

def applyWord (z : Six) : List Generator → Six
  | [] => z
  | g :: gs => applyWord (step g z) gs

def Reachable (z z' : Six) : Prop := ∃ word, applyWord z word = z'

theorem step_q1 (g : Generator) (z : Six) : q1 (step g z) = q1 z := by
  cases g <;> simp [step, q1_mu1, q1_mu2, q1_mu3, q1_inv1, q1_inv2,
    q1_inv3, q1_eps1, q1_eps2, q1_eps3, q1_eps4]

theorem step_q2_sq (g : Generator) (z : Six) : q2 (step g z) ^ 2 = q2 z ^ 2 := by
  cases g <;> simp [step, q2_mu1, q2_mu2, q2_mu3, q2_inv1, q2_inv2,
    q2_inv3, q2_eps1, q2_eps2, q2_eps3, q2_eps4]

theorem applyWord_q1 (word : List Generator) (z : Six) : q1 (applyWord z word) = q1 z := by
  induction word generalizing z with
  | nil => rfl
  | cons g gs ih => exact (ih (step g z)).trans (step_q1 g z)

theorem applyWord_q2_sq (word : List Generator) (z : Six) :
    q2 (applyWord z word) ^ 2 = q2 z ^ 2 := by
  induction word generalizing z with
  | nil => rfl
  | cons g gs ih => exact (ih (step g z)).trans (step_q2_sq g z)

theorem step_preserves_solution (g : Generator) (z : Six) (hz : isSolution z) :
    isSolution (step g z) := by
  rcases hz with ⟨h1, h2⟩
  cases g <;> simp only [step, isSolution, q1_mu1, q1_mu2, q1_mu3,
    q1_inv1, q1_inv2, q1_inv3, q2_mu1, q2_mu2, q2_mu3,
    q2_inv1, q2_inv2, q2_inv3, q1_eps1, q1_eps2, q1_eps3,
    q1_eps4, q2_eps1, q2_eps2, q2_eps3, q2_eps4, neg_sq] <;> exact ⟨h1, h2⟩

theorem applyWord_preserves_solution (word : List Generator) (z : Six)
    (hz : isSolution z) : isSolution (applyWord z word) := by
  induction word generalizing z with
  | nil => exact hz
  | cons g gs ih => exact ih (step g z) (step_preserves_solution g z hz)

theorem applyWord_append (z : Six) (u v : List Generator) :
    applyWord z (u ++ v) = applyWord (applyWord z u) v := by
  induction u generalizing z with
  | nil => rfl
  | cons g gs ih => exact ih (step g z)

theorem reachable_refl (z : Six) : Reachable z z := ⟨[], rfl⟩
theorem reachable_trans {x y z : Six} (hxy : Reachable x y) (hyz : Reachable y z) :
    Reachable x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  refine ⟨u ++ v, ?_⟩
  rw [applyWord_append, hu, hv]

theorem applyWord_inverse (z : Six) (word : List Generator) :
    applyWord (applyWord z word) (word.reverse.map inverseGenerator) = z := by
  induction word generalizing z with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.reverse_cons, List.map_append, List.map_singleton, applyWord]
      rw [applyWord_append, ih]
      exact step_inverse g z

theorem reachable_symm {x y : Six} (h : Reachable x y) : Reachable y x := by
  rcases h with ⟨word, hw⟩
  refine ⟨word.reverse.map inverseGenerator, ?_⟩
  rw [← hw, applyWord_inverse]

theorem reachable_q1 {x y : Six} (h : Reachable x y) : q1 x = q1 y := by
  rcases h with ⟨word, hw⟩
  rw [← hw, applyWord_q1]

theorem reachable_q2_sq {x y : Six} (h : Reachable x y) : q2 x ^ 2 = q2 y ^ 2 := by
  rcases h with ⟨word, hw⟩
  rw [← hw, applyWord_q2_sq]

theorem reachable_equivalence : Equivalence Reachable :=
  ⟨reachable_refl, @reachable_symm, @reachable_trans⟩

def reachabilitySetoid : Setoid Six where
  r := Reachable
  iseqv := reachable_equivalence

theorem reachable_preserves_solution {x y : Six} (h : Reachable x y)
    (hx : isSolution x) : isSolution y := by
  rcases h with ⟨word, hw⟩
  rw [← hw]
  exact applyWord_preserves_solution word x hx

theorem reachable_solution_iff {x y : Six} (h : Reachable x y) :
    isSolution x ↔ isSolution y :=
  ⟨reachable_preserves_solution h, reachable_preserves_solution (reachable_symm h)⟩

def family (x y : ℤ) : Six := ⟨-x, -x, -2, 2, -y, -y⟩

theorem q1_family (x y : ℤ) : q1 (family x y) = 8 := by unfold q1 family; ring
theorem q2_family (x y : ℤ) : q2 (family x y) = -4 := by unfold q2 family; ring
theorem family_isSolution (x y : ℤ) : isSolution (family x y) := by
  simp [isSolution, q1_family, q2_family]

theorem family_swap (x y : ℤ) :
    applyWord (family x y) [.m1, .m2, .m3, .m2, .m1] = family y x := by
  ext <;> simp [applyWord, step, mu1, mu2, mu3, family] <;> ring

theorem family_reflection (x y : ℤ) :
    applyWord (family x y) [.m3, .m2, .m2, .m3, .s2, .s3] =
      family (x + 2 * y) (-y) := by
  ext <;> simp [applyWord, step, mu2, mu3, eps2, eps3, family] <;> ring

theorem family_negation (x y : ℤ) :
    applyWord (family x y) [.s2, .s3] = family (-x) (-y) := by
  ext <;> simp [applyWord, step, eps2, eps3, family]

theorem family_swap_reachable (x y : ℤ) : Reachable (family x y) (family y x) :=
  ⟨[.m1, .m2, .m3, .m2, .m1], family_swap x y⟩
theorem family_reflection_reachable (x y : ℤ) :
    Reachable (family x y) (family (x + 2 * y) (-y)) :=
  ⟨[.m3, .m2, .m2, .m3, .s2, .s3], family_reflection x y⟩
theorem family_negation_reachable (x y : ℤ) :
    Reachable (family x y) (family (-x) (-y)) :=
  ⟨[.s2, .s3], family_negation x y⟩

theorem kronecker_q2 (b c d e : ℤ) : q2 ⟨-2, b, c, d, e, 2⟩ = -4 - b * e + c * d := by
  unfold q2; ring
theorem kronecker_q1 (b c d e : ℤ) :
    q1 ⟨-2, b, c, d, e, 2⟩ = 8 + (b - c + d - e) ^ 2 + 2 * (b * e - c * d) := by
  unfold q1; ring

theorem kronecker_minus1 (b d : ℤ) :
    applyWord ⟨-2, b, b, d, d, 2⟩ [.i2, .i3] = family (-b) (-d) := by
  ext <;> simp [applyWord, step, inv2, inv3, family] <;> ring
theorem kronecker_minus2 (b c : ℤ) :
    applyWord ⟨-2, b, c, -b, -c, 2⟩ [.m2, .m1, .s2, .s4] = family b (-c) := by
  ext <;> simp [applyWord, step, mu1, mu2, eps2, eps4, family] <;> ring

theorem kronecker_minus_components (b c d e : ℤ)
    (h1 : q1 ⟨-2, b, c, d, e, 2⟩ = 8)
    (h2 : q2 ⟨-2, b, c, d, e, 2⟩ = -4) :
    (b = c ∧ e = d) ∨ (d = -b ∧ e = -c) := by
  rw [kronecker_q2] at h2
  have hprod : b * e = c * d := by linarith
  rw [kronecker_q1, hprod] at h1
  have hsum : b - c + d - e = 0 := by nlinarith [sq_nonneg (b - c + d - e)]
  have he : e = b - c + d := by omega
  rw [he] at hprod
  have hfactor : (b - c) * (b + d) = 0 := by nlinarith [hprod]
  rcases mul_eq_zero.mp hfactor with hbc | hbd
  · left
    exact ⟨by omega, by omega⟩
  · right
    exact ⟨by omega, by omega⟩

theorem kronecker_minus_reachable_family (b c d e : ℤ)
    (h1 : q1 ⟨-2, b, c, d, e, 2⟩ = 8)
    (h2 : q2 ⟨-2, b, c, d, e, 2⟩ = -4) :
    ∃ x y : ℤ, Reachable ⟨-2, b, c, d, e, 2⟩ (family x y) := by
  rcases kronecker_minus_components b c d e h1 h2 with ⟨hbc, hed⟩ | ⟨hdb, hec⟩
  · refine ⟨-b, -d, [.i2, .i3], ?_⟩
    simpa only [← hbc, hed] using kronecker_minus1 b d
  · refine ⟨b, -c, [.m2, .m1, .s2, .s4], ?_⟩
    simpa only [hdb, hec] using kronecker_minus2 b c

theorem kronecker_plus_components (b c d e : ℤ)
    (h1 : q1 ⟨-2, b, c, d, e, 2⟩ = 8)
    (h2 : q2 ⟨-2, b, c, d, e, 2⟩ = 4) :
    b * e - c * d = -8 ∧ (b - c + d - e = 4 ∨ b - c + d - e = -4) := by
  rw [kronecker_q2] at h2
  have hp : b * e - c * d = -8 := by linarith
  constructor
  · exact hp
  · rw [kronecker_q1, hp] at h1
    have hf : (b - c + d - e - 4) * (b - c + d - e + 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; omega
    · right; omega

def kroneckerPlus (u v B : ℤ) : Six :=
  ⟨-2, B, B - u, v - B, u + v - B - 4, 2⟩

theorem q2_kroneckerPlus (u v B : ℤ) :
    q2 (kroneckerPlus u v B) = 4 * B - u * v - 4 := by
  unfold q2 kroneckerPlus; ring

theorem q1_kroneckerPlus (u v B : ℤ) :
    q1 (kroneckerPlus u v B) = 24 + 2 * (u * v - 4 * B) := by
  unfold q1 kroneckerPlus; ring

theorem kroneckerPlus_isSolution (u v B : ℤ) (h : 4 * B = u * v + 8) :
    isSolution (kroneckerPlus u v B) := by
  constructor
  · rw [q1_kroneckerPlus, h]; ring
  · rw [q2_kroneckerPlus, h]; ring

theorem kroneckerPlus_translation_u (u v B : ℤ) :
    applyWord (kroneckerPlus u v B) [.m1, .s1, .s2] =
      kroneckerPlus (u + 4) v (B + v) := by
  ext <;> simp [applyWord, step, mu1, eps1, eps2, kroneckerPlus] <;> ring

theorem kroneckerPlus_translation_v (u v B : ℤ) :
    applyWord (kroneckerPlus u v B) [.m3] =
      kroneckerPlus u (v + 4) (B + u) := by
  ext <;> simp [applyWord, step, mu3, kroneckerPlus] <;> ring

theorem kroneckerPlus_translation_u_reachable (u v B : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus (u + 4) v (B + v)) :=
  ⟨[.m1, .s1, .s2], kroneckerPlus_translation_u u v B⟩
theorem kroneckerPlus_translation_v_reachable (u v B : ℤ) :
    Reachable (kroneckerPlus u v B) (kroneckerPlus u (v + 4) (B + u)) :=
  ⟨[.m3], kroneckerPlus_translation_v u v B⟩

/-! The eight concrete positive-component certificates of Appendix B. -/
theorem kronecker_plus_certificate_00 :
    applyWord ⟨-2, 2, 2, -2, -6, 2⟩ [.m1, .s4] = family 2 2 := by decide
theorem kronecker_plus_certificate_01 :
    applyWord ⟨-2, 2, 2, -1, -5, 2⟩
      [.m1, .m2, .m2, .m2, .i3, .s2, .s3, .s4] = family 1 (-2) := by decide
theorem kronecker_plus_certificate_02 :
    applyWord ⟨-2, 2, 2, 0, -4, 2⟩ [.m1, .m2, .i3, .s4] = family 0 2 := by decide
theorem kronecker_plus_certificate_03 :
    applyWord ⟨-2, 2, 2, 1, -3, 2⟩
      [.m1, .m2, .i3, .i3, .i3, .s2, .s3, .s4] = family 1 (-2) := by decide
theorem kronecker_plus_certificate_10 :
    applyWord ⟨-2, 2, 1, -2, -5, 2⟩ [.i2, .m1, .m1, .m1, .s2] = family 2 (-1) := by decide
theorem kronecker_plus_certificate_20 :
    applyWord ⟨-2, 2, 0, -2, -4, 2⟩ [.i2, .m1, .s2] = family 2 0 := by decide
theorem kronecker_plus_certificate_22 :
    applyWord ⟨-2, 3, 1, -1, -3, 2⟩ [.m2, .i1, .i3, .s3] = family 1 (-3) := by decide
theorem kronecker_plus_certificate_30 :
    applyWord ⟨-2, 2, -1, -2, -3, 2⟩ [.i2, .i2, .i2, .m1, .s2] = family 2 (-1) := by decide

def p3 : Six := ⟨4, 10, 20, 4, 10, 4⟩
def q3 : Six := ⟨5, 14, 40, 5, 16, 4⟩
def v5 : Six := ⟨5, 7, 25, 5, 22, 5⟩
def v22 : Six := ⟨7, 8, 18, 4, 13, 4⟩
def x72 : Six := ⟨-6, -7, -3, 3, 7, 6⟩

theorem p3_isSolution : isSolution p3 := by norm_num [isSolution, q1, q2, p3]
theorem q3_isSolution : isSolution q3 := by norm_num [isSolution, q1, q2, q3]
theorem v5_isSolution : isSolution v5 := by norm_num [isSolution, q1, q2, v5]
theorem v22_isSolution : isSolution v22 := by norm_num [isSolution, q1, q2, v22]
theorem x72_isSolution : isSolution x72 := by norm_num [isSolution, q1, q2, x72]

end SerreMarkov
