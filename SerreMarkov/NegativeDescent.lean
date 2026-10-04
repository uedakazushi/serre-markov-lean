import SerreMarkov.KroneckerNormalize
import SerreMarkov.Repeated
import SerreMarkov.IntrinsicType

/-! # Integral reductions toward negative-side descent

These are universal arithmetic lemmas, not a bounded search and not an assumed
negative classification. In particular, this module does not assert the still
unproved global short-word descent principle.
-/

namespace SerreMarkov.NegativeDescent

set_option maxRecDepth 4000

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

def l1 (z : Six) : ℕ :=
  z.a.natAbs + z.b.natAbs + z.c.natAbs + z.d.natAbs + z.e.natAbs + z.f.natAbs

def integerL1 (z : Six) : ℤ :=
  |z.a| + |z.b| + |z.c| + |z.d| + |z.e| + |z.f|

/-- The explicit sum of the principal third symmetric minors. -/
def negativeMarker (z : Six) : ℤ :=
  32 + 2 * (z.a*z.b*z.d + z.a*z.c*z.e + z.b*z.c*z.f + z.d*z.e*z.f) -
    4 * (z.a^2 + z.b^2 + z.c^2 + z.d^2 + z.e^2 + z.f^2)

theorem negativeMarker_eq (z : Six) : negativeMarker z = IntrinsicSigns.thirdMinorSum z := rfl

theorem integerL1_cast (z : Six) : integerL1 z = (l1 z : ℤ) := by
  simp [integerL1, l1]

theorem l1_lt_iff (z w : Six) : l1 w < l1 z ↔ integerL1 w < integerL1 z := by
  rw [integerL1_cast, integerL1_cast]
  norm_cast

theorem l1_eps2 (z : Six) : l1 (eps2 z) = l1 z := by simp [l1, eps2]
theorem l1_eps3 (z : Six) : l1 (eps3 z) = l1 z := by simp [l1, eps3]
theorem l1_eps4 (z : Six) : l1 (eps4 z) = l1 z := by simp [l1, eps4]

theorem marker_eps2 (z : Six) : negativeMarker (eps2 z) = negativeMarker z := by
  dsimp [negativeMarker, eps2]
  ring
theorem marker_eps3 (z : Six) : negativeMarker (eps3 z) = negativeMarker z := by
  dsimp [negativeMarker, eps3]
  ring
theorem marker_eps4 (z : Six) : negativeMarker (eps4 z) = negativeMarker z := by
  dsimp [negativeMarker, eps4]
  ring

/-- Three independently chosen vertex signs make the first row nonnegative,
without changing the integer height or the negative-sign polynomial. -/
theorem first_row_sign_normalization (z : Six) :
    ∃ w : Six, Reachable z w ∧ 0 ≤ w.a ∧ 0 ≤ w.b ∧ 0 ≤ w.c ∧
      l1 w = l1 z ∧ negativeMarker w = negativeMarker z := by
  let z₁ := if 0 ≤ z.a then z else eps2 z
  have hr₁ : Reachable z z₁ := by
    by_cases h : 0 ≤ z.a
    · simpa [z₁, h] using reachable_refl z
    · exact ⟨[.s2], by simp [z₁, h, applyWord, step]⟩
  have ha₁ : 0 ≤ z₁.a := by
    by_cases h : 0 ≤ z.a <;> simp [z₁, h, eps2] <;> omega
  have hb₁ : z₁.b = z.b := by by_cases h : 0 ≤ z.a <;> simp [z₁, h, eps2]
  have hc₁ : z₁.c = z.c := by by_cases h : 0 ≤ z.a <;> simp [z₁, h, eps2]
  have hl₁ : l1 z₁ = l1 z := by
    by_cases h : 0 ≤ z.a <;> simp [z₁, h, l1_eps2]
  have hm₁ : negativeMarker z₁ = negativeMarker z := by
    by_cases h : 0 ≤ z.a <;> simp [z₁, h, marker_eps2]
  let z₂ := if 0 ≤ z₁.b then z₁ else eps3 z₁
  have hr₂ : Reachable z₁ z₂ := by
    by_cases h : 0 ≤ z₁.b
    · simpa [z₂, h] using reachable_refl z₁
    · exact ⟨[.s3], by simp [z₂, h, applyWord, step]⟩
  have ha₂ : 0 ≤ z₂.a := by
    by_cases h : 0 ≤ z₁.b <;> simpa [z₂, h, eps3] using ha₁
  have hb₂ : 0 ≤ z₂.b := by
    by_cases h : 0 ≤ z₁.b <;> simp [z₂, h, eps3] <;> omega
  have hc₂ : z₂.c = z₁.c := by by_cases h : 0 ≤ z₁.b <;> simp [z₂, h, eps3]
  have hl₂ : l1 z₂ = l1 z₁ := by
    by_cases h : 0 ≤ z₁.b <;> simp [z₂, h, l1_eps3]
  have hm₂ : negativeMarker z₂ = negativeMarker z₁ := by
    by_cases h : 0 ≤ z₁.b <;> simp [z₂, h, marker_eps3]
  let z₃ := if 0 ≤ z₂.c then z₂ else eps4 z₂
  have hr₃ : Reachable z₂ z₃ := by
    by_cases h : 0 ≤ z₂.c
    · simpa [z₃, h] using reachable_refl z₂
    · exact ⟨[.s4], by simp [z₃, h, applyWord, step]⟩
  have ha₃ : 0 ≤ z₃.a := by
    by_cases h : 0 ≤ z₂.c <;> simpa [z₃, h, eps4] using ha₂
  have hb₃ : 0 ≤ z₃.b := by
    by_cases h : 0 ≤ z₂.c <;> simpa [z₃, h, eps4] using hb₂
  have hc₃ : 0 ≤ z₃.c := by
    by_cases h : 0 ≤ z₂.c <;> simp [z₃, h, eps4] <;> omega
  have hl₃ : l1 z₃ = l1 z₂ := by
    by_cases h : 0 ≤ z₂.c <;> simp [z₃, h, l1_eps4]
  have hm₃ : negativeMarker z₃ = negativeMarker z₂ := by
    by_cases h : 0 ≤ z₂.c <;> simp [z₃, h, marker_eps4]
  exact ⟨z₃, reachable_trans (reachable_trans hr₁ hr₂) hr₃,
    ha₃, hb₃, hc₃, hl₃.trans (hl₂.trans hl₁), hm₃.trans (hm₂.trans hm₁)⟩

theorem mu1_drop_iff (z : Six) : l1 (mu1 z) < l1 z ↔
    |z.a*z.b-z.d| + |z.a*z.c-z.e| < |z.d| + |z.e| := by
  rw [l1_lt_iff]
  dsimp [integerL1, mu1]
  omega
theorem inv1_drop_iff (z : Six) : l1 (inv1 z) < l1 z ↔
    |z.a*z.d-z.b| + |z.a*z.e-z.c| < |z.b| + |z.c| := by
  rw [l1_lt_iff]
  dsimp [integerL1, inv1]
  omega
theorem mu2_drop_iff (z : Six) : l1 (mu2 z) < l1 z ↔
    |z.a*z.d-z.b| + |z.d*z.e-z.f| < |z.b| + |z.f| := by
  rw [l1_lt_iff]
  dsimp [integerL1, mu2]
  omega
theorem inv2_drop_iff (z : Six) : l1 (inv2 z) < l1 z ↔
    |z.b*z.d-z.a| + |z.d*z.f-z.e| < |z.a| + |z.e| := by
  rw [l1_lt_iff]
  dsimp [integerL1, inv2]
  omega
theorem mu3_drop_iff (z : Six) : l1 (mu3 z) < l1 z ↔
    |z.f*z.b-z.c| + |z.f*z.d-z.e| < |z.c| + |z.e| := by
  rw [l1_lt_iff]
  dsimp [integerL1, mu3]
  omega
theorem inv3_drop_iff (z : Six) : l1 (inv3 z) < l1 z ↔
    |z.f*z.c-z.b| + |z.f*z.e-z.d| < |z.b| + |z.d| := by
  rw [l1_lt_iff]
  dsimp [integerL1, inv3]
  omega

/-- A single reflected coordinate decreases exactly when this polynomial
is negative. This removes absolute values without numerical bounds. -/
theorem abs_reflection_lt_iff (x r : ℤ) :
    |x-r| < |r| ↔ x*(x-2*r) < 0 := by
  rw [← sq_lt_sq₀ (abs_nonneg (x-r)) (abs_nonneg r), sq_abs, sq_abs]
  constructor <;> intro h <;> nlinarith [h]

theorem abs_reflection_le_iff (x r : ℤ) :
    |x-r| ≤ |r| ↔ x*(x-2*r) ≤ 0 := by
  rw [← sq_le_sq₀ (abs_nonneg (x-r)) (abs_nonneg r), sq_abs, sq_abs]
  constructor <;> intro h <;> nlinarith [h]

theorem paired_reflection_drop (x y r s : ℤ)
    (hx : x*(x-2*r) < 0) (hy : y*(y-2*s) ≤ 0) :
    |x-r| + |y-s| < |r| + |s| := by
  exact add_lt_add_of_lt_of_le ((abs_reflection_lt_iff x r).mpr hx)
    ((abs_reflection_le_iff y s).mpr hy)

theorem mu1_drop_of_polynomials (z : Six)
    (hb : (z.a*z.b)*(z.a*z.b-2*z.d) < 0)
    (hc : (z.a*z.c)*(z.a*z.c-2*z.e) ≤ 0) : l1 (mu1 z) < l1 z :=
  (mu1_drop_iff z).mpr (paired_reflection_drop _ _ _ _ hb hc)

def signedValue (negative : Bool) (x : ℤ) : ℤ := if negative then -x else x

theorem signedValue_eq_abs (negative : Bool) (x : ℤ)
    (h : 0 ≤ signedValue negative x) : signedValue negative x = |x| := by
  cases negative with
  | false => simpa [signedValue] using (abs_of_nonneg h).symm
  | true =>
    have hx : x ≤ 0 := by simpa [signedValue] using neg_nonneg.mp h
    simpa [signedValue] using (abs_of_nonpos hx).symm

theorem signedValue_witness (x : ℤ) :
    ∃ negative : Bool, 0 ≤ signedValue negative x ∧ signedValue negative x = |x| := by
  by_cases hx : 0 ≤ x
  · refine ⟨false, ?_, ?_⟩
    · simpa [signedValue] using hx
    · simp [signedValue, abs_of_nonneg hx]
  · refine ⟨true, ?_, ?_⟩
    · simp [signedValue]
      omega
    · simp [signedValue, abs_of_nonpos (by omega : x ≤ 0)]

/-- Sixteen sign choices, each consisting solely of polynomial inequalities.
No absolute value or bounded coordinate search occurs in this predicate. -/
def PairLowerPolynomial (r s t u : ℤ) : Prop :=
  ∃ er es et eu : Bool,
    0 ≤ signedValue er r ∧ 0 ≤ signedValue es s ∧
    0 ≤ signedValue et t ∧ 0 ≤ signedValue eu u ∧
    signedValue er r + signedValue es s < signedValue et t + signedValue eu u

theorem pair_lower_polynomial_iff (r s t u : ℤ) :
    PairLowerPolynomial r s t u ↔ |r| + |s| < |t| + |u| := by
  constructor
  · rintro ⟨er,es,et,eu,hr,hs,ht,hu,hlt⟩
    simpa only [signedValue_eq_abs er r hr, signedValue_eq_abs es s hs,
      signedValue_eq_abs et t ht, signedValue_eq_abs eu u hu] using hlt
  · intro hlt
    obtain ⟨er,hr,her⟩ := signedValue_witness r
    obtain ⟨es,hs,hes⟩ := signedValue_witness s
    obtain ⟨et,ht,het⟩ := signedValue_witness t
    obtain ⟨eu,hu,heu⟩ := signedValue_witness u
    refine ⟨er,es,et,eu,hr,hs,ht,hu,?_⟩
    simpa only [her,hes,het,heu] using hlt

def OneStepDrop (z : Six) : Prop :=
  l1 (mu1 z) < l1 z ∨ l1 (inv1 z) < l1 z ∨
  l1 (mu2 z) < l1 z ∨ l1 (inv2 z) < l1 z ∨
  l1 (mu3 z) < l1 z ∨ l1 (inv3 z) < l1 z

/-- Exact universal reduction of one-step descent to six groups of sixteen
polynomial sign cases. This is an equivalence, not merely a sufficient test. -/
theorem one_step_drop_polynomial_iff (z : Six) : OneStepDrop z ↔
    PairLowerPolynomial (z.a*z.b-z.d) (z.a*z.c-z.e) z.d z.e ∨
    PairLowerPolynomial (z.a*z.d-z.b) (z.a*z.e-z.c) z.b z.c ∨
    PairLowerPolynomial (z.a*z.d-z.b) (z.d*z.e-z.f) z.b z.f ∨
    PairLowerPolynomial (z.b*z.d-z.a) (z.d*z.f-z.e) z.a z.e ∨
    PairLowerPolynomial (z.f*z.b-z.c) (z.f*z.d-z.e) z.c z.e ∨
    PairLowerPolynomial (z.f*z.c-z.b) (z.f*z.e-z.d) z.b z.d := by
  simp only [OneStepDrop, mu1_drop_iff, inv1_drop_iff, mu2_drop_iff,
    inv2_drop_iff, mu3_drop_iff, inv3_drop_iff, pair_lower_polynomial_iff]

abbrev SignPattern := Fin 6 → Bool

def CorrectSigns (z : Six) (e : SignPattern) : Prop :=
  0 ≤ signedValue (e 0) z.a ∧ 0 ≤ signedValue (e 1) z.b ∧
  0 ≤ signedValue (e 2) z.c ∧ 0 ≤ signedValue (e 3) z.d ∧
  0 ≤ signedValue (e 4) z.e ∧ 0 ≤ signedValue (e 5) z.f

def signedL1 (z : Six) (e : SignPattern) : ℤ :=
  signedValue (e 0) z.a + signedValue (e 1) z.b + signedValue (e 2) z.c +
    signedValue (e 3) z.d + signedValue (e 4) z.e + signedValue (e 5) z.f

theorem correctSigns_exists (z : Six) : ∃ e : SignPattern, CorrectSigns z e := by
  obtain ⟨ea,ha,_⟩ := signedValue_witness z.a
  obtain ⟨eb,hb,_⟩ := signedValue_witness z.b
  obtain ⟨ec,hc,_⟩ := signedValue_witness z.c
  obtain ⟨ed,hd,_⟩ := signedValue_witness z.d
  obtain ⟨ee,he,_⟩ := signedValue_witness z.e
  obtain ⟨ef,hf,_⟩ := signedValue_witness z.f
  exact ⟨![ea,eb,ec,ed,ee,ef],ha,hb,hc,hd,he,hf⟩

theorem signedL1_eq (z : Six) (e : SignPattern) (h : CorrectSigns z e) :
    signedL1 z e = integerL1 z := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := h
  simp only [signedL1, integerL1, signedValue_eq_abs _ _ ha,
    signedValue_eq_abs _ _ hb, signedValue_eq_abs _ _ hc,
    signedValue_eq_abs _ _ hd, signedValue_eq_abs _ _ he, signedValue_eq_abs _ _ hf]

/-- A finite choice of twelve signs gives an exact polynomial formula for
the strict comparison of the six-coordinate heights. -/
def L1LowerPolynomial (z w : Six) : Prop :=
  ∃ ez ew : SignPattern, CorrectSigns z ez ∧ CorrectSigns w ew ∧
    signedL1 w ew < signedL1 z ez

theorem l1_lower_polynomial_iff (z w : Six) :
    L1LowerPolynomial z w ↔ l1 w < l1 z := by
  rw [l1_lt_iff]
  constructor
  · rintro ⟨ez,ew,hz,hw,hlt⟩
    simpa only [signedL1_eq z ez hz, signedL1_eq w ew hw] using hlt
  · intro hlt
    obtain ⟨ez,hz⟩ := correctSigns_exists z
    obtain ⟨ew,hw⟩ := correctSigns_exists w
    refine ⟨ez,ew,hz,hw,?_⟩
    simpa only [signedL1_eq z ez hz, signedL1_eq w ew hw] using hlt

/-- Exact conic eliminant at an adjacent inner product equal to two. -/
theorem edge_two_q1_identity (b c d e f : ℤ) :
    q1 ⟨2,b,c,d,e,f⟩ - 8 =
      (b-d)^2 + (c-e)^2 - f*(b-d)*(c-e) - f^2 +
        f*q2 ⟨2,b,c,d,e,f⟩ - 4 := by
  dsimp [q1, q2]
  ring

theorem edge_two_conic_plus (b c d e f : ℤ)
    (h1 : q1 ⟨2,b,c,d,e,f⟩ = 8) (h2 : q2 ⟨2,b,c,d,e,f⟩ = 4) :
    (b-d)^2 + (c-e)^2 - f*(b-d)*(c-e) = (f-2)^2 := by
  have h := edge_two_q1_identity b c d e f
  rw [h1,h2] at h
  nlinarith [h]

theorem edge_two_conic_minus (b c d e f : ℤ)
    (h1 : q1 ⟨2,b,c,d,e,f⟩ = 8) (h2 : q2 ⟨2,b,c,d,e,f⟩ = -4) :
    (b-d)^2 + (c-e)^2 - f*(b-d)*(c-e) = (f+2)^2 := by
  have h := edge_two_q1_identity b c d e f
  rw [h1,h2] at h
  nlinarith [h]

/-- Two endpoint inner products of absolute value two already reduce to the
fully formalized two-Kronecker slice, with no extra sign or height hypothesis. -/
theorem endpoint_two_reachable_family (z : Six) (hz : isSolution z)
    (ha : z.a = 2 ∨ z.a = -2) (hf : z.f = 2 ∨ z.f = -2) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  have minus_plus (w : Six) (hw : isSolution w) (hwa : w.a = -2) (hwf : w.f = 2) :
      ∃ x y : ℤ, Reachable w (family x y) := by
    have heq : w = ⟨-2,w.b,w.c,w.d,w.e,2⟩ := by ext <;> simp [hwa,hwf]
    rw [heq] at hw ⊢
    exact kronecker_slice_reachable_family w.b w.c w.d w.e hw.1 hw.2
  rcases ha with ha | ha <;> rcases hf with hf | hf
  · have hr : Reachable z (eps1 z) := ⟨[.s1],rfl⟩
    obtain ⟨x,y,hxy⟩ := minus_plus (eps1 z) (reachable_preserves_solution hr hz)
      (by simp [eps1,ha]) (by simp [eps1,hf])
    exact ⟨x,y,reachable_trans hr hxy⟩
  · have hr : Reachable z (eps4 (eps1 z)) := ⟨[.s1,.s4],rfl⟩
    obtain ⟨x,y,hxy⟩ := minus_plus (eps4 (eps1 z)) (reachable_preserves_solution hr hz)
      (by simp [eps1,eps4,ha]) (by simp [eps1,eps4,hf])
    exact ⟨x,y,reachable_trans hr hxy⟩
  · exact minus_plus z hz ha hf
  · have hr : Reachable z (eps4 z) := ⟨[.s4],rfl⟩
    obtain ⟨x,y,hxy⟩ := minus_plus (eps4 z) (reachable_preserves_solution hr hz)
      (by simp [eps4,ha]) (by simp [eps4,hf])
    exact ⟨x,y,reachable_trans hr hxy⟩

def braidMoves : List Generator := [.m1,.i1,.m2,.i2,.m3,.i3]

/-- Every braid word of length at most `n`, with both orientations allowed. -/
def braidWords : ℕ → List (List Generator)
  | 0 => [[]]
  | n+1 => [] :: (braidMoves.flatMap fun g => (braidWords n).map (g :: ·))

theorem braidWords_three_count : (braidWords 3).length = 259 := by decide

theorem mem_braidWords_iff (n : ℕ) (word : List Generator) :
    word ∈ braidWords n ↔ word.length ≤ n ∧ ∀ g ∈ word, g ∈ braidMoves := by
  induction n generalizing word with
  | zero =>
    cases word with
    | nil => simp [braidWords]
    | cons g tail => simp [braidWords]
  | succ n ih =>
    cases word with
    | nil => simp [braidWords]
    | cons g tail =>
      simp only [braidWords, List.mem_cons, List.cons_ne_nil, false_or,
        List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨g',hg',tail',htail',heq⟩
        have he : g' = g ∧ tail' = tail := List.cons.inj heq
        have heg := he.1
        have het := he.2
        subst g'
        subst tail'
        have ht := (ih tail).mp htail'
        refine ⟨by simpa using Nat.succ_le_succ ht.1, ?_⟩
        intro h hh
        rcases hh with rfl | hh
        · exact hg'
        · exact ht.2 h hh
      · rintro ⟨hlen,hall⟩
        refine ⟨g,hall g (by simp),tail,?_,rfl⟩
        apply (ih tail).mpr
        refine ⟨by simpa using hlen,?_⟩
        intro h hh
        exact hall h (Or.inr hh)

/-- The twelve explicit coordinate alternatives for equal or opposite columns
are exactly the stopping conditions used in `Repeated.lean`. -/
def NoRepeatedColumns (z : Six) : Prop :=
  ¬ PositiveRepeatedColumns z ∧ ¬ NegativeRepeatedColumns z

private theorem repeated_coordinate_pair (z : Six)
    (h : PositiveRepeatedColumns z ∨ NegativeRepeatedColumns z) :
    ∃ i j : Fin 4, i ≠ j ∧
      ((∀ k, symmetricForm z k i = symmetricForm z k j) ∨
       (∀ k, symmetricForm z k i = -symmetricForm z k j)) := by
  rcases h with h | h
  · rcases h with ⟨ha,hb,hc⟩ | ⟨hb,ha,hc⟩ | ⟨hc,ha,hb⟩ |
      ⟨hd,ha,he⟩ | ⟨he,ha,hd⟩ | ⟨hf,hb,hd⟩
    · refine ⟨0,1,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨0,2,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨0,3,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨1,2,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hd,he]
    · refine ⟨1,3,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hd,he]
    · refine ⟨2,3,by decide,Or.inl ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,hb,hd,hf]
  · rcases h with ⟨ha,hb,hc⟩ | ⟨hb,ha,hc⟩ | ⟨hc,ha,hb⟩ |
      ⟨hd,ha,he⟩ | ⟨he,ha,hd⟩ | ⟨hf,hb,hd⟩
    · refine ⟨0,1,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨0,2,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨0,3,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hb,hc]
    · refine ⟨1,2,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hd,he]
    · refine ⟨1,3,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,ha,hd,he]
    · refine ⟨2,3,by decide,Or.inr ?_⟩
      intro k; fin_cases k <;> simp [symmetricForm,gram,hb,hd,hf]

private theorem repeated_pair_coordinates (z : Six) (i j : Fin 4) (hij : i < j)
    (hcols : (∀ k, symmetricForm z k i = symmetricForm z k j) ∨
      (∀ k, symmetricForm z k i = -symmetricForm z k j)) :
    PositiveRepeatedColumns z ∨ NegativeRepeatedColumns z := by
  rcases hcols with hcols | hcols
  all_goals
    have h0 := hcols 0
    have h1 := hcols 1
    have h2 := hcols 2
    have h3 := hcols 3
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals
      simp [symmetricForm,gram] at h0 h1 h2 h3
      simp only [PositiveRepeatedColumns,NegativeRepeatedColumns]
      aesop

/-- The polynomial stopping conditions are equivalent to the literal absence
of every equal or opposite pair of symmetric-form columns. -/
theorem noRepeatedColumns_iff (z : Six) : NoRepeatedColumns z ↔
    ∀ i j : Fin 4, i ≠ j →
      ¬ ((∀ k, symmetricForm z k i = symmetricForm z k j) ∨
         (∀ k, symmetricForm z k i = -symmetricForm z k j)) := by
  constructor
  · rintro ⟨hp,hm⟩ i j hne hcols
    have hc : PositiveRepeatedColumns z ∨ NegativeRepeatedColumns z := by
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact repeated_pair_coordinates z i j hij hcols
      · apply repeated_pair_coordinates z j i hji
        rcases hcols with h | h
        · exact Or.inl (fun k => (h k).symm)
        · apply Or.inr
          intro k
          have hk := h k
          omega
    exact hc.elim hp hm
  · intro hnone
    constructor
    · intro hp
      obtain ⟨i,j,hne,hcols⟩ := repeated_coordinate_pair z (Or.inl hp)
      exact hnone i j hne hcols
    · intro hm
      obtain ⟨i,j,hne,hcols⟩ := repeated_coordinate_pair z (Or.inr hm)
      exact hnone i j hne hcols

/-- The remaining universal arithmetic cutpoint. This is a public hypothesis,
not an axiom or a theorem asserted by this module. -/
def LocalDescentProperty : Prop :=
  ∀ z : Six, isSolution z → IntrinsicSigns.thirdMinorSum z < 0 →
    NoRepeatedColumns z → ∃ word : List Generator,
      word.length ≤ 3 ∧ (∀ g ∈ word, g ∈ braidMoves) ∧
        l1 (applyWord z word) < l1 z

theorem local_descent_finite_word_iff : LocalDescentProperty ↔
    ∀ z : Six, isSolution z → IntrinsicSigns.thirdMinorSum z < 0 →
      NoRepeatedColumns z → ∃ word ∈ braidWords 3,
        l1 (applyWord z word) < l1 z := by
  constructor
  · intro h z hz hn hnr
    obtain ⟨word,hlen,hbraid,hdrop⟩ := h z hz hn hnr
    exact ⟨word,(mem_braidWords_iff 3 word).mpr ⟨hlen,hbraid⟩,hdrop⟩
  · intro h z hz hn hnr
    obtain ⟨word,hw,hdrop⟩ := h z hz hn hnr
    obtain ⟨hlen,hbraid⟩ := (mem_braidWords_iff 3 word).mp hw
    exact ⟨word,hlen,hbraid,hdrop⟩

/-- The unproved global descent assertion is exactly an unbounded integer
statement over 259 polynomial word choices and two finite sign patterns.
There is no coordinate bound or absolute value in its concluding formula. -/
theorem local_descent_polynomial_iff : LocalDescentProperty ↔
    ∀ z : Six, isSolution z → IntrinsicSigns.thirdMinorSum z < 0 →
      NoRepeatedColumns z → ∃ word ∈ braidWords 3,
        L1LowerPolynomial z (applyWord z word) := by
  rw [local_descent_finite_word_iff]
  simp only [l1_lower_polynomial_iff]

/-- Genuine well-founded induction reduces negative family surjectivity to
the explicitly exposed local integer inequality. The local inequality itself
remains unproved; no geometric or classification input is hidden here. -/
theorem local_descent_implies_negative_family_surjectivity
    (hlocal : LocalDescentProperty) (z : Six) (hz : isSolution z)
    (hneg : IntrinsicSigns.thirdMinorSum z < 0) :
    ∃ x y : ℤ, Reachable z (family x y) := by
  suffices hind : ∀ n : ℕ, ∀ z : Six, l1 z = n → isSolution z →
      IntrinsicSigns.thirdMinorSum z < 0 → ∃ x y : ℤ, Reachable z (family x y) by
    exact hind (l1 z) z rfl hz hneg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hn hz hneg
    by_cases hp : PositiveRepeatedColumns z
    · exact positive_repeated_columns_reachable_family z hz hp
    by_cases hm : NegativeRepeatedColumns z
    · exact negative_repeated_columns_reachable_family z hz hm
    obtain ⟨word,_,_,hdrop⟩ := hlocal z hz hneg ⟨hp,hm⟩
    let w := applyWord z word
    have hr : Reachable z w := ⟨word,rfl⟩
    have hw : isSolution w := reachable_preserves_solution hr hz
    have hk : intrinsicKind z = .negative := (intrinsicKind_negative_iff z hz).mpr hneg
    have hkw : intrinsicKind w = .negative := by
      rw [← reachable_intrinsicKind hz hr]
      exact hk
    have hwneg := (intrinsicKind_negative_iff w hw).mp hkw
    obtain ⟨x,y,hxy⟩ := ih (l1 w) (by change l1 (applyWord z word) < n; omega)
      w rfl hw hwneg
    exact ⟨x,y,reachable_trans hr hxy⟩

end SerreMarkov.NegativeDescent
