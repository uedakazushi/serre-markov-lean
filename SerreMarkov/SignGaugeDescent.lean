import SerreMarkov.NegativeDescent
import SerreMarkov.PositiveNormalization

/-! # Transfer descent through any exceptional-basis sign gauge

Braid moves swap the adjacent vertex signs. Sign moves commute with the
gauge. Consequently every signed-mutation word has exactly the same absolute
coordinate height before and after any initial vertex-sign change.
-/

namespace SerreMarkov.SignGaugeDescent

open PositiveNormalization NegativeDescent
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- The same diagonal sign action used in actual frame normalization. -/
abbrev diagonalSign (s : Fin 4 → ℤ) (z : Six) : Six := signedSix z s

/-- A braid move swaps the two adjacent basis signs; a sign move leaves
an existing gauge unchanged. -/
def moveSigns (g : Generator) (s : Fin 4 → ℤ) : Fin 4 → ℤ :=
  match g with
  | .m1 | .i1 => ![s 1,s 0,s 2,s 3]
  | .m2 | .i2 => ![s 0,s 2,s 1,s 3]
  | .m3 | .i3 => ![s 0,s 1,s 3,s 2]
  | .s1 | .s2 | .s3 | .s4 => s

theorem moveSigns_square (g : Generator) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) :
    ∀ i,(moveSigns g s i)^2=1 := by
  intro i
  cases g <;> fin_cases i <;> simp only [moveSigns]
  all_goals first | exact hs 0 | exact hs 1 | exact hs 2 | exact hs 3

/-- Exact polynomial gauge covariance of each of the ten actual moves. -/
theorem step_signedSix (g : Generator) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) (z : Six) :
    step g (signedSix z s) = signedSix (step g z) (moveSigns g s) := by
  cases g <;> ext <;>
    simp [step,mu1,inv1,mu2,inv2,mu3,inv3,eps1,eps2,eps3,eps4,signedSix,moveSigns]
  all_goals ring_nf
  all_goals simp [hs]

/-- Track the gauge while reading a mutation word in its actual order. -/
def wordSigns (s : Fin 4 → ℤ) : List Generator → Fin 4 → ℤ
  | [] => s
  | g::word => wordSigns (moveSigns g s) word

theorem wordSigns_square (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) (word : List Generator) :
    ∀ i,(wordSigns s word i)^2=1 := by
  induction word generalizing s with
  | nil => exact hs
  | cons g word ih => exact ih _ (moveSigns_square g s hs)

/-- Every word transports a vertex gauge without changing the braid word. -/
theorem applyWord_signedSix (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1)
    (z : Six) (word : List Generator) :
    applyWord (signedSix z s) word = signedSix (applyWord z word) (wordSigns s word) := by
  induction word generalizing s z with
  | nil => rfl
  | cons g word ih =>
    simp only [applyWord,wordSigns]
    rw [step_signedSix g s hs z]
    exact ih _ (moveSigns_square g s hs) _

private theorem sign_natAbs (a : ℤ) (h : a^2=1) : a.natAbs=1 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show a^2=(1:ℤ)^2 by simpa only [one_pow] using h) with h|h
  · rw [h]; rfl
  · rw [h]; rfl

private theorem sign_abs (a : ℤ) (h : a^2=1) : |a|=1 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show a^2=(1:ℤ)^2 by simpa only [one_pow] using h) with h|h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- All six absolute coordinate values are preserved by a vertex gauge. -/
theorem signedSix_abs (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) :
    |(signedSix z s).a|=|z.a| ∧ |(signedSix z s).b|=|z.b| ∧
    |(signedSix z s).c|=|z.c| ∧ |(signedSix z s).d|=|z.d| ∧
    |(signedSix z s).e|=|z.e| ∧ |(signedSix z s).f|=|z.f| := by
  simp [signedSix,abs_mul,sign_abs _ (hs 0),sign_abs _ (hs 1),
    sign_abs _ (hs 2),sign_abs _ (hs 3)]

theorem l1_signedSix (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) :
    l1 (signedSix z s)=l1 z := by
  simp [l1,signedSix,Int.natAbs_mul,sign_natAbs _ (hs 0),sign_natAbs _ (hs 1),
    sign_natAbs _ (hs 2),sign_natAbs _ (hs 3)]

/-- The intrinsic sign polynomial is also unchanged by every vertex gauge. -/
theorem negativeMarker_signedSix (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1) :
    negativeMarker (signedSix z s)=negativeMarker z := by
  dsimp only [negativeMarker,signedSix]
  ring_nf
  simp [hs]
  ring

/-- The height after the same word is independent of the initial gauge.
No bound on word length or restriction to braid generators is needed. -/
theorem l1_applyWord_signedSix (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1)
    (word : List Generator) :
    l1 (applyWord (signedSix z s) word)=l1 (applyWord z word) := by
  rw [applyWord_signedSix s hs]
  exact l1_signedSix _ _ (wordSigns_square s hs word)

/-- Strict descent on a gauged tuple transfers to the identical word on the
original tuple, so length and braid-membership restrictions are unchanged. -/
theorem descent_transfer (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1)
    (word : List Generator)
    (h : l1 (applyWord (signedSix z s) word) < l1 (signedSix z s)) :
    l1 (applyWord z word) < l1 z := by
  simpa only [l1_applyWord_signedSix z s hs word,l1_signedSix z s hs] using h

/-- Any desired word restriction transfers with the very same witness. -/
theorem restricted_descent_transfer (z : Six) (s : Fin 4 → ℤ) (hs : ∀ i,(s i)^2=1)
    (P : List Generator → Prop)
    (h : ∃ word, P word ∧ l1 (applyWord (signedSix z s) word)<l1 (signedSix z s)) :
    ∃ word, P word ∧ l1 (applyWord z word)<l1 z := by
  obtain ⟨word,hP,hdrop⟩ := h
  exact ⟨word,hP,descent_transfer z s hs word hdrop⟩

/-- Fix the first vertex and independently make the other first-row entries
nonnegative. This is an explicit gauge, rather than just a reachable tuple. -/
def firstRowSigns (z : Six) : Fin 4 → ℤ :=
  ![1,if 0≤z.a then 1 else -1,if 0≤z.b then 1 else -1,if 0≤z.c then 1 else -1]

theorem firstRowSigns_square (z : Six) : ∀ i,(firstRowSigns z i)^2=1 := by
  intro i
  fin_cases i <;> simp [firstRowSigns]

theorem firstRowSigns_normalizes (z : Six) :
    (signedSix z (firstRowSigns z)).a=|z.a| ∧
    (signedSix z (firstRowSigns z)).b=|z.b| ∧
    (signedSix z (firstRowSigns z)).c=|z.c| := by
  refine ⟨?_,?_,?_⟩
  · by_cases h : 0≤z.a
    · simp [signedSix,firstRowSigns,h,abs_of_nonneg h]
    · simp [signedSix,firstRowSigns,h,abs_of_nonpos (by omega : z.a≤0)]
  · by_cases h : 0≤z.b
    · simp [signedSix,firstRowSigns,h,abs_of_nonneg h]
    · simp [signedSix,firstRowSigns,h,abs_of_nonpos (by omega : z.b≤0)]
  · by_cases h : 0≤z.c
    · simp [signedSix,firstRowSigns,h,abs_of_nonneg h]
    · simp [signedSix,firstRowSigns,h,abs_of_nonpos (by omega : z.c≤0)]

/-- The first-row normalization retains an explicit gauge and its signs. -/
theorem first_row_abs_sign_gauge (z : Six) :
    ∃ s : Fin 4 → ℤ, (∀ i,(s i)^2=1) ∧
      (signedSix z s).a=|z.a| ∧ (signedSix z s).b=|z.b| ∧ (signedSix z s).c=|z.c| ∧
      Reachable z (signedSix z s) ∧ l1 (signedSix z s)=l1 z := by
  have h := firstRowSigns_normalizes z
  exact ⟨firstRowSigns z,firstRowSigns_square z,h.1,h.2.1,h.2.2,
    signedSix_reachable z _ (firstRowSigns_square z),l1_signedSix z _ (firstRowSigns_square z)⟩

end SerreMarkov.SignGaugeDescent
