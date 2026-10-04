import Mathlib.Data.List.Chain
import Mathlib.Data.List.Palindrome
import Mathlib.Tactic

/-! # Reduced words in a free product of involutions

Letters cancel precisely when two equal letters are adjacent. The stack
algorithm gives a unique reduced normal form, and a nonempty reduced word
whose square reduces to the empty word is a conjugate of one letter.
-/

namespace SerreMarkov.UniversalWord

variable {α : Type*} [DecidableEq α]

/-- A word is reduced if its adjacent letters are distinct. -/
def Reduced (w : List α) : Prop := w.IsChain (· ≠ ·)

@[simp] theorem reduced_nil : Reduced ([] : List α) := List.isChain_nil
@[simp] theorem reduced_singleton (a : α) : Reduced [a] := List.isChain_singleton a

@[simp] theorem reduced_cons_cons (a b : α) (w : List α) :
    Reduced (a::b::w) ↔ a ≠ b ∧ Reduced (b::w) := List.isChain_cons_cons

theorem Reduced.tail {a : α} {w : List α} (h : Reduced (a::w)) : Reduced w := by
  exact List.IsChain.tail h

theorem Reduced.reverse {w : List α} (h : Reduced w) : Reduced w.reverse := by
  apply List.isChain_reverse.mpr
  simpa only [Reduced, Function.flip_def, ne_comm] using h

/-- Cancel the stack head if it equals the incoming letter. -/
def push (a : α) : List α → List α
  | [] => [a]
  | b::w => if a=b then w else a::b::w

theorem push_reduced (a : α) {w : List α} (h : Reduced w) : Reduced (push a w) := by
  cases w with
  | nil => exact reduced_singleton a
  | cons b w =>
    by_cases hab : a=b
    · simpa only [push, if_pos hab] using h.tail
    · simpa only [push, if_neg hab, reduced_cons_cons] using And.intro hab h

theorem push_involutive (a : α) {w : List α} (h : Reduced w) :
    push a (push a w) = w := by
  cases w with
  | nil => simp [push]
  | cons b w =>
    by_cases hab : a=b
    · subst b
      cases w with
      | nil => simp [push]
      | cons c w =>
        have hac : a ≠ c := (reduced_cons_cons a c w).mp h |>.1
        simp [push, hac]
    · simp [push, hab]

abbrev NormalForm (α : Type*) := {w : List α // Reduced w}

def pushNF (a : α) (w : NormalForm α) : NormalForm α :=
  ⟨push a w.val, push_reduced a w.property⟩

@[simp] theorem pushNF_involutive (a : α) (w : NormalForm α) :
    pushNF a (pushNF a w) = w := Subtype.ext (push_involutive a w.property)

def emptyNF : NormalForm α := ⟨[],reduced_nil⟩

/-- Read a word from the right onto a reduced stack. -/
def act (w : List α) (s : NormalForm α) : NormalForm α :=
  w.foldr pushNF s

@[simp] theorem act_nil (s : NormalForm α) : act [] s = s := rfl
@[simp] theorem act_cons (a : α) (w : List α) (s : NormalForm α) :
    act (a::w) s = pushNF a (act w s) := rfl

theorem act_append (u v : List α) (s : NormalForm α) :
    act (u++v) s = act u (act v s) := by simp [act, List.foldr_append]

@[simp] theorem act_reverse_cancel (w : List α) (s : NormalForm α) :
    act w.reverse (act w s) = s := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.reverse_cons, act_append, act_cons, act_cons, act_nil,
      pushNF_involutive, ih]

@[simp] theorem act_cancel_reverse (w : List α) (s : NormalForm α) :
    act w (act w.reverse s) = s := by
  simpa only [List.reverse_reverse] using act_reverse_cancel w.reverse s

/-- The computable stack normal form. -/
def reduce (w : List α) : List α := (act w emptyNF).val

@[simp] theorem reduce_nil : reduce ([] : List α) = [] := rfl
@[simp] theorem reduce_cons (a : α) (w : List α) :
    reduce (a::w) = push a (reduce w) := rfl

@[simp] theorem reduce_reduced (w : List α) : Reduced (reduce w) := (act w emptyNF).property

@[simp] theorem Reduced.reduce_eq {w : List α} (h : Reduced w) : reduce w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [reduce_cons, ih h.tail]
    cases w with
    | nil => rfl
    | cons b w =>
      have hab : a ≠ b := (reduced_cons_cons a b w).mp h |>.1
      simp [push, hab]

@[simp] theorem reduce_reduce (w : List α) : reduce (reduce w) = reduce w :=
  (reduce_reduced w).reduce_eq

/-- Adjacent equal letters have the same action as the empty word. -/
@[simp] theorem act_repeat (a : α) (w : List α) (s : NormalForm α) :
    act (a::a::w) s = act w s := by simp

/-- Normalization preserves the action on every reduced stack. -/
theorem act_reduce (w : List α) (s : NormalForm α) : act (reduce w) s = act w s := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [reduce_cons, act_cons, ← ih]
    cases hw : reduce w with
    | nil => simp [push]
    | cons b t =>
      by_cases hab : a=b
      · subst b
        simp [push]
      · simp [push, hab]

/-- Adjacent-repeat cancellation in an arbitrary word context. -/
@[simp] theorem reduce_cancel_adjacent (u : List α) (a : α) (v : List α) :
    reduce (u ++ a::a::v) = reduce (u++v) := by
  change (act (u ++ a::a::v) emptyNF).val = (act (u++v) emptyNF).val
  rw [act_append, act_append, act_repeat]

/-- The normal forms are exactly the fixed points of normalization. -/
theorem reduced_iff_reduce_eq (w : List α) : Reduced w ↔ reduce w = w := by
  constructor
  · exact Reduced.reduce_eq
  · intro h
    rw [← h]
    exact reduce_reduced w

/-- Normalization commutes with reversal. -/
@[simp] theorem reduce_reverse (w : List α) : reduce w.reverse = (reduce w).reverse := by
  have he : act (reduce w) (act w.reverse emptyNF) = emptyNF := by
    rw [act_reduce, act_cancel_reverse]
  have hr := congrArg (act (reduce w).reverse) he
  have hv : reduce w.reverse = reduce (reduce w).reverse := by
    exact congrArg Subtype.val (by simpa only [act_reverse_cancel] using hr)
  exact hv.trans (reduce_reduced w).reverse.reduce_eq

/-- Stack multiplication depends only on the two reduced normal forms. -/
theorem reduce_append_reduce (u v : List α) :
    reduce (reduce u ++ reduce v) = reduce (u++v) := by
  change (act (reduce u ++ reduce v) emptyNF).val = (act (u++v) emptyNF).val
  rw [act_append, act_append, act_reduce, act_reduce]

/-- A normalized concatenation is empty exactly when its normalized factors
are reverse words. -/
theorem reduce_append_eq_nil_iff (u v : List α) :
    reduce (u++v) = [] ↔ reduce u = (reduce v).reverse := by
  constructor
  · intro h
    have hn : act u (act v emptyNF) = emptyNF := by
      apply Subtype.ext
      simpa only [← act_append, reduce, emptyNF] using h
    have hv : act v emptyNF = act u.reverse emptyNF := by
      have hh := congrArg (act u.reverse) hn
      simpa only [act_reverse_cancel] using hh
    have hc : reduce v = reduce u.reverse := congrArg Subtype.val hv
    rw [reduce_reverse] at hc
    simpa only [List.reverse_reverse] using (congrArg List.reverse hc).symm
  · intro h
    rw [← reduce_append_reduce, h]
    unfold reduce
    rw [act_append, act_reverse_cancel]
    rfl

/-- A reduced square-empty word is a palindrome. -/
theorem reduced_square_palindrome {w : List α} (hw : Reduced w)
    (h : reduce (w++w) = []) : List.Palindrome w := by
  apply List.Palindrome.of_reverse_eq
  have he := (reduce_append_eq_nil_iff w w).mp h
  simpa only [hw.reduce_eq] using he.symm

/-- A nonempty reduced palindrome has one central letter. -/
theorem reduced_palindrome_conjugate {w : List α} (hw : Reduced w)
    (hp : List.Palindrome w) (hn : w ≠ []) :
    ∃ (pref : List α) (i : α), w = pref ++ [i] ++ pref.reverse := by
  induction hp with
  | nil => exact False.elim (hn rfl)
  | singleton i => exact ⟨[],i,by simp⟩
  | @cons_concat a w hp ih =>
    by_cases hnil : w = []
    · subst w
      have haa : a ≠ a := (reduced_cons_cons a a []).mp hw |>.1
      exact False.elim (haa rfl)
    · have hmiddle : Reduced w := List.IsChain.left_of_append hw.tail
      rcases ih hmiddle hnil with ⟨pref,i,he⟩
      refine ⟨a::pref,i,?_⟩
      simp only [he, List.reverse_cons, List.cons_append, List.append_assoc]

/-- The order-two normal-form theorem: every nontrivial reduced word whose
square is empty is a conjugate of a central generator. -/
theorem reduced_square_conjugate {w : List α} (hw : Reduced w)
    (hn : w ≠ []) (hsquare : reduce (w++w) = []) :
    ∃ (pref : List α) (i : α), w = pref ++ [i] ++ pref.reverse :=
  reduced_palindrome_conjugate hw (reduced_square_palindrome hw hsquare) hn

/-- The order-two conclusion for any word, expressed in its normal form. -/
theorem normalized_square_conjugate (w : List α) (hn : reduce w ≠ [])
    (hsquare : reduce (w++w) = []) :
    ∃ (pref : List α) (i : α), reduce w = pref ++ [i] ++ pref.reverse := by
  apply reduced_square_conjugate (reduce_reduced w) hn
  rw [reduce_append_reduce]
  exact hsquare

/-- Conversely, a conjugated letter has square equal to the empty normal form. -/
theorem conjugate_square (pref : List α) (i : α) :
    reduce ((pref ++ [i] ++ pref.reverse) ++ (pref ++ [i] ++ pref.reverse)) = [] := by
  apply (reduce_append_eq_nil_iff _ _).mpr
  rw [← reduce_reverse]
  congr 1
  simp [List.reverse_append, List.append_assoc]

/-- Equal normal forms are precisely equal actions on reduced stacks. This
certifies uniqueness of the stack normal form. -/
theorem reduce_eq_iff_act_eq (u v : List α) :
    reduce u = reduce v ↔ ∀ s : NormalForm α, act u s = act v s := by
  constructor
  · intro h s
    rw [← act_reduce u, ← act_reduce v, h]
  · intro h
    exact congrArg Subtype.val (h emptyNF)

section Evaluation

variable {S : Type*} (f : α → S → S) (hf : ∀ a, Function.Involutive (f a))
include hf

/-- A single stack operation preserves every action by involutive letters. -/
theorem foldr_push (a : α) (w : List α) (s : S) :
    (push a w).foldr f s = f a (w.foldr f s) := by
  cases w with
  | nil => rfl
  | cons b w =>
    by_cases hab : a=b
    · subst b
      simpa only [push, if_pos rfl, List.foldr_cons] using (hf a (w.foldr f s)).symm
    · simp only [push, if_neg hab, List.foldr_cons]

/-- Normalization preserves evaluation of a word from right to left. -/
theorem foldr_reduce (w : List α) (s : S) :
    (reduce w).foldr f s = w.foldr f s := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [reduce_cons, foldr_push f hf, List.foldr_cons, ih]

/-- Normalization preserves evaluation with the first letter acting first,
matching the fold-left convention of the reflection-word application. -/
theorem foldl_reduce (w : List α) (s : S) :
    (reduce w).foldl (fun s a => f a s) s = w.foldl (fun s a => f a s) s := by
  rw [List.foldl_eq_foldr_reverse, List.foldl_eq_foldr_reverse, ← reduce_reverse]
  exact foldr_reduce f hf w.reverse s

end Evaluation

section MonoidEvaluation

variable {G : Type*} [Monoid G]

/-- The product of the letters in their written order. -/
def evaluate (letters : α → G) (w : List α) : G :=
  w.foldr (fun a g => letters a * g) 1

@[simp] theorem evaluate_nil (letters : α → G) : evaluate letters [] = 1 := rfl
@[simp] theorem evaluate_cons (letters : α → G) (a : α) (w : List α) :
    evaluate letters (a::w) = letters a * evaluate letters w := rfl

@[simp] theorem evaluate_singleton (letters : α → G) (a : α) :
    evaluate letters [a] = letters a := by simp [evaluate]

theorem evaluate_append (letters : α → G) (u v : List α) :
    evaluate letters (u++v) = evaluate letters u * evaluate letters v := by
  induction u with
  | nil => simp
  | cons a u ih => simp only [List.cons_append, evaluate_cons, ih, mul_assoc]

/-- A representation by involutions factors through the stack normal form. -/
theorem evaluate_reduce (letters : α → G) (hletters : ∀ a, letters a * letters a = 1)
    (w : List α) : evaluate letters (reduce w) = evaluate letters w := by
  apply foldr_reduce (fun a g => letters a * g)
  intro a g
  change letters a * (letters a * g) = g
  rw [← mul_assoc, hletters a, one_mul]

/-- Faithfulness on reduced words identifies the identity normal form. -/
theorem evaluate_eq_one_iff_reduce_nil (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1)
    (hfaithful : ∀ w, Reduced w → evaluate letters w = 1 → w = []) (w : List α) :
    evaluate letters w = 1 ↔ reduce w = [] := by
  constructor
  · intro h
    exact hfaithful (reduce w) (reduce_reduced w) (by rw [evaluate_reduce letters hletters]; exact h)
  · intro h
    rw [← evaluate_reduce letters hletters w, h, evaluate_nil]

/-- Connect the combinatorial order-two theorem to any faithful monoid
representation by involutive letters. Faithfulness is an explicit input. -/
theorem orderTwo_conjugate_of_faithful (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1)
    (hfaithful : ∀ w, Reduced w → evaluate letters w = 1 → w = [])
    (w : List α) (hne : evaluate letters w ≠ 1)
    (hsquare : evaluate letters w * evaluate letters w = 1) :
    ∃ (pref : List α) (i : α), reduce w = pref ++ [i] ++ pref.reverse := by
  apply normalized_square_conjugate w
  · intro hnil
    exact hne ((evaluate_eq_one_iff_reduce_nil letters hletters hfaithful w).mpr hnil)
  · apply (evaluate_eq_one_iff_reduce_nil letters hletters hfaithful (w++w)).mp
    rw [evaluate_append]
    exact hsquare

/-- Reverse product, matching the first-letter-first convention for
matrices acting on column vectors. -/
def evaluateReverse (letters : α → G) (w : List α) : G := evaluate letters w.reverse

theorem evaluateReverse_append (letters : α → G) (u v : List α) :
    evaluateReverse letters (u++v) = evaluateReverse letters v * evaluateReverse letters u := by
  simp only [evaluateReverse, List.reverse_append, evaluate_append]

theorem evaluateReverse_reduce (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1) (w : List α) :
    evaluateReverse letters (reduce w) = evaluateReverse letters w := by
  simp only [evaluateReverse, ← reduce_reverse, evaluate_reduce letters hletters]

/-- Identity recognition for the reverse-product matrix convention. -/
theorem evaluateReverse_eq_one_iff_reduce_nil (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1)
    (hfaithful : ∀ w, Reduced w → evaluateReverse letters w = 1 → w = []) (w : List α) :
    evaluateReverse letters w = 1 ↔ reduce w = [] := by
  constructor
  · intro h
    exact hfaithful (reduce w) (reduce_reduced w)
      (by rw [evaluateReverse_reduce letters hletters]; exact h)
  · intro h
    rw [← evaluateReverse_reduce letters hletters w, h]
    rfl

/-- The order-two classification directly in the reverse-product convention. -/
theorem orderTwo_reverse_conjugate_of_faithful (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1)
    (hfaithful : ∀ w, Reduced w → evaluateReverse letters w = 1 → w = [])
    (w : List α) (hne : evaluateReverse letters w ≠ 1)
    (hsquare : evaluateReverse letters w * evaluateReverse letters w = 1) :
    ∃ (pref : List α) (i : α), reduce w = pref ++ [i] ++ pref.reverse := by
  apply normalized_square_conjugate w
  · intro hnil
    exact hne ((evaluateReverse_eq_one_iff_reduce_nil letters hletters hfaithful w).mpr hnil)
  · apply (evaluateReverse_eq_one_iff_reduce_nil letters hletters hfaithful (w++w)).mp
    rw [evaluateReverse_append]
    exact hsquare

end MonoidEvaluation

section GroupEvaluation

variable {G : Type*} [Group G]

/-- Reversal is inversion in every group representation by involutions. -/
theorem evaluate_reverse (letters : α → G) (hletters : ∀ a, letters a * letters a = 1)
    (w : List α) : evaluate letters w.reverse = (evaluate letters w)⁻¹ := by
  have hinv (a : α) : (letters a)⁻¹ = letters a := by
    calc
      (letters a)⁻¹ = (letters a)⁻¹ * 1 := by simp
      _ = (letters a)⁻¹ * (letters a * letters a) := by rw [hletters a]
      _ = letters a := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.reverse_cons, evaluate_append, evaluate_singleton, ih, evaluate_cons,
      mul_inv_rev, hinv a]

/-- The word classification yields an actual conjugacy statement in a
faithful group representation. -/
theorem orderTwo_evaluation_conjugate_of_faithful (letters : α → G)
    (hletters : ∀ a, letters a * letters a = 1)
    (hfaithful : ∀ w, Reduced w → evaluate letters w = 1 → w = [])
    (w : List α) (hne : evaluate letters w ≠ 1)
    (hsquare : evaluate letters w * evaluate letters w = 1) :
    ∃ (pref : List α) (i : α),
      evaluate letters w = evaluate letters pref * letters i * (evaluate letters pref)⁻¹ := by
  rcases orderTwo_conjugate_of_faithful letters hletters hfaithful w hne hsquare with ⟨pref,i,h⟩
  refine ⟨pref,i,?_⟩
  rw [← evaluate_reduce letters hletters w, h, evaluate_append, evaluate_append,
    evaluate_singleton, evaluate_reverse letters hletters]

end GroupEvaluation

abbrev Word := List (Fin 3)
abbrev reducedWord (w : Word) : Prop := Reduced w
abbrev wordReduce (w : Word) : Word := reduce w

end SerreMarkov.UniversalWord
