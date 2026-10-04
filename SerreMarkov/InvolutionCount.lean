import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Counting representatives of a finite involution

For a finite invariant set in a linear order, choose the lower member of each
two-element orbit and keep every fixed point. Twice the representative count
is the set's cardinality plus its fixed-point count.
-/

namespace SerreMarkov.InvolutionCount

variable {X : Type*} [LinearOrder X]

def representatives (S : Finset X) (f : X → X) : Finset X :=
  S.filter (fun x => x ≤ f x)

def fixedPoints (S : Finset X) (f : X → X) : Finset X :=
  S.filter (fun x => f x = x)

/-- The exact orbit count, without a freeness assumption. -/
theorem twice_representative_card (S : Finset X) (f : X → X)
    (hf : Function.Involutive f) (hS : ∀ x ∈ S, f x ∈ S) :
    2*(representatives S f).card = S.card+(fixedPoints S f).card := by
  let L := S.filter (fun x => x < f x)
  let U := S.filter (fun x => f x < x)
  have hLU : L.card = U.card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS,hxlt⟩
      apply Finset.mem_filter.mpr
      exact ⟨hS x hxS, by simpa only [hf x] using hxlt⟩
    · intro x hx y hy hxy
      exact hf.injective hxy
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyS,hylt⟩
      refine ⟨f y, Finset.mem_filter.mpr ⟨hS y hyS, ?_⟩, hf y⟩
      simpa only [hf y] using hylt
  have hrep : representatives S f = L ∪ fixedPoints S f := by
    ext x
    simp only [representatives,L,fixedPoints,Finset.mem_filter,Finset.mem_union,
      le_iff_lt_or_eq]
    constructor
    · rintro ⟨hx, hlt | heq⟩
      · exact Or.inl ⟨hx,hlt⟩
      · exact Or.inr ⟨hx,heq.symm⟩
    · rintro (⟨hx,hlt⟩ | ⟨hx,heq⟩)
      · exact ⟨hx,Or.inl hlt⟩
      · exact ⟨hx,Or.inr heq.symm⟩
  have hd : Disjoint L (fixedPoints S f) := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxF
    have hlt := (Finset.mem_filter.mp hxL).2
    have heq := (Finset.mem_filter.mp hxF).2
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  have hcount : (representatives S f).card = L.card+(fixedPoints S f).card := by
    rw [hrep,Finset.card_union_of_disjoint hd]
  have hpartition : (representatives S f).card+U.card = S.card := by
    simpa only [representatives,U,not_le] using
      Finset.filter_card_add_filter_neg_card_eq_card (s := S) (fun x => x ≤ f x)
  omega

theorem twice_representative_card_of_no_fixed (S : Finset X) (f : X → X)
    (hf : Function.Involutive f) (hS : ∀ x ∈ S, f x ∈ S)
    (hfree : ∀ x ∈ S, f x ≠ x) :
    2*(representatives S f).card = S.card := by
  have hfixed : fixedPoints S f = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hfree x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  simpa [hfixed] using twice_representative_card S f hf hS

/-- The actual orbit relation of an involution. -/
def orbitSetoid (f : X → X) (hf : Function.Involutive f) : Setoid X where
  r x y := y=x ∨ y=f x
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => by
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h,hf]),
    fun hxy hyz => by
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hyz.trans hxy)
      · exact Or.inr (hyz.trans (congrArg f hxy))
      · exact Or.inr (hyz.trans hxy)
      · exact Or.inl (hyz.trans ((congrArg f hxy).trans (hf _)))⟩

def canonicalRepresentative (f : X → X) (x : X) : X := min x (f x)

private theorem canonical_mem (f : X → X) (hf : Function.Involutive f) (x : X) :
    canonicalRepresentative f x ≤ f (canonicalRepresentative f x) := by
  by_cases h : x ≤ f x
  · simpa only [canonicalRepresentative,min_eq_left h] using h
  · have h' : f x ≤ x := le_of_not_ge h
    simpa only [canonicalRepresentative,min_eq_right h',hf x] using h'

private theorem canonical_invariant (f : X → X) (hf : Function.Involutive f) (x : X) :
    canonicalRepresentative f (f x) = canonicalRepresentative f x := by
  simp only [canonicalRepresentative,hf x,min_comm]

/-- Every involution orbit has exactly one canonical lower representative. -/
def quotientEquivRepresentatives (f : X → X) (hf : Function.Involutive f) :
    Quotient (orbitSetoid f hf) ≃ {x : X // x ≤ f x} where
  toFun := Quotient.lift (fun x => ⟨canonicalRepresentative f x,canonical_mem f hf x⟩)
    (fun x y h => by
      apply Subtype.ext
      change canonicalRepresentative f x = canonicalRepresentative f y
      rcases h with h | h
      · rw [h]
      · rw [h,canonical_invariant f hf])
  invFun x := Quotient.mk (orbitSetoid f hf) x.val
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      change x = canonicalRepresentative f x ∨ x = f (canonicalRepresentative f x)
      by_cases h : x ≤ f x
      · exact Or.inl (by simp only [canonicalRepresentative,min_eq_left h])
      · exact Or.inr (by simp only [canonicalRepresentative,min_eq_right (le_of_not_ge h),hf x])
  right_inv x := by
    apply Subtype.ext
    exact min_eq_left x.property

theorem quotient_card_representatives [Fintype X] (f : X → X) (hf : Function.Involutive f) :
    Nat.card (Quotient (orbitSetoid f hf)) = (representatives Finset.univ f).card := by
  calc
    _ = Nat.card {x : X // x ≤ f x} := Nat.card_congr (quotientEquivRepresentatives f hf)
    _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_subtype,representatives]

/-- Exact cardinality of the actual quotient by an involution. -/
theorem twice_quotient_card [Fintype X] (f : X → X) (hf : Function.Involutive f) :
    2*Nat.card (Quotient (orbitSetoid f hf)) =
      Fintype.card X+(fixedPoints Finset.univ f).card := by
  rw [quotient_card_representatives]
  simpa only [Finset.card_univ] using
    twice_representative_card Finset.univ f hf (fun x hx => Finset.mem_univ _)

end SerreMarkov.InvolutionCount
