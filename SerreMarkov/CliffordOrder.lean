import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# The finite integral even order of four Clifford generators

The ambient ring need not be commutative. Four elements square to `-1` and
have integer anticommutators. Their even words lie in the integer span of eight
ordered squarefree monomials, and this span is a finitely generated subring.
-/

namespace SerreMarkov
namespace CliffordOrder

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {R : Type*} [Ring R]

/-- Four generators with integral Clifford relations. -/
structure Generators (R : Type*) [Ring R] where
  a : R
  b : R
  c : R
  d : R
  hab : ℤ
  hac : ℤ
  had : ℤ
  hbc : ℤ
  hbd : ℤ
  hcd : ℤ
  square_a : a * a = -1
  square_b : b * b = -1
  square_c : c * c = -1
  square_d : d * d = -1
  relation_ab : a * b + b * a = hab • (1 : R)
  relation_ac : a * c + c * a = hac • (1 : R)
  relation_ad : a * d + d * a = had • (1 : R)
  relation_bc : b * c + c * b = hbc • (1 : R)
  relation_bd : b * d + d * b = hbd • (1 : R)
  relation_cd : c * d + d * c = hcd • (1 : R)

def generator (r : Generators R) (i : Fin 4) : R :=
  match i.val with
  | 0 => r.a
  | 1 => r.b
  | 2 => r.c
  | _ => r.d

def evenMonomial (r : Generators R) (i : Fin 8) : R :=
  match i.val with
  | 0 => 1
  | 1 => r.a * r.b
  | 2 => r.a * r.c
  | 3 => r.a * r.d
  | 4 => r.b * r.c
  | 5 => r.b * r.d
  | 6 => r.c * r.d
  | _ => r.a * (r.b * (r.c * r.d))

def oddMonomial (r : Generators R) (i : Fin 8) : R :=
  match i.val with
  | 0 => r.a
  | 1 => r.b
  | 2 => r.c
  | 3 => r.d
  | 4 => r.a * (r.b * r.c)
  | 5 => r.a * (r.b * r.d)
  | 6 => r.a * (r.c * r.d)
  | _ => r.b * (r.c * r.d)

def evenSpan (r : Generators R) : Submodule ℤ R :=
  Submodule.span ℤ (Set.range (evenMonomial r))

def oddSpan (r : Generators R) : Submodule ℤ R :=
  Submodule.span ℤ (Set.range (oddMonomial r))

theorem evenMonomial_mem (r : Generators R) (i : Fin 8) :
    evenMonomial r i ∈ evenSpan r := Submodule.subset_span ⟨i, rfl⟩

theorem oddMonomial_mem (r : Generators R) (i : Fin 8) :
    oddMonomial r i ∈ oddSpan r := Submodule.subset_span ⟨i, rfl⟩

private theorem swap_pair (a b : R) (h : ℤ)
    (hh : a * b + b * a = h • (1 : R)) : b * a = h • (1 : R) - a * b := by
  exact eq_sub_of_add_eq' hh

private theorem swap_word (a b : R) (h : ℤ)
    (hh : a * b + b * a = h • (1 : R)) (x : R) :
    b * (a * x) = h • x - a * (b * x) := by
  rw [← mul_assoc, swap_pair a b h hh, sub_mul, smul_mul_assoc,
    one_mul, mul_assoc]

private theorem square_word (a : R) (ha : a * a = -1) (x : R) :
    a * (a * x) = -x := by
  rw [← mul_assoc, ha, neg_one_mul]

private theorem intCast_mul_mem (P : Submodule ℤ R) (k : ℤ) (x : R)
    (hx : x ∈ P) : (k : R) * x ∈ P := by
  simpa only [zsmul_eq_mul] using P.smul_mem k hx

private theorem intCast_mem (P : Submodule ℤ R) (h1 : (1 : R) ∈ P) (k : ℤ) :
    (k : R) ∈ P := by
  simpa only [zsmul_eq_mul, mul_one] using P.smul_mem k h1

/-- Left multiplication by a generator takes each even basis monomial into
the span of the eight odd monomials. -/
theorem generator_evenMonomial_mem (r : Generators R) (i : Fin 4) (j : Fin 8) :
    generator r i * evenMonomial r j ∈ oddSpan r := by
  have h0 := oddMonomial_mem r 0
  have h1 := oddMonomial_mem r 1
  have h2 := oddMonomial_mem r 2
  have h3 := oddMonomial_mem r 3
  have h4 := oddMonomial_mem r 4
  have h5 := oddMonomial_mem r 5
  have h6 := oddMonomial_mem r 6
  have h7 := oddMonomial_mem r 7
  simp only [oddMonomial] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases i <;> fin_cases j <;> dsimp [generator, evenMonomial]
  all_goals
    try simp only [mul_assoc, swap_word _ _ _ r.relation_ab,
      swap_word _ _ _ r.relation_ac, swap_word _ _ _ r.relation_ad,
      swap_word _ _ _ r.relation_bc, swap_word _ _ _ r.relation_bd,
      swap_word _ _ _ r.relation_cd, swap_pair _ _ _ r.relation_ab,
      swap_pair _ _ _ r.relation_ac, swap_pair _ _ _ r.relation_ad,
      swap_pair _ _ _ r.relation_bc, swap_pair _ _ _ r.relation_bd,
      swap_pair _ _ _ r.relation_cd, square_word _ r.square_a,
      square_word _ r.square_b, square_word _ r.square_c,
      square_word _ r.square_d, r.square_a, r.square_b, r.square_c,
      r.square_d, mul_add, mul_sub, mul_neg, neg_mul, mul_smul_comm,
      smul_mul_assoc, smul_smul, one_mul, mul_one, neg_one_mul, mul_neg_one]
    aesop (add safe apply [Submodule.add_mem, Submodule.sub_mem,
      Submodule.neg_mem, Submodule.smul_mem, Submodule.zero_mem,
      intCast_mul_mem, intCast_mem])

/-- The converse parity change on the eight odd monomials. -/
theorem generator_oddMonomial_mem (r : Generators R) (i : Fin 4) (j : Fin 8) :
    generator r i * oddMonomial r j ∈ evenSpan r := by
  have h0 := evenMonomial_mem r 0
  have h1 := evenMonomial_mem r 1
  have h2 := evenMonomial_mem r 2
  have h3 := evenMonomial_mem r 3
  have h4 := evenMonomial_mem r 4
  have h5 := evenMonomial_mem r 5
  have h6 := evenMonomial_mem r 6
  have h7 := evenMonomial_mem r 7
  simp only [evenMonomial] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases i <;> fin_cases j <;> dsimp [generator, oddMonomial]
  all_goals
    try simp only [mul_assoc, swap_word _ _ _ r.relation_ab,
      swap_word _ _ _ r.relation_ac, swap_word _ _ _ r.relation_ad,
      swap_word _ _ _ r.relation_bc, swap_word _ _ _ r.relation_bd,
      swap_word _ _ _ r.relation_cd, swap_pair _ _ _ r.relation_ab,
      swap_pair _ _ _ r.relation_ac, swap_pair _ _ _ r.relation_ad,
      swap_pair _ _ _ r.relation_bc, swap_pair _ _ _ r.relation_bd,
      swap_pair _ _ _ r.relation_cd, square_word _ r.square_a,
      square_word _ r.square_b, square_word _ r.square_c,
      square_word _ r.square_d, r.square_a, r.square_b, r.square_c,
      r.square_d, mul_add, mul_sub, mul_neg, neg_mul, mul_smul_comm,
      smul_mul_assoc, smul_smul, one_mul, mul_one, neg_one_mul, mul_neg_one]
    aesop (add safe apply [Submodule.add_mem, Submodule.sub_mem,
      Submodule.neg_mem, Submodule.smul_mem, Submodule.zero_mem,
      intCast_mul_mem, intCast_mem])

theorem generator_mul_evenSpan (r : Generators R) (i : Fin 4) (x : R)
    (hx : x ∈ evenSpan r) : generator r i * x ∈ oddSpan r := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact generator_evenMonomial_mem r i j
  | zero => rw [mul_zero]; exact (oddSpan r).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [mul_add] using (oddSpan r).add_mem ihx ihy
  | smul k x hx ih =>
      simpa only [mul_smul_comm] using (oddSpan r).smul_mem k ih

theorem generator_mul_oddSpan (r : Generators R) (i : Fin 4) (x : R)
    (hx : x ∈ oddSpan r) : generator r i * x ∈ evenSpan r := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact generator_oddMonomial_mem r i j
  | zero => rw [mul_zero]; exact (evenSpan r).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [mul_add] using (evenSpan r).add_mem ihx ihy
  | smul k x hx ih =>
      simpa only [mul_smul_comm] using (evenSpan r).smul_mem k ih

theorem evenMonomial_mul_evenSpan (r : Generators R) (j : Fin 8) (x : R)
    (hx : x ∈ evenSpan r) : evenMonomial r j * x ∈ evenSpan r := by
  have hp (i k : Fin 4) : generator r i * (generator r k * x) ∈ evenSpan r :=
    generator_mul_oddSpan r i _ (generator_mul_evenSpan r k x hx)
  have hfour : generator r 0 * (generator r 1 * (generator r 2 * (generator r 3 * x))) ∈
      evenSpan r :=
    generator_mul_oddSpan r 0 _ (generator_mul_evenSpan r 1 _
      (generator_mul_oddSpan r 2 _ (generator_mul_evenSpan r 3 x hx)))
  fin_cases j
  · simpa only [evenMonomial, one_mul] using hx
  · simpa only [evenMonomial, generator, mul_assoc] using hp 0 1
  · simpa only [evenMonomial, generator, mul_assoc] using hp 0 2
  · simpa only [evenMonomial, generator, mul_assoc] using hp 0 3
  · simpa only [evenMonomial, generator, mul_assoc] using hp 1 2
  · simpa only [evenMonomial, generator, mul_assoc] using hp 1 3
  · simpa only [evenMonomial, generator, mul_assoc] using hp 2 3
  · simpa only [evenMonomial, generator, mul_assoc] using hfour

/-- The finite integer span is closed under ring multiplication. -/
theorem evenSpan_mul_mem (r : Generators R) (x y : R)
    (hx : x ∈ evenSpan r) (hy : y ∈ evenSpan r) : x * y ∈ evenSpan r := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact evenMonomial_mul_evenSpan r j y hy
  | zero => rw [zero_mul]; exact (evenSpan r).zero_mem
  | add x z hx hz ihx ihz => simpa only [add_mul] using (evenSpan r).add_mem ihx ihz
  | smul k x hx ih => simpa only [smul_mul_assoc] using (evenSpan r).smul_mem k ih

def evenSubring (r : Generators R) : Subring R where
  carrier := evenSpan r
  one_mem' := evenMonomial_mem r 0
  zero_mem' := (evenSpan r).zero_mem
  add_mem' := (evenSpan r).add_mem
  neg_mem' := (evenSpan r).neg_mem
  mul_mem' := evenSpan_mul_mem r _ _

theorem evenSpan_finitely_generated (r : Generators R) : (evenSpan r).FG :=
  Submodule.fg_span (Set.finite_range (evenMonomial r))

/-- The same integral order, presented as a subalgebra over the integers. -/
def evenSubalgebra (r : Generators R) : Subalgebra ℤ R where
  toSubsemiring := (evenSubring r).toSubsemiring
  algebraMap_mem' k := by
    change (k : R) ∈ evenSpan r
    exact intCast_mem (evenSpan r) (evenMonomial_mem r 0) k

instance evenSubalgebra_finite (r : Generators R) : Module.Finite ℤ (evenSubalgebra r) := by
  change Module.Finite ℤ (evenSpan r)
  exact Module.Finite.iff_fg.mpr (evenSpan_finitely_generated r)

def wordProduct (r : Generators R) : List (Fin 4) → R
  | [] => 1
  | i :: w => generator r i * wordProduct r w

/-- Every even word belongs to the eight-monomial integral order. -/
theorem wordProduct_mem_parity (r : Generators R) (w : List (Fin 4)) :
    (Even w.length → wordProduct r w ∈ evenSpan r) ∧
    (Odd w.length → wordProduct r w ∈ oddSpan r) := by
  induction w with
  | nil =>
      constructor
      · intro _; exact evenMonomial_mem r 0
      · intro h; simp at h
  | cons i w ih =>
      constructor
      · intro h
        apply generator_mul_oddSpan r i
        apply ih.2
        simpa only [List.length_cons, Nat.even_add_one, Nat.not_even_iff_odd] using h
      · intro h
        apply generator_mul_evenSpan r i
        apply ih.1
        simpa only [List.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even] using h

theorem even_word_mem (r : Generators R) (w : List (Fin 4)) (hw : Even w.length) :
    wordProduct r w ∈ evenSpan r := (wordProduct_mem_parity r w).1 hw

/-- The even-word normal form uses eight integer coefficients. -/
theorem even_word_eq_sum (r : Generators R) (w : List (Fin 4)) (hw : Even w.length) :
    ∃ coefficients : Fin 8 → ℤ,
      ∑ j, coefficients j • evenMonomial r j = wordProduct r w :=
  (Submodule.mem_span_range_iff_exists_fun ℤ).mp (even_word_mem r w hw)

end CliffordOrder
end SerreMarkov
